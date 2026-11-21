#!/usr/bin/env python3
"""
Barchart-driven CSP tracker (no IBKR involved at all).

Barchart is used ONLY as a screener - to rank and discover which
symbol/strike/expiration combos are worth looking at (by annualized
potential return). ALL actual pricing - stock price, bid, ask - comes from
yfinance instead, since Barchart's own bid/price snapshot runs slightly
stale relative to Yahoo. Barchart's bid is kept only as a reference column
for comparison, never used in any P&L math.

Each run:
  1. Scrapes Barchart's free naked-puts screener (top ~20 rows, already
     sorted by ANNUALIZED potential return desc via the URL's own orderBy
     param).
  2. Walks that ranked list and adds EVERY candidate whose symbol isn't
     already an open (unexpired) tracked position - no daily cap. If two
     rows in the same run share a symbol, only the top-ranked one is added
     (still at most one open position per symbol at a time). Paring the
     resulting list down to a smaller "actually trading" subset is a manual
     decision made later, not something this script does.
  3. Prices each new candidate via yfinance (matching symbol/strike/
     expiration in the live option chain) - stock price, bid, AND ask all
     come from yfinance. If yfinance has no usable bid/ask for that
     contract, falls back to Barchart's bid (flagged) and approximates
     ask = bid * 1.2 (also flagged).
  4. Adds them to a small local JSON position store, then rebuilds a summary
     CSV covering EVERY open (unexpired) tracked position - not just the new
     ones - with entry vs. current stock price, and TWO unrealized P&L
     readings for both the CSP-seller and long-put-buyer side:
       - "fictional": off intrinsic value at the CURRENT stock price only -
         i.e. what settlement P&L would be if the option expired right now.
         Ignores time value entirely, so it's not a real closing price.
       - "actual": what you'd really get closing the position today, crossing
         the spread against yourself the way a real exit would - selling a
         long put at the current BID, buying back a short put at the current
         ASK. Requires a fresh live option-chain requote per position (not
         just the stock price), rate-limited to avoid hammering yfinance.
     Realized (settled) P&L doesn't need this distinction - by expiration,
     time value has decayed to zero, so there's only one real number.

Usage:
  python barchart_csp_tracker.py
"""

import subprocess
import sys
import time
import json
import math
import os
import urllib.request
from datetime import datetime, date, timedelta
from zoneinfo import ZoneInfo
from pathlib import Path

yf = None
pd = None
plt = None

BARCHART_URL = "https://www.barchart.com/options/income-strategies/naked-puts?orderBy=potentialReturnAnnual&orderDir=desc"
POSITIONS_FILE = Path("barchart_csp_positions.json")
SUMMARY_CSV = Path("barchart_csp_summary.csv")
REALIZED_PNL_PNG = Path("barchart_csp_realized_pnl.png")
SUMMARY_HTML = Path("index.html")  # repo-root name - GitHub Pages serves this at the clean root URL
SUMMARY_HTML_URL = "https://mkcan1973.github.io/barchart-csp-tracker/"

# One entry per actual script execution that got past the market-open
# check (so weekends/holidays correctly show zero entries, not "missing"
# ones) - exists so the webpage can show whether GitHub Actions' own
# scheduler is actually firing all 4 daily triggers, independent of
# whether any run found a new candidate worth a run_label. Capped to the
# most recent entries so the file doesn't grow unbounded.
RUN_LOG_FILE = Path("run_log.json")
RUN_LOG_MAX_ENTRIES = 200


def load_run_log():
    if not RUN_LOG_FILE.exists():
        return []
    try:
        return json.loads(RUN_LOG_FILE.read_text())
    except Exception:
        return []


def save_run_log(log):
    RUN_LOG_FILE.write_text(json.dumps(log[-RUN_LOG_MAX_ENTRIES:], indent=2))

# Single source of truth for "what counts as a good opportunity" - edit
# this file (not the script) to change which new candidates trigger a
# Discord ping AND what the webpage's filter boxes show on EVERY load
# (no localStorage override - the page always starts from this file).
# Same fields/semantics as the webpage's own filter boxes; null/missing
# means no bound on that dimension. Every new candidate is still tracked
# and shown on the dashboard regardless - this only gates the notification.
FILTER_CONFIG_FILE = Path("discord_filter_config.json")
DEFAULT_FILTER_CONFIG = {
    "min_roi": 150, "max_roi": None,
    "min_pe": None, "max_pe": None,
    "min_dte_entry": None, "max_dte_entry": None,
    "base_investment": None,
    "min_put_strike": None, "max_put_strike": None,
    # "monthly" (Barchart only), "weekly" (Yahoo-sourced non-monthly only),
    # or "both" - gates Discord the same as every other field here AND sets
    # the webpage's 3-way expiration toggle on every load.
    "expiry_filter": "monthly",
}


def load_filter_config():
    if FILTER_CONFIG_FILE.exists():
        try:
            cfg = json.loads(FILTER_CONFIG_FILE.read_text())
            return {**DEFAULT_FILTER_CONFIG, **cfg}
        except Exception as e:
            print(f"  WARNING: couldn't parse {FILTER_CONFIG_FILE} ({e}) - using defaults.")
    return dict(DEFAULT_FILTER_CONFIG)


def position_passes_filter_config(p, cfg):
    """Same filter logic as the webpage's client-side JS (ROI/PE/DTE@entry/
    base investment/put strike/expiry type) - works on either a freshly-
    built candidate position or an already-stored one, since both carry the
    same field names."""
    ann_return = p.get("potential_return_annual_pct") or 0
    if cfg.get("min_roi") is not None and ann_return < cfg["min_roi"]:
        return False
    if cfg.get("max_roi") is not None and ann_return > cfg["max_roi"]:
        return False

    # Missing PE ("--" on the webpage) means unprofitable/undefined, not
    # zero - treat as infinite so it fails a Max PE cap but still passes a
    # Min-PE-only filter, same convention as the webpage's own fix.
    pe = p.get("pe_at_entry")
    pe_for_check = pe if pe is not None else float("inf")
    if cfg.get("min_pe") is not None and pe_for_check < cfg["min_pe"]:
        return False
    if cfg.get("max_pe") is not None and pe_for_check > cfg["max_pe"]:
        return False

    if cfg.get("min_dte_entry") is not None or cfg.get("max_dte_entry") is not None:
        added = datetime.strptime(p["added_date"], "%Y-%m-%d").date()
        exp = datetime.strptime(p["expiration"], "%Y-%m-%d").date()
        dte_entry = (exp - added).days
        if cfg.get("min_dte_entry") is not None and dte_entry < cfg["min_dte_entry"]:
            return False
        if cfg.get("max_dte_entry") is not None and dte_entry > cfg["max_dte_entry"]:
            return False

    if cfg.get("base_investment") is not None:
        ask = p.get("ask")
        if ask is None or ask * 100 > cfg["base_investment"]:
            return False

    strike = p.get("strike")
    if cfg.get("min_put_strike") is not None and (strike is None or strike < cfg["min_put_strike"]):
        return False
    if cfg.get("max_put_strike") is not None and (strike is None or strike > cfg["max_put_strike"]):
        return False

    expiry_filter = cfg.get("expiry_filter") or "both"
    if expiry_filter != "both" and p.get("expiry_type", "monthly") != expiry_filter:
        return False

    return True

# If yfinance has no usable bid/ask for the exact contract Barchart
# surfaced, fall back to Barchart's own bid (flagged) and approximate
# ask = bid * this multiplier (also flagged) - better than skipping the
# candidate entirely just because one side's free data feed is thin.
YAHOO_APPROX_ASK_MULTIPLIER = 1.2

# PnL per position is scaled to what it would have been at this fixed
# capital-at-risk size, so positions on wildly different-priced stocks are
# comparable. Risk basis: CSP seller = cash-secured collateral (strike x
# 100); long put buyer = premium paid, their actual max loss (ask x 100).
NORMALIZED_RISK_USD = 1000.0

# "Actual" unrealized P&L requotes the live option chain for every open
# position, every run - with the tracked list only growing (no cap), that's
# real traffic against yfinance's free, rate-limit-sensitive feed. A fixed
# minimum gap between requests keeps runs well-behaved instead of firing
# everything back to back.
YF_MIN_REQUEST_INTERVAL_SECONDS = 0.3


class _RateLimiter:
    def __init__(self, min_interval_seconds):
        self.min_interval = min_interval_seconds
        self.last_call = 0.0

    def wait(self):
        now = time.time()
        remaining = self.min_interval - (now - self.last_call)
        if remaining > 0:
            time.sleep(remaining)
        self.last_call = time.time()


_yf_rate_limiter = _RateLimiter(YF_MIN_REQUEST_INTERVAL_SECONDS)

# --- Discord notifications -------------------------------------------------------
# Same webhook pattern as the tictactoe project's notify.py - URL comes from an
# env var only (never a committed file), since this repo is public. GitHub
# Actions supplies it from an encrypted repo secret; set it locally too if you
# ever want notifications from a manual run.

def notify_discord(message):
    """Best-effort Discord webhook ping - never raises, silently no-ops if
    DISCORD_WEBHOOK_URL isn't set."""
    url = os.environ.get("DISCORD_WEBHOOK_URL")
    if not url:
        return
    try:
        data = json.dumps({"content": message}).encode("utf-8")
        # Cloudflare 403s urllib's default User-Agent; use a browser one.
        req = urllib.request.Request(url, data=data, headers={
            "Content-Type": "application/json",
            "User-Agent": ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                           "(KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"),
        })
        urllib.request.urlopen(req, timeout=5)
    except Exception as e:
        print(f"  [notification] Discord webhook failed (run continues normally): "
              f"{type(e).__name__}: {e}")


def _install(pkg):
    print(f"  Installing {pkg}...")
    subprocess.check_call([sys.executable, "-m", "pip", "install", "--quiet", pkg])


def ensure_deps():
    global yf, pd
    try:
        import playwright  # noqa: F401
    except ImportError:
        _install("playwright")
        subprocess.check_call([sys.executable, "-m", "playwright", "install", "chromium"])
    if yf is None:
        try:
            import yfinance as _yf
        except ImportError:
            _install("yfinance")
            import yfinance as _yf
        yf = _yf
    if pd is None:
        try:
            import pandas as _pd
        except ImportError:
            _install("pandas")
            import pandas as _pd
        pd = _pd


def is_us_market_open_today(today):
    """False on weekends and US market holidays - lets a scheduler (cron,
    GitHub Actions, Task Scheduler) fire every day without this script
    wasting a run (and a Barchart scrape) on days nothing is trading."""
    try:
        import pandas_market_calendars as mcal
    except ImportError:
        _install("pandas_market_calendars")
        import pandas_market_calendars as mcal
    nyse = mcal.get_calendar("NYSE")
    schedule = nyse.schedule(start_date=today.isoformat(), end_date=today.isoformat())
    return not schedule.empty

# --- Barchart scrape -------------------------------------------------------------

def scrape_barchart_top20():
    """Get symbol/expiration/strike/bid/potential-return from Barchart's free
    naked-puts screener - NOT by reading the rendered page text (its grid
    renders values somewhere DOM-text-extraction can't reach: confirmed via a
    live check where a screenshot showed real numbers while every DOM/
    accessibility text-read, including Playwright's own shadow-DOM-piercing
    .inner_text(), came back empty at the same instant - almost certainly a
    closed Shadow Root). Instead, intercept the JSON API call the page itself
    makes to populate that grid (proxies/core-api/v1/options/naked-puts),
    which returns clean, already-numeric fields under each row's "raw" key.
    Already sorted by potential return desc (via the URL's own orderBy), and
    Barchart's free tier already caps this at ~20 rows without a login."""
    from playwright.sync_api import sync_playwright

    rows_out = []
    captured = {}

    def on_response(resp):
        if "/proxies/core-api/v1/options/naked-puts" in resp.url and "body" not in captured:
            try:
                captured["body"] = resp.json()
            except Exception:
                pass

    with sync_playwright() as pw:
        browser = pw.chromium.launch(headless=True)
        ctx = browser.new_context(
            user_agent="Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                       "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"
        )
        page = ctx.new_page()
        page.on("response", on_response)
        print(f"  Opening {BARCHART_URL}")
        page.goto(BARCHART_URL, wait_until="domcontentloaded", timeout=30000)

        for sel in ["button:has-text('Accept')", "button:has-text('I Agree')", "[aria-label='Close']"]:
            try:
                page.click(sel, timeout=2000)
            except Exception:
                pass

        deadline = time.time() + 20
        while "body" not in captured and time.time() < deadline:
            page.wait_for_timeout(250)
        browser.close()

    if "body" not in captured:
        print("  Never captured the naked-puts API response - Barchart may have changed its endpoint.")
        return rows_out

    data = captured["body"].get("data", [])
    for row in data[:20]:
        raw = row.get("raw", {})
        symbol = raw.get("baseSymbol")
        expiration = raw.get("expirationDate")  # already YYYY-MM-DD
        strike = raw.get("strike")
        bid = raw.get("bidPrice")
        if not symbol or not expiration or strike is None or bid is None:
            continue
        rows_out.append({
            "symbol": symbol,
            "expiration": expiration,
            "strike": float(strike),
            "barchart_bid": float(bid),  # reference only - never used in P&L math
            "stock_px": raw.get("underlyingLastPrice"),  # reference only - entry price comes from yfinance
            "potential_return_pct": raw.get("potentialReturn"),
            "potential_return_annual_pct": raw.get("potentialReturnAnnual"),
            "expiry_type": "monthly",
        })

    return rows_out

# Barchart's free naked-puts screener only ever surfaces one (monthly-
# cadence) expiration per symbol - weeklies are paywalled there. Bounds how
# many of a symbol's earlier expirations get a full option-chain fetch, so
# a liquid name with many weeklies can't blow up one run's yfinance traffic.
MAX_WEEKLY_EXPIRATIONS_PER_SYMBOL = 4


def scrape_yahoo_weeklies(barchart_rows, today):
    """For the SAME symbols Barchart's screener already surfaced, indepen-
    dently scan yfinance's full option chain for any expiration EARLIER
    than Barchart's own monthly pick - genuinely more frequent opportun-
    ities than Barchart's free tier otherwise exposes for that symbol.
    There's no Barchart ranking available for these, so each OTM put across
    every such expiration is self-scored the same way Barchart's own
    screener works (bid / strike, annualized by days-to-expiration), and
    only the single BEST (strike, expiration) per symbol is kept - one shot
    per symbol per run, same cadence pick_new_candidates already expects
    from a Barchart scan, not a flood of every weekly/strike combination."""
    rows_out = []
    for row in barchart_rows:
        symbol = row["symbol"]
        monthly_exp = datetime.strptime(row["expiration"], "%Y-%m-%d").date()

        _yf_rate_limiter.wait()
        try:
            t = yf.Ticker(symbol)
            all_expirations = t.options
        except Exception:
            continue

        earlier_exps = sorted(
            e for e in all_expirations
            if today < datetime.strptime(e, "%Y-%m-%d").date() < monthly_exp
        )[:MAX_WEEKLY_EXPIRATIONS_PER_SYMBOL]
        if not earlier_exps:
            continue

        stock_px = get_current_stock_price(symbol)
        if stock_px is None:
            continue

        best = None
        for exp in earlier_exps:
            _yf_rate_limiter.wait()
            try:
                puts = t.option_chain(exp).puts
            except Exception:
                continue
            dte = (datetime.strptime(exp, "%Y-%m-%d").date() - today).days
            if dte <= 0:
                continue
            for _, r in puts.iterrows():
                strike, bid = r.get("strike"), r.get("bid")
                if strike is None or bid is None or pd.isna(strike) or pd.isna(bid) or bid <= 0:
                    continue
                strike, bid = float(strike), float(bid)
                if strike >= stock_px:  # CSP candidates are OTM puts only
                    continue
                ann_roi_pct = (bid / strike * 100) * (365.0 / dte)
                if best is None or ann_roi_pct > best["potential_return_annual_pct"]:
                    best = {
                        "symbol": symbol,
                        "expiration": exp,
                        "strike": strike,
                        "barchart_bid": bid,  # sourced from yfinance here, not Barchart - see expiry_type
                        "stock_px": stock_px,
                        "potential_return_pct": round(bid / strike * 100, 4),
                        "potential_return_annual_pct": round(ann_roi_pct, 4),
                        "expiry_type": "weekly",
                    }
        if best is not None:
            rows_out.append(best)
    return rows_out

# --- Bear call spread scanner -------------------------------------------------
# A separate, complementary bearish strategy that reuses the SAME symbols the
# naked-puts screen above already surfaced, rather than its own screen. Simple
# candidates-only - no cross-run position tracking, no Discord notifications,
# just a fresh snapshot of today's spreads on every run. All three thresholds
# below are filtered LIVE in the browser (same pattern as the CSP filter bar),
# not baked into the scan - these are just the values the page's inputs start
# from on load, editable via "Edit thresholds on GitHub" without a code change.

BEAR_CALL_CONFIG_FILE = Path("bear_call_spread_config.json")
DEFAULT_BEAR_CALL_CONFIG = {
    # Net credit as a percentage of the strike width - e.g. 30 means the
    # upfront credit must be at least 30% of the width (so at most 70% of
    # the width is at risk as the max loss).
    "min_credit_pct": 30.0,
    # Collateral per spread (width x 100) above which a candidate is
    # skipped - same idea as the CSP side's base_investment cap. None means
    # no cap.
    "max_collateral": None,
    # Trailing P/E floor on the underlying - None means no PE filtering.
    # Missing/undefined PE is treated as infinite, same convention as the
    # CSP side's own min-PE filter (passes a min-only filter, fails a cap).
    "min_pe": None,
    # Delta the short call strike is chosen to target (see
    # _bs_call_delta/pick_short_call_strike below) - 0.30 is a common
    # credit-spread convention (~70% rough probability of expiring OTM).
    # This picks WHICH strike pair gets used at all, so unlike the three
    # filters above it isn't something the page's filter bar can change
    # after the fact - it has to be applied at scan time.
    "target_short_delta": 0.30,
    # Assumed fill quality, 0-100, for both entry pricing and the "actual"
    # unrealized P&L (see credit_leg_fill_price/debit_leg_fill_price) - 0 is
    # pessimistic (crossing the full bid-ask spread both ways, the original
    # behavior), 100 is optimistic (the opposite extreme), 50 is the mid for
    # both legs. Defaults to 0 (unchanged, conservative behavior) since this
    # directly drives what gets locked in as a new position's entry credit -
    # dial it up once you have a sense of your own realistic fill quality.
    # The page also has a live slider over this same range for exploring
    # "what if" on already-open positions without waiting for a new run.
    "fill_pct": 0,
}

# Flat assumption for Black-Scholes delta - near-term option delta is not
# very sensitive to the risk-free rate, so a fixed, roughly-current rate is
# fine here rather than fetching a live treasury yield.
_BS_RISK_FREE_RATE = 0.045


def _norm_cdf(x):
    return 0.5 * (1.0 + math.erf(x / math.sqrt(2.0)))


def _bs_call_delta(stock_px, strike, dte_days, iv):
    """Black-Scholes call delta (N(d1)) - used to pick the short strike by
    probability-of-finishing-ITM instead of raw dollar distance from price,
    since "the next strike up" lands very differently depending on a
    stock's own strike spacing and volatility. None if the inputs aren't
    usable (missing/zero IV, non-positive DTE, bad prices)."""
    if iv is None or iv <= 0 or dte_days <= 0 or stock_px <= 0 or strike <= 0:
        return None
    t = dte_days / 365.0
    try:
        d1 = (math.log(stock_px / strike) + (_BS_RISK_FREE_RATE + 0.5 * iv * iv) * t) / (iv * math.sqrt(t))
    except (ValueError, ZeroDivisionError):
        return None
    return _norm_cdf(d1)


def pick_short_call_strike(calls, stock_px, dte_days, target_delta):
    """Among the OTM call strikes, pick whichever one's Black-Scholes delta
    is closest to target_delta, rather than always taking the literal
    nearest-OTM strike - lets strike selection adapt to each stock's own
    volatility instead of being thrown off by wide/narrow strike spacing.
    Falls back to the plain nearest-OTM strike if usable IV data isn't
    available for any OTM strike (thin/illiquid chains). Returns None if
    there's no OTM strike at all."""
    otm = calls[calls["strike"] > stock_px].sort_values("strike")
    if otm.empty:
        return None

    best_strike, best_diff = None, None
    for _, r in otm.iterrows():
        iv = r.get("impliedVolatility")
        iv = float(iv) if iv is not None and not pd.isna(iv) else None
        delta = _bs_call_delta(stock_px, float(r["strike"]), dte_days, iv)
        if delta is None:
            continue
        diff = abs(delta - target_delta)
        if best_diff is None or diff < best_diff:
            best_strike, best_diff = float(r["strike"]), diff

    if best_strike is not None:
        return best_strike
    return float(otm.iloc[0]["strike"])  # fallback: plain nearest-OTM


def load_bear_call_config():
    if BEAR_CALL_CONFIG_FILE.exists():
        try:
            cfg = json.loads(BEAR_CALL_CONFIG_FILE.read_text())
            return {**DEFAULT_BEAR_CALL_CONFIG, **cfg}
        except Exception:
            pass
    return dict(DEFAULT_BEAR_CALL_CONFIG)


def scan_bear_call_spreads(all_rows, today, cfg):
    """For each distinct (symbol, expiration) the naked-puts screen (plus its
    weekly extension) surfaced: pick a short call strike targeting
    cfg['target_short_delta'] (see pick_short_call_strike), buy the very
    next strike above that as the long leg - keeping them adjacent, just
    choosing WHICH adjacent pair by probability instead of raw distance -
    a defined-risk bear call credit spread. Every structurally valid spread
    (positive width, positive net credit) is returned - the credit%/
    collateral/PE thresholds are filtered live in the browser, not here,
    same as the CSP side's own filter bar (target_short_delta is the one
    exception - it decides which strikes get used at all, so it has to be
    applied here at scan time). Sorted richest-credit-first (the default
    sort before any filter is applied)."""
    seen = set()
    pe_cache = {}
    out = []
    target_delta = cfg.get("target_short_delta") or DEFAULT_BEAR_CALL_CONFIG["target_short_delta"]
    fill_pct = cfg.get("fill_pct")
    if fill_pct is None:
        fill_pct = DEFAULT_BEAR_CALL_CONFIG["fill_pct"]
    for row in all_rows:
        symbol, expiration = row["symbol"], row["expiration"]
        key = (symbol, expiration)
        if key in seen:
            continue
        seen.add(key)

        stock_px = get_current_stock_price(symbol)
        if stock_px is None:
            continue

        _yf_rate_limiter.wait()
        try:
            t = yf.Ticker(symbol)
            if expiration not in t.options:
                continue
            calls = t.option_chain(expiration).calls
        except Exception:
            continue

        dte = (datetime.strptime(expiration, "%Y-%m-%d").date() - today).days
        short_strike = pick_short_call_strike(calls, stock_px, dte, target_delta)
        if short_strike is None:
            continue
        strikes_above_short = sorted(set(
            float(s) for s in calls["strike"].tolist()
            if s is not None and not pd.isna(s) and s > short_strike
        ))
        if not strikes_above_short:
            continue
        long_strike = strikes_above_short[0]

        short_row = calls[abs(calls["strike"] - short_strike) < 0.01]
        long_row = calls[abs(calls["strike"] - long_strike) < 0.01]
        if short_row.empty or long_row.empty:
            continue
        short_bid = short_row.iloc[0].get("bid")
        short_ask = short_row.iloc[0].get("ask")
        long_bid = long_row.iloc[0].get("bid")
        long_ask = long_row.iloc[0].get("ask")
        if (short_bid is None or short_ask is None or long_bid is None or long_ask is None
                or pd.isna(short_bid) or pd.isna(short_ask) or pd.isna(long_bid) or pd.isna(long_ask)):
            continue
        short_bid, short_ask = float(short_bid), float(short_ask)
        long_bid, long_ask = float(long_bid), float(long_ask)
        if short_bid <= 0 or long_ask <= 0:
            continue

        width = round(long_strike - short_strike, 4)
        # fill_pct=0 reduces to short_bid - long_ask, the original
        # always-cross-the-spread assumption.
        net_credit = round(
            credit_leg_fill_price(short_bid, short_ask, fill_pct)
            - debit_leg_fill_price(long_bid, long_ask, fill_pct), 4)
        if width <= 0 or net_credit <= 0:
            continue
        credit_pct = round(net_credit / width * 100, 2)
        collateral = round(width * 100, 2)

        if symbol not in pe_cache:
            pe, _eps = get_trailing_pe_and_eps(symbol)
            pe_cache[symbol] = pe
        pe = pe_cache[symbol]

        out.append({
            "symbol": symbol,
            "expiration": expiration,
            "dte": dte,
            "stock_px": round(stock_px, 2),
            "pe": pe,
            "short_strike": short_strike,
            "short_bid": short_bid,
            "short_ask": short_ask,
            "long_strike": long_strike,
            "long_bid": long_bid,
            "long_ask": long_ask,
            "width": width,
            "net_credit": net_credit,
            "credit_pct": credit_pct,
            "collateral": collateral,
            "fill_pct_at_entry": fill_pct,
            "max_profit": round(net_credit * 100, 2),
            "max_loss": round((width - net_credit) * 100, 2),
        })

    out.sort(key=lambda c: c["credit_pct"], reverse=True)
    return out

# --- yfinance quote for the exact contract ----------------------------------------

def get_yahoo_quote(symbol, expiration, strike):
    """(bid, ask) for the exact put contract, or (None, None) if yfinance has
    no usable quote for it (expiration not listed, strike not found, or
    bid/ask are NaN - all common on thinner names)."""
    _yf_rate_limiter.wait()
    try:
        t = yf.Ticker(symbol)
        if expiration not in t.options:
            return None, None
        chain = t.option_chain(expiration)
        match = chain.puts[abs(chain.puts["strike"] - strike) < 0.01]
        if match.empty:
            return None, None
        r = match.iloc[0]
        bid = r.get("bid")
        ask = r.get("ask")
        bid = float(bid) if bid is not None and not pd.isna(bid) and bid > 0 else None
        ask = float(ask) if ask is not None and not pd.isna(ask) and ask > 0 else None
        return bid, ask
    except Exception:
        return None, None


def get_yahoo_call_quote(symbol, expiration, strike):
    """Same as get_yahoo_quote but for a CALL contract - used to live-
    requote both legs of a tracked bear call spread."""
    _yf_rate_limiter.wait()
    try:
        t = yf.Ticker(symbol)
        if expiration not in t.options:
            return None, None
        chain = t.option_chain(expiration)
        match = chain.calls[abs(chain.calls["strike"] - strike) < 0.01]
        if match.empty:
            return None, None
        r = match.iloc[0]
        bid = r.get("bid")
        ask = r.get("ask")
        bid = float(bid) if bid is not None and not pd.isna(bid) and bid > 0 else None
        ask = float(ask) if ask is not None and not pd.isna(ask) and ask > 0 else None
        return bid, ask
    except Exception:
        return None, None


def get_current_stock_price(symbol):
    _yf_rate_limiter.wait()
    try:
        return float(yf.Ticker(symbol).fast_info["last_price"])
    except Exception:
        return None


def get_trailing_pe_and_eps(symbol):
    """Trailing P/E and trailing EPS at this moment, fetched together (one
    yfinance call) - used both to capture a new position's entry-time
    values and, once, to backfill a stand-in for positions tracked before
    this existed. Either can be None if yfinance has nothing (no/negative
    earnings, delisted, etc.) - a real, not uncommon case, not an error."""
    _yf_rate_limiter.wait()
    try:
        info = yf.Ticker(symbol).info
        pe = info.get("trailingPE")
        eps = info.get("trailingEps")
        return (float(pe) if pe is not None else None,
                float(eps) if eps is not None else None)
    except Exception:
        return None, None


def get_price_at(symbol, target_date_str):
    """First available close on/after target_date - used to settle a
    position once its expiration has passed."""
    _yf_rate_limiter.wait()
    try:
        td = datetime.strptime(target_date_str, "%Y-%m-%d").date()
        end = td + timedelta(days=5)
        hist = yf.Ticker(symbol).history(start=td.isoformat(), end=end.isoformat(), interval="1d")
        if hist is None or hist.empty:
            return None
        return float(hist["Close"].iloc[0])
    except Exception:
        return None

# --- position store ----------------------------------------------------------------

def load_positions():
    if not POSITIONS_FILE.exists():
        return []
    try:
        positions = json.loads(POSITIONS_FILE.read_text())
    except Exception:
        return []
    for p in positions:
        # Backward-compat: entries saved before Barchart's bid was demoted
        # to reference-only have no "bid" field - backfill using barchart_bid
        # (flagged as approx, since it wasn't actually refreshed from yfinance).
        if "bid" not in p:
            p["bid"] = p["barchart_bid"]
            p["bid_is_approx"] = True
    return positions


def save_positions(positions):
    POSITIONS_FILE.write_text(json.dumps(positions, indent=2))


def ensure_pe_at_entry(positions):
    """One-time backfill: positions tracked before the PE/EPS fields
    existed have no captured entry-time trailing P/E or EPS. Fetch today's
    values as an approximate stand-in (flagged), fetched once here and then
    frozen permanently in the stored record - never re-fetched on later
    runs, same pattern as the "bid" backward-compat migration. Returns True
    if any position changed (caller should save_positions() in that case)."""
    changed = False
    for p in positions:
        if "pe_at_entry" not in p or "eps_at_entry" not in p:
            pe, eps = get_trailing_pe_and_eps(p["symbol"])
            p["pe_at_entry"] = pe
            p["eps_at_entry"] = eps
            p["pe_at_entry_is_approx"] = True
            changed = True
    return changed


def is_already_open(positions, symbol, strike, expiration, today):
    """True if this exact CONTRACT (symbol+strike+expiration) has an
    unexpired tracked position - dedup is per-contract, not per-symbol, so a
    genuinely different, later opportunity on the same stock can still be
    tracked alongside an earlier one that's still open. (The HTML filter's
    "first signal to qualify" logic is what decides which instance of a
    symbol actually gets shown/counted for a given ROI threshold.)"""
    for p in positions:
        if (p["symbol"] == symbol and abs(p["strike"] - strike) < 0.01 and p["expiration"] == expiration
                and datetime.strptime(p["expiration"], "%Y-%m-%d").date() >= today):
            return True
    return False


# --- P&L off intrinsic value at a given price ---------------------------------
# Same formula for both cases - only the price plugged in differs: the
# CURRENT stock price for an unrealized (still-open) mark-to-market figure,
# or the stock price AT EXPIRATION for a realized (settled) final figure.

def calc_pnl_at_price(strike, bid, ask, price):
    seller_pnl = (bid - max(0.0, strike - price)) * 100
    buyer_pnl = (max(strike - price, 0.0) - ask) * 100
    return round(seller_pnl, 2), round(buyer_pnl, 2)


def calc_actual_close_pnl(entry_bid, entry_ask, current_bid, current_ask):
    """What you'd really get closing the position today, crossing the spread
    against yourself the way a real exit would - this is the "actual" side,
    as opposed to calc_pnl_at_price's intrinsic-only "fictional" side.

    Seller (short put): closing means BUYING it back - you pay the ask.
    Buyer (long put): closing means SELLING it - you receive the bid.
    Either side returns None if no live quote exists for that leg (illiquid
    contract) - callers should treat None as "no live quote," and are
    expected to fall back to the intrinsic-value ("fictional") estimate
    themselves and flag it as approximate, rather than let it collapse to
    an implicit $0 in aggregate totals."""
    seller_pnl = round((entry_bid - current_ask) * 100, 2) if current_ask is not None else None
    buyer_pnl = round((current_bid - entry_ask) * 100, 2) if current_bid is not None else None
    return seller_pnl, buyer_pnl


def calc_mid_close_pnl(entry_bid, entry_ask, current_bid, current_ask):
    """Companion to calc_actual_close_pnl using the MID price instead of
    crossing the spread - "actual" is deliberately the worst case (you pay
    the ask / receive the bid), this is a less pessimistic, more typical
    reference point using the same live quote, no extra yfinance traffic."""
    if current_bid is None or current_ask is None:
        return None, None
    mid = (current_bid + current_ask) / 2
    seller_pnl = round((entry_bid - mid) * 100, 2)
    buyer_pnl = round((mid - entry_ask) * 100, 2)
    return seller_pnl, buyer_pnl


# --- Bear call spread P&L -------------------------------------------------------

def spread_intrinsic_value(short_strike, long_strike, price):
    """What a (short_strike, long_strike) call vertical is worth at a given
    stock price - 0 if price is at/below the short strike (both legs
    worthless), the full width if price is at/above the long strike (both
    legs fully ITM), linear in between. This is what it would cost to close
    the spread at that price, or what it settles for at expiration."""
    width = long_strike - short_strike
    return max(0.0, min(width, price - short_strike))


def calc_bear_call_pnl_at_price(short_strike, long_strike, net_credit, price):
    """Fictional (intrinsic-only) P&L per spread at a given stock price -
    what you entered as credit minus what the spread is worth at that
    price. Positive while the stock stays at/below the short strike (you
    keep the full credit); shrinks, then goes negative, as price rises
    through the width."""
    return round((net_credit - spread_intrinsic_value(short_strike, long_strike, price)) * 100, 2)


def credit_leg_fill_price(bid, ask, fill_pct):
    """Price for a leg you're SELLING (short call at entry, long call at
    close) at a given fill quality - fill_pct=0 is the pessimistic/
    guaranteed-fill price (the bid), fill_pct=100 the optimistic one (the
    ask), fill_pct=50 the mid. Always crossing the spread (fill_pct=0) is
    the safe/conservative assumption but can overstate real trading costs,
    since a resting limit order between bid and ask often does fill -
    this just makes "how much of that you assume you capture" a dial
    instead of a fixed all-or-nothing choice."""
    return bid + (fill_pct / 100.0) * (ask - bid)


def debit_leg_fill_price(bid, ask, fill_pct):
    """Price for a leg you're BUYING (long call at entry, short call at
    close) at a given fill quality - mirror of credit_leg_fill_price:
    fill_pct=0 is pessimistic (the ask), fill_pct=100 optimistic (the bid),
    fill_pct=50 the mid."""
    return ask - (fill_pct / 100.0) * (ask - bid)


def calc_bear_call_actual_close_pnl(net_credit, current_short_bid, current_short_ask,
                                     current_long_bid, current_long_ask, fill_pct=0):
    """What closing the spread today would really net, at a given fill
    quality (see credit_leg_fill_price/debit_leg_fill_price) - buying back
    the short call (a debit leg) and selling the long call (a credit leg).
    fill_pct=0 reduces to the old always-cross-the-spread assumption
    (pay the short's ask, receive the long's bid). None if either leg has
    no live quote (illiquid contract) - same convention as
    calc_actual_close_pnl: callers should fall back to the intrinsic
    ("fictional") estimate rather than let a missing quote read as $0."""
    if current_short_bid is None or current_short_ask is None or current_long_bid is None or current_long_ask is None:
        return None
    close_short_cost = debit_leg_fill_price(current_short_bid, current_short_ask, fill_pct)
    close_long_proceeds = credit_leg_fill_price(current_long_bid, current_long_ask, fill_pct)
    cost_to_close = close_short_cost - close_long_proceeds
    return round((net_credit - cost_to_close) * 100, 2)


def calc_stock_equivalent(entry_px, other_px):
    """P&L (and % price change) from simply buying NORMALIZED_RISK_USD worth
    of SHARES at entry and marking to other_px (current price for an open
    position, settlement price for a closed one) - no options at all. Purely
    a benchmark: "would I have been better off just trading the stock?"
    Short is the exact negative of long, so callers only need this once.
    Returns (long_pnl, pct_change) - short_pnl is -long_pnl, short pct is
    -pct_change."""
    if entry_px is None or other_px is None or entry_px == 0:
        return None, None
    pct_change = (other_px - entry_px) / entry_px * 100
    long_pnl = round(NORMALIZED_RISK_USD * pct_change / 100, 2)
    return long_pnl, round(pct_change, 2)


def normalize_pnl(seller_pnl, buyer_pnl, strike, ask):
    """Scale a position's actual-dollar PnL to what it would've been sized at
    NORMALIZED_RISK_USD capital at risk, so positions on different-priced
    stocks (and therefore wildly different position sizes) are comparable.
    Either side may be None (e.g. no live quote for an "actual" leg)."""
    seller_risk = strike * 100
    buyer_risk = ask * 100
    norm_seller = round(seller_pnl * (NORMALIZED_RISK_USD / seller_risk), 2) if seller_pnl is not None and seller_risk > 0 else None
    norm_buyer = round(buyer_pnl * (NORMALIZED_RISK_USD / buyer_risk), 2) if buyer_pnl is not None and buyer_risk > 0 else None
    return norm_seller, norm_buyer


def calc_roi_pct(pnl, risk):
    return round(pnl / risk * 100, 2) if pnl is not None and risk > 0 else None


def annualize_roi_pct(roi_pct, days_held):
    return round(roi_pct * (365.0 / days_held), 2) if roi_pct is not None and days_held and days_held > 0 else None


def settle_expired_positions(positions, today, same_day_ok=False):
    """Once a tracked position's expiration has passed, lock in its final
    P&L using the stock price at expiration instead of continuing to mark it
    to market - settled positions are kept permanently (not dropped) so a
    realized P&L total means something.

    same_day_ok allows settling a position that expires TODAY, not just
    strictly-in-the-past ones - only safe to set True once the market has
    actually closed for the day (the caller is responsible for that check),
    since yfinance can return a live, still-moving intraday "close" for the
    current session rather than the final one while trading is ongoing."""
    changed = False
    for p in positions:
        if p.get("settled"):
            continue
        exp_date = datetime.strptime(p["expiration"], "%Y-%m-%d").date()
        if exp_date > today or (exp_date == today and not same_day_ok):
            continue
        final_px = get_price_at(p["symbol"], p["expiration"])
        if final_px is None:
            continue  # no price yet (e.g. data lag) - retry next run
        seller_pnl, buyer_pnl = calc_pnl_at_price(p["strike"], p["bid"], p["ask"], final_px)
        p["settled"] = True
        p["final_stock_px"] = final_px
        p["settled_seller_pnl"] = seller_pnl
        p["settled_buyer_pnl"] = buyer_pnl
        p["settled_at"] = today.isoformat()
        changed = True
    return changed

# --- main orchestration --------------------------------------------------------

def pick_new_candidates(barchart_rows, positions, today):
    """Every ranked candidate whose exact CONTRACT isn't already an open
    position - no daily cap, and no per-symbol limit either, since a stock
    can legitimately have more than one distinct opportunity tracked over
    time (e.g. it first qualified at 55% annualized return, then later a
    different strike/expiration on the same stock qualified at 150% - both
    get tracked; which one "counts" for a given viewing threshold is decided
    at display time, not here). Still dedups identical (symbol, strike,
    expiration) rows appearing twice within the same ranked list."""
    picked = []
    staged_contracts = set()
    for row in barchart_rows:
        key = (row["symbol"], row["strike"], row["expiration"])
        if is_already_open(positions, row["symbol"], row["strike"], row["expiration"], today) or key in staged_contracts:
            continue
        picked.append(row)
        staged_contracts.add(key)
    return picked


def add_new_position(candidate, today):
    """Barchart only identified this symbol/strike/expiration - all actual
    pricing (stock price, bid, ask) is pulled fresh from yfinance here.
    Barchart's own bid is kept only as a reference/comparison column and
    never feeds into P&L math; it's the fallback if yfinance has nothing."""
    symbol, strike, expiration = candidate["symbol"], candidate["strike"], candidate["expiration"]
    barchart_bid = candidate["barchart_bid"]

    yahoo_bid, yahoo_ask = get_yahoo_quote(symbol, expiration, strike)

    bid_is_approx = yahoo_bid is None
    bid = yahoo_bid if yahoo_bid is not None else barchart_bid

    ask_is_approx = yahoo_ask is None
    ask = yahoo_ask if yahoo_ask is not None else round(bid * YAHOO_APPROX_ASK_MULTIPLIER, 2)

    entry_stock_px = get_current_stock_price(symbol)  # yfinance, not Barchart's snapshot
    pe_at_entry, eps_at_entry = get_trailing_pe_and_eps(symbol)

    position = {
        "symbol": symbol,
        "strike": strike,
        "expiration": expiration,
        "barchart_bid": barchart_bid,  # reference only
        "bid": bid,
        "bid_is_approx": bid_is_approx,
        "ask": ask,
        "ask_is_approx": ask_is_approx,
        "potential_return_pct": candidate.get("potential_return_pct"),
        "potential_return_annual_pct": candidate.get("potential_return_annual_pct"),
        "entry_stock_px": entry_stock_px,
        "pe_at_entry": pe_at_entry,
        "eps_at_entry": eps_at_entry,
        "pe_at_entry_is_approx": False,
        "added_date": today.isoformat(),
        "expiry_type": candidate.get("expiry_type", "monthly"),
    }
    return position

# --- Bear call spread position tracking -----------------------------------------
# Same tracking philosophy as the CSP side above: every structurally valid
# spread the scan finds gets tracked as a position (open until settled), and
# the page's filter bar decides what's shown/counted - the scan itself
# doesn't gate on the credit%/collateral/PE thresholds.

BEAR_CALL_POSITIONS_FILE = Path("bear_call_spread_positions.json")


def load_bear_call_positions():
    if BEAR_CALL_POSITIONS_FILE.exists():
        return json.loads(BEAR_CALL_POSITIONS_FILE.read_text())
    return []


def save_bear_call_positions(positions):
    BEAR_CALL_POSITIONS_FILE.write_text(json.dumps(positions, indent=2))


def is_bear_call_already_open(positions, symbol, short_strike, long_strike, expiration, today):
    """Same per-contract dedup as is_already_open, keyed on the whole spread
    (both strikes) instead of a single strike."""
    for p in positions:
        if (p["symbol"] == symbol and abs(p["short_strike"] - short_strike) < 0.01
                and abs(p["long_strike"] - long_strike) < 0.01 and p["expiration"] == expiration
                and datetime.strptime(p["expiration"], "%Y-%m-%d").date() >= today):
            return True
    return False


def settle_expired_bear_call_positions(positions, today, same_day_ok=False):
    """Same settlement timing rules as settle_expired_positions - lock in
    final P&L using the stock price at expiration, keep settled positions
    permanently rather than dropping them."""
    changed = False
    for p in positions:
        if p.get("settled"):
            continue
        exp_date = datetime.strptime(p["expiration"], "%Y-%m-%d").date()
        if exp_date > today or (exp_date == today and not same_day_ok):
            continue
        final_px = get_price_at(p["symbol"], p["expiration"])
        if final_px is None:
            continue  # no price yet (e.g. data lag) - retry next run
        pnl = calc_bear_call_pnl_at_price(p["short_strike"], p["long_strike"], p["net_credit"], final_px)
        p["settled"] = True
        p["final_stock_px"] = final_px
        p["settled_pnl"] = pnl
        p["settled_at"] = today.isoformat()
        changed = True
    return changed


def pick_new_bear_call_candidates(candidates, positions, today):
    """Every scanned spread whose exact (symbol, short strike, long strike,
    expiration) isn't already an open position."""
    picked = []
    staged = set()
    for c in candidates:
        key = (c["symbol"], c["short_strike"], c["long_strike"], c["expiration"])
        if is_bear_call_already_open(positions, c["symbol"], c["short_strike"], c["long_strike"],
                                      c["expiration"], today) or key in staged:
            continue
        picked.append(c)
        staged.add(key)
    return picked


def add_new_bear_call_position(candidate, today):
    """The scan already pulled a live quote for both legs plus the
    underlying's stock price/PE for this exact spread, so just capture it
    as-is rather than re-fetching (unlike the CSP side, whose candidate rows
    only carry Barchart's own reference bid, not a real quote)."""
    return {
        "symbol": candidate["symbol"],
        "short_strike": candidate["short_strike"],
        "long_strike": candidate["long_strike"],
        "expiration": candidate["expiration"],
        "short_bid": candidate["short_bid"],
        "short_ask": candidate["short_ask"],
        "long_bid": candidate["long_bid"],
        "long_ask": candidate["long_ask"],
        "net_credit": candidate["net_credit"],
        "width": candidate["width"],
        "collateral": candidate["collateral"],
        "fill_pct_at_entry": candidate.get("fill_pct_at_entry", 0),
        "entry_stock_px": candidate["stock_px"],
        "pe_at_entry": candidate["pe"],
        "added_date": today.isoformat(),
    }

# --- realized P&L chart --------------------------------------------------------

def ensure_plot_deps():
    global plt
    if plt is not None:
        return
    try:
        import matplotlib
    except ImportError:
        _install("matplotlib")
        import matplotlib
    matplotlib.use("Agg")  # headless - just saving a PNG, no display needed
    import matplotlib.pyplot as _plt
    plt = _plt


def plot_realized_pnl(closed_rows):
    """PNG of average realized ROI% by settlement (expiration) date - how
    THAT period's batch of settlements actually performed, not a running
    cumulative dollar total. Each position's ROI % IF SOLD/BOUGHT is
    already "per $NORMALIZED_RISK_USD risked" in effect (ROI is scale-
    invariant - a position normalized to any base investment size has the
    same % return as its own actual size), so averaging those per date
    gives exactly "ROI for that period, based on the base investment"
    without needing a separate normalized-dollar computation."""
    if not closed_rows:
        return None
    ensure_plot_deps()

    by_date = {}
    counts = {}
    for r in closed_rows:
        d = datetime.strptime(r["EXPIRATION"], "%Y-%m-%d").date()
        bucket = by_date.setdefault(d, {"seller": [], "buyer": []})
        if r["ROI % IF SOLD (CSP)"] is not None:
            bucket["seller"].append(r["ROI % IF SOLD (CSP)"])
        if r["ROI % IF BOUGHT (long put)"] is not None:
            bucket["buyer"].append(r["ROI % IF BOUGHT (long put)"])
        counts[d] = counts.get(d, 0) + 1

    dates = sorted(by_date)
    avg_seller = [sum(by_date[d]["seller"]) / len(by_date[d]["seller"]) if by_date[d]["seller"] else None for d in dates]
    avg_buyer = [sum(by_date[d]["buyer"]) / len(by_date[d]["buyer"]) if by_date[d]["buyer"] else None for d in dates]
    tick_labels = [d.strftime("%b %d") + f"\n(n={counts[d]})" for d in dates]

    fig, ax = plt.subplots(figsize=(9, 5))
    ax.plot(dates, avg_seller, marker="o", label="Short (CSP seller)")
    ax.plot(dates, avg_buyer, marker="o", label="Long (put buyer)")
    ax.axhline(0, color="gray", linewidth=0.8)
    ax.set_xticks(dates)
    ax.set_xticklabels(tick_labels, rotation=45, ha="right", fontsize=8)
    ax.set_xlabel("Settlement (expiration) date  (n = closed positions that date)")
    ax.set_ylabel("Avg ROI % for that period's settlements")
    ax.set_title("Realized CSP ROI by settlement period")
    ax.legend()
    ax.grid(True, alpha=0.3)
    fig.tight_layout()
    fig.savefig(REALIZED_PNL_PNG)
    plt.close(fig)
    return REALIZED_PNL_PNG

# --- mobile-friendly HTML summary ------------------------------------------------

def _html_escape(s):
    return str(s).replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def _fmt_money(x):
    return f"${x:,.2f}" if x is not None else "--"


def _fmt_pct(x):
    return f"{x:+.1f}%" if x is not None else "--"


def _pnl_class(x):
    if x is None:
        return ""
    return "pos" if x >= 0 else "neg"


def _fmt_money_paren(x, label="mid"):
    """Parenthetical companion figure, e.g. ' (mid: $123.45)' - blank if None.
    label can be "exe" on individual cards when the figure is actually a
    guaranteed exercise value rather than a market mid-price estimate."""
    return f" ({label}: {_fmt_money(x)})" if x is not None else ""


def generate_html_summary(open_rows, closed_rows, totals, today, filter_cfg=None, run_log=None, bear_call_data=None):
    """Single self-contained HTML file - a card per position (readable on a
    phone, unlike the 20+ column CSV) plus the totals and the realized P&L
    chart if one exists. No build step, no external assets - just open it in
    a browser (or serve it as-is via GitHub Pages)."""

    def run_log_html():
        """Last 10 weekdays, oldest first, cross-referenced against run_log
        entries - a day with zero entries means GitHub's scheduler never
        actually fired (or every trigger that day failed before logging),
        not that nothing new happened to report that day (a run that found
        nothing still logs an entry, just with run_label=None). A rare
        actual market holiday will also show as "missing" here since this
        only checks weekday, not the NYSE calendar - an acceptable false
        positive for a diagnostic view."""
        by_date = {}
        for entry in (run_log or []):
            by_date.setdefault(entry.get("date"), []).append(entry)

        days = []
        d = today
        while len(days) < 10:
            if d.weekday() < 5:
                days.append(d)
            d -= timedelta(days=1)
        days.reverse()

        rows = []
        for day in days:
            day_str = day.isoformat()
            entries = sorted(by_date.get(day_str, []), key=lambda e: e.get("time_utc") or "")
            if not entries:
                rows.append(
                    f'<tr class="runlog-missing"><td>{day_str}</td>'
                    f'<td colspan="3">No runs recorded - check GitHub Actions</td></tr>'
                )
                continue
            for e in entries:
                label = _html_escape(e.get("run_label") or "--")
                if e.get("note") == "scrape_failed":
                    n_text = "Barchart scrape failed"
                elif e.get("note") == "eod_update_only":
                    n_text = "End-of-day update (no new candidates scanned)"
                else:
                    n = e.get("new_candidates")
                    n_text = "--" if n is None else str(n)
                time_utc = e.get("time_utc") or ""
                rows.append(
                    f'<tr><td>{day_str}</td><td>{label}</td>'
                    f'<td class="runlog-time" data-utc="{_html_escape(time_utc)}">{_html_escape(time_utc)}</td>'
                    f'<td>{n_text}</td></tr>'
                )
        return (
            '<table class="runlog"><thead><tr><th>Date</th><th>Run</th>'
            '<th>Time (your local)</th><th>New candidates</th></tr></thead>'
            f'<tbody>{"".join(rows)}</tbody></table>'
        )

    def bear_call_html():
        """Open and closed bear call spread positions - the same two-pass
        P&L presentation as the CSP tab (fictional intrinsic-value mark vs.
        actual live requote for open positions; locked-in P&L for closed
        ones), just single-valued instead of CSP's seller/buyer duality,
        since this is one strategy as actually entered, not two
        interpretations of the same contract. Every scanned spread gets
        tracked regardless of the credit%/collateral/PE thresholds - those
        are applied LIVE in the browser (same pattern as the CSP filter
        bar), not baked into what gets tracked."""
        data = bear_call_data or {}
        open_rows = data.get("open_rows") or []
        closed_rows = data.get("closed_rows") or []
        totals = data.get("totals") or {}
        cfg = data.get("config") or DEFAULT_BEAR_CALL_CONFIG
        target_delta = cfg.get("target_short_delta", DEFAULT_BEAR_CALL_CONFIG["target_short_delta"])

        def bc_attr(x):
            return "" if x is None else str(x)

        fict_norm_col = f"NORM P/L (FICTIONAL) (${NORMALIZED_RISK_USD:.0f} risk)"
        actual_norm_col = f"NORM P/L (ACTUAL) (${NORMALIZED_RISK_USD:.0f} risk)"
        realized_norm_col = f"NORM P/L (${NORMALIZED_RISK_USD:.0f} risk)"

        def bc_open_card(r):
            pe = r.get("PE AT ENTRY")
            pe_text = f'{pe:.1f}' if pe is not None else 'n/a'
            run_label = r.get("RUN LABEL")
            run_badge = f'<span class="run-badge">{_html_escape(run_label)}</span> ' if run_label else ''
            fict_norm = r[fict_norm_col]
            actual_norm = r[actual_norm_col]
            approx_tag = ' <span class="weekly-badge">approx</span>' if r["ACTUAL IS APPROX"] else ''
            return f'''
    <div class="card" data-kind="open" data-credit-pct="{bc_attr(r["CREDIT % OF WIDTH (entry)"])}" data-collateral="{bc_attr(r["COLLATERAL"])}" data-pe="{bc_attr(pe)}" data-stock-pct="{bc_attr(r["STOCK PCT CHANGE"])}" data-norm-fict="{bc_attr(fict_norm)}" data-norm-actual="{bc_attr(actual_norm)}" data-roi-fict="{bc_attr(r["ROI % (FICTIONAL)"])}" data-roi-actual="{bc_attr(r["ROI % (ACTUAL)"])}" data-ann-fict="{bc_attr(r["ANNUALIZED ROI % (FICTIONAL)"])}" data-ann-actual="{bc_attr(r["ANNUALIZED ROI % (ACTUAL)"])}" data-net-credit="{bc_attr(r["NET CREDIT (entry)"])}" data-cur-short-bid="{bc_attr(r["CURRENT SHORT BID"])}" data-cur-short-ask="{bc_attr(r["CURRENT SHORT ASK"])}" data-cur-long-bid="{bc_attr(r["CURRENT LONG BID"])}" data-cur-long-ask="{bc_attr(r["CURRENT LONG ASK"])}" data-days-held="{bc_attr(r["DAYS HELD"])}">
      <div class="card-title">{run_badge}{_html_escape(r["SYMBOL"])} &middot; exp {_html_escape(r["EXPIRATION"])} ({r["DAYS LEFT"]}d left)</div>
      <div>Stock ${r["CURRENT STOCK PRICE"]:.2f} (entry ${r["ENTRY STOCK PRICE"]:.2f}, {r["STOCK PCT CHANGE"]:+.1f}%)</div>
      <div>Short ${r["SHORT STRIKE"]:g}C (entry bid {r["SHORT BID (entry)"]:.2f}) &nbsp;/&nbsp; Long ${r["LONG STRIKE"]:g}C (entry ask {r["LONG ASK (entry)"]:.2f})</div>
      <div>Entry credit: <strong>${r["NET CREDIT (entry)"]:.2f}</strong> ({r["CREDIT % OF WIDTH (entry)"]:.1f}% of ${r["WIDTH"]:g} width) &middot; Collateral ${r["COLLATERAL"]:.2f} &middot; PE {pe_text}</div>
      <div class="{_pnl_class(fict_norm)}">Unrealized (fictional): {_fmt_money(fict_norm)} &middot; ROI {_fmt_pct(r["ROI % (FICTIONAL)"])} (ann. {_fmt_pct(r["ANNUALIZED ROI % (FICTIONAL)"])})</div>
      <div class="{_pnl_class(actual_norm)} bc-actual-line">Unrealized (actual, live requote{approx_tag}): <span class="bc-actual-amt">{_fmt_money(actual_norm)}</span> &middot; ROI <span class="bc-actual-roi">{_fmt_pct(r["ROI % (ACTUAL)"])}</span> (ann. <span class="bc-actual-ann">{_fmt_pct(r["ANNUALIZED ROI % (ACTUAL)"])}</span>)</div>
    </div>'''

        def bc_closed_card(r):
            pe = r.get("PE AT ENTRY")
            pe_text = f'{pe:.1f}' if pe is not None else 'n/a'
            norm = r[realized_norm_col]
            return f'''
    <div class="card" data-kind="closed" data-credit-pct="{bc_attr(r["CREDIT % OF WIDTH (entry)"])}" data-collateral="{bc_attr(r["COLLATERAL"])}" data-pe="{bc_attr(pe)}" data-stock-pct="{bc_attr(r["STOCK PCT CHANGE"])}" data-norm-realized="{bc_attr(norm)}" data-roi-realized="{bc_attr(r["ROI %"])}" data-ann-realized="{bc_attr(r["ANNUALIZED ROI %"])}">
      <div class="card-title">{_html_escape(r["SYMBOL"])} &middot; exp {_html_escape(r["EXPIRATION"])}</div>
      <div>Final stock ${r["FINAL STOCK PRICE"]:.2f} (entry ${r["ENTRY STOCK PRICE"]:.2f}, {r["STOCK PCT CHANGE"]:+.1f}%)</div>
      <div>Short ${r["SHORT STRIKE"]:g}C &nbsp;/&nbsp; Long ${r["LONG STRIKE"]:g}C &middot; width ${r["WIDTH"]:g}</div>
      <div>Entry credit: <strong>${r["NET CREDIT (entry)"]:.2f}</strong> ({r["CREDIT % OF WIDTH (entry)"]:.1f}% of width) &middot; Collateral ${r["COLLATERAL"]:.2f} &middot; PE {pe_text}</div>
      <div class="{_pnl_class(norm)}">Realized: {_fmt_money(norm)} &middot; ROI {_fmt_pct(r["ROI %"])} (ann. {_fmt_pct(r["ANNUALIZED ROI %"])})</div>
      <div class="sub2">Added {r["ADDED"]} &middot; settled {r["SETTLED AT"]}</div>
    </div>'''

        open_cards_html = ''.join(bc_open_card(r) for r in open_rows)
        closed_cards_html = ''.join(bc_closed_card(r) for r in closed_rows)

        return f'''
  <div class="updated" style="margin-top:0;">Sell the call strike closest to {target_delta:g} delta (at its bid), buy the very next strike up (at its ask) - a defined-risk bear call credit spread. The short strike is chosen by probability (delta), not just "the nearest strike above price," so it adapts to each stock's own volatility and strike spacing; the long strike is always the adjacent one above it. Reuses the same symbols as the naked-puts screen above - a separate, complementary bearish strategy with its own open/closed tracking.</div>
  <div class="filterbar">
    <label>Min credit % of width <input type="number" id="bcMinCreditPct" step="any" placeholder="-&infin;" inputmode="decimal"></label>
    <label>Max collateral $ <input type="number" id="bcMaxCollateral" step="any" placeholder="&infin;" inputmode="decimal"></label>
    <label>Min PE <input type="number" id="bcMinPe" step="any" placeholder="-&infin;" inputmode="decimal"></label>
    <button id="bcApplyFilter" type="button">Filter</button>
    <a class="editlink" href="https://github.com/mkcan1973/barchart-csp-tracker/edit/master/bear_call_spread_config.json" target="_blank" rel="noopener">Edit defaults on GitHub</a>
    <span class="count" id="bcFilterCount"></span>
  </div>

  <div class="updated" style="margin-top:0;">
    Assumed fill quality for <strong>open</strong> positions' "actual" P&amp;L (does not change entry credit, closed positions, or the fictional figures): <span id="bcFillPctLabel">{int(cfg.get("fill_pct") or 0)}</span>% &middot; 0 = pessimistic (cross the full bid-ask spread), 100 = optimistic, 50 = mid for both legs<br>
    <input type="range" id="bcFillPct" min="0" max="100" step="1" value="{int(cfg.get("fill_pct") or 0)}" style="width:100%; max-width:420px;">
  </div>

  <div class="totals">
    <div class="box">
      <div class="label">UNREALIZED (<span id="bcOpenCount">{len(open_rows)}</span> open, normalized $<span class="norm-base-num">{NORMALIZED_RISK_USD:.0f}</span>/spread)</div>
      <div class="val {_pnl_class(totals.get("unrealized_fict_total"))}" id="bcTotalFict">Fictional <span id="bcTotalFictAmt">{_fmt_money(totals.get("unrealized_fict_total"))}</span></div>
      <div class="sub2">avg ROI <span id="bcAvgFictRoi">{_fmt_pct(totals.get("avg_unrealized_fict_roi"))}</span> &middot; avg ann. ROI <span id="bcAvgFictAnn">{_fmt_pct(totals.get("avg_unrealized_fict_ann_roi"))}</span></div>
      <div class="val {_pnl_class(totals.get("unrealized_actual_total"))}" id="bcTotalActual">Actual (live requote) <span id="bcTotalActualAmt">{_fmt_money(totals.get("unrealized_actual_total"))}</span></div>
      <div class="sub2">avg ROI <span id="bcAvgActualRoi">{_fmt_pct(totals.get("avg_unrealized_actual_roi"))}</span> &middot; avg ann. ROI <span id="bcAvgActualAnn">{_fmt_pct(totals.get("avg_unrealized_actual_ann_roi"))}</span></div>
      <div class="sub2">Stock dropped from entry: <span id="bcStockDownOpen">{totals.get("stock_down_open", 0)} of {len(open_rows)} open</span></div>
    </div>
    <div class="box">
      <div class="label">REALIZED (<span id="bcRealizedCount">{totals.get("settled_count", 0)}</span> settled, normalized $<span class="norm-base-num">{NORMALIZED_RISK_USD:.0f}</span>/spread)</div>
      <div class="val {_pnl_class(totals.get("realized_total"))}" id="bcTotalRealized">Realized <span id="bcTotalRealizedAmt">{_fmt_money(totals.get("realized_total"))}</span></div>
      <div class="sub2">avg ROI <span id="bcAvgRealizedRoi">{_fmt_pct(totals.get("avg_realized_roi"))}</span> &middot; avg ann. ROI <span id="bcAvgRealizedAnn">{_fmt_pct(totals.get("avg_realized_ann_roi"))}</span></div>
      <div class="sub2">Stock dropped from entry: <span id="bcStockDownClosed">{totals.get("stock_down_closed", 0)} of {len(closed_rows)} closed</span></div>
    </div>
  </div>
  <div class="updated" id="bcFilterNote" style="display:none;">Totals above reflect only the positions currently passing the filter.</div>

  <h2 style="margin-top:0;">Open bear call spreads (<span id="bcOpenSectionCount">{len(open_rows)}</span>)</h2>
  <div class="cards" id="bcOpenCards">
  {open_cards_html}
  </div>

  <h2>Closed bear call spreads (<span id="bcClosedSectionCount">{len(closed_rows)}</span>)
    <button type="button" id="bcClosedToggle" class="expandbtn">Expand</button>
  </h2>
  <div class="cards" id="bcClosedCardsWrap" style="display:none;">
  {closed_cards_html}
  </div>
'''

    def pnl_row(label, seller_pnl, buyer_pnl, seller_roi, buyer_roi, ann_seller_roi, ann_buyer_roi, norm_seller, norm_buyer,
                norm_seller_key, norm_buyer_key,
                seller_quote=None, seller_quote_label="", buyer_quote=None, buyer_quote_label="",
                seller_mid=None, buyer_mid=None, norm_seller_mid=None, norm_buyer_mid=None,
                norm_seller_mid_key=None, norm_buyer_mid_key=None,
                seller_mid_label="mid", buyer_mid_label="mid"):
        # seller_mid/buyer_mid are on the SAME (raw, per-position) basis as
        # seller_pnl/buyer_pnl and never rescale with the base-investment
        # filter (they're real dollar estimates for THIS position's actual
        # size). norm_seller_mid/norm_buyer_mid ARE on the normalized
        # ($NORMALIZED_RISK_USD risk) basis and DO rescale - each
        # norm-*-num span below carries a data-src pointing at the card's
        # own data-norm-* attribute so the client-side filter can
        # recompute it live against whatever base investment is entered,
        # without re-deriving strike/ask risk math in JS (see applyFilter()).
        # buyer_mid_label switches to "exe" when buyer_mid is actually a
        # guaranteed exercise value (buy shares + exercise), not a market
        # mid-price estimate.
        seller_quote_html = (f'<div class="sub2">{seller_quote_label}: {_fmt_money(seller_quote)}</div>'
                              if seller_quote is not None else '')
        buyer_quote_html = (f'<div class="sub2">{buyer_quote_label}: {_fmt_money(buyer_quote)}</div>'
                             if buyer_quote is not None else '')
        seller_mid_num_html = (f'<span class="{_pnl_class(norm_seller_mid)} norm-mid-num" data-src="{norm_seller_mid_key}">{_fmt_money(norm_seller_mid)}</span>'
                                if norm_seller_mid is not None and norm_seller_mid_key else '')
        buyer_mid_num_html = (f'<span class="{_pnl_class(norm_buyer_mid)} norm-mid-num" data-src="{norm_buyer_mid_key}">{_fmt_money(norm_buyer_mid)}</span>'
                               if norm_buyer_mid is not None and norm_buyer_mid_key else '')
        return f"""
          <div class="rowlabel">{label}</div>
          <div class="grid2">
            <div class="box">
              <div class="label">LONG (bought put) - bearish, same side as short stock</div>
              <div class="val {_pnl_class(buyer_pnl)}">{_fmt_money(buyer_pnl)}<span class="{_pnl_class(buyer_mid)}">{_fmt_money_paren(buyer_mid, buyer_mid_label)}</span></div>
              <div class="sub2">ROI {_fmt_pct(buyer_roi)} &middot; ann {_fmt_pct(ann_buyer_roi)}</div>
              <div class="sub2">norm (<span class="norm-base-num">{NORMALIZED_RISK_USD:.0f}</span> risk): <span class="{_pnl_class(norm_buyer)} norm-primary-num" data-src="{norm_buyer_key}">{_fmt_money(norm_buyer)}</span>{f' ({buyer_mid_label}: ' + buyer_mid_num_html + ')' if buyer_mid_num_html else ''}</div>
              {buyer_quote_html}
            </div>
            <div class="box short-block">
              <div class="label">SHORT (sold CSP) - bullish, same side as long stock</div>
              <div class="val {_pnl_class(seller_pnl)}">{_fmt_money(seller_pnl)}<span class="{_pnl_class(seller_mid)}">{_fmt_money_paren(seller_mid, seller_mid_label)}</span></div>
              <div class="sub2">ROI {_fmt_pct(seller_roi)} &middot; ann {_fmt_pct(ann_seller_roi)}</div>
              <div class="sub2">norm (<span class="norm-base-num">{NORMALIZED_RISK_USD:.0f}</span> risk): <span class="{_pnl_class(norm_seller)} norm-primary-num" data-src="{norm_seller_key}">{_fmt_money(norm_seller)}</span>{f' ({seller_mid_label}: ' + seller_mid_num_html + ')' if seller_mid_num_html else ''}</div>
              {seller_quote_html}
            </div>
          </div>"""

    def attr(x):
        """None-safe value for an HTML data-* attribute - JS treats "" as missing."""
        return "" if x is None else str(x)

    def position_card(r, closed):
        actual_norm_seller_key = f"NORM P/L (ACTUAL) IF SOLD (${NORMALIZED_RISK_USD:.0f} risk)"
        actual_norm_buyer_key = f"NORM P/L (ACTUAL) IF BOUGHT (${NORMALIZED_RISK_USD:.0f} risk)"
        mid_norm_seller_key = f"NORM P/L (MID) IF SOLD (${NORMALIZED_RISK_USD:.0f} risk)"
        mid_norm_buyer_key = f"NORM P/L (MID) IF BOUGHT (${NORMALIZED_RISK_USD:.0f} risk)"
        realized_norm_seller_key = f"NORM P/L IF SOLD (${NORMALIZED_RISK_USD:.0f} risk)"
        realized_norm_buyer_key = f"NORM P/L IF BOUGHT (${NORMALIZED_RISK_USD:.0f} risk)"

        price_line = (f"Final {r['FINAL STOCK PRICE']:.2f}" if closed
                      else f"Now {r['CURRENT STOCK PRICE']:.2f}" if r["CURRENT STOCK PRICE"] is not None else "Now --")
        if closed:
            days_line = f"Settled {r['SETTLED AT']}"
        else:
            days_active = (today - datetime.strptime(r["ADDED"], "%Y-%m-%d").date()).days
            days_line = f"{days_active}d active &middot; {r['DAYS LEFT']}d left"

        if closed:
            rows_html = pnl_row("REALIZED", r["REALIZED P/L IF SOLD (CSP)"], r["REALIZED P/L IF BOUGHT (long put)"],
                                 r["ROI % IF SOLD (CSP)"], r["ROI % IF BOUGHT (long put)"],
                                 r["ANNUALIZED ROI % IF SOLD (CSP)"], r["ANNUALIZED ROI % IF BOUGHT (long put)"],
                                 r[realized_norm_seller_key], r[realized_norm_buyer_key],
                                 norm_seller_key="data-norm-rs", norm_buyer_key="data-norm-rb")
            data_attrs = (
                f'data-kind="closed" data-expiration="{attr(r["EXPIRATION"])}" '
                f'data-norm-rs="{attr(r[realized_norm_seller_key])}" data-norm-rb="{attr(r[realized_norm_buyer_key])}" '
                f'data-roi-rs="{attr(r["ROI % IF SOLD (CSP)"])}" data-roi-rb="{attr(r["ROI % IF BOUGHT (long put)"])}" '
                f'data-ann-rs="{attr(r["ANNUALIZED ROI % IF SOLD (CSP)"])}" data-ann-rb="{attr(r["ANNUALIZED ROI % IF BOUGHT (long put)"])}" '
                f'data-stock-long="{attr(r["STOCK LONG P/L"])}" data-stock-short="{attr(r["STOCK SHORT P/L"])}" '
                f'data-stock-pct="{attr(r["STOCK PCT CHANGE"])}" data-stock-pct-ann="{attr(r["STOCK PCT CHANGE ANN"])}"'
            )
        else:
            # Once buying shares at today's price and exercising the put is
            # already profitable net of the premium paid (pure intrinsic
            # value, independent of the option's own - possibly thin -
            # market quotes), that guaranteed value is a more useful
            # reference than a market mid-price guess - build_summary()
            # already substituted it into UNREALIZED/NORM P/L (MID) IF
            # BOUGHT for this position. Relabel it "exe" here so the card
            # makes clear it's a guaranteed exercise value, not a market
            # estimate. Doesn't apply to the SHORT side - a seller has no
            # equivalent voluntary exercise path.
            buyer_mid_is_exercise = r.get("BUYER MID IS EXERCISE", False)
            buyer_mid_label = "exe" if buyer_mid_is_exercise else "mid"

            rows_html = pnl_row("ACTUAL (real quote, crossing the spread to close now)",
                                 r["UNREALIZED P/L (ACTUAL) IF SOLD (CSP)"], r["UNREALIZED P/L (ACTUAL) IF BOUGHT (long put)"],
                                 r["ROI % (ACTUAL) IF SOLD (CSP)"], r["ROI % (ACTUAL) IF BOUGHT (long put)"],
                                 r["ANNUALIZED ROI % (ACTUAL) IF SOLD (CSP)"], r["ANNUALIZED ROI % (ACTUAL) IF BOUGHT (long put)"],
                                 r[actual_norm_seller_key], r[actual_norm_buyer_key],
                                 norm_seller_key="data-norm-as", norm_buyer_key="data-norm-ab",
                                 seller_quote=r["CURRENT OPTION ASK"], seller_quote_label="current ask (pay to close)",
                                 buyer_quote=r["CURRENT OPTION BID"], buyer_quote_label="current bid (receive to close)",
                                 seller_mid=r["UNREALIZED P/L (MID) IF SOLD (CSP)"],
                                 buyer_mid=r["UNREALIZED P/L (MID) IF BOUGHT (long put)"],
                                 norm_seller_mid=r[mid_norm_seller_key], norm_buyer_mid=r[mid_norm_buyer_key],
                                 norm_seller_mid_key="data-norm-ms", norm_buyer_mid_key="data-norm-mb",
                                 buyer_mid_label=buyer_mid_label)
            if buyer_mid_is_exercise:
                rows_html += ('<div class="sub2">Long "exe" = buy shares + exercise the put '
                               '(guaranteed, independent of the option\'s own market quotes)</div>')
            seller_approx_labels = [lbl for lbl, flag in (("ACTUAL", r.get("ACTUAL SELLER IS APPROX")),
                                                           ("MID", r.get("MID SELLER IS APPROX"))) if flag]
            buyer_approx_labels = [lbl for lbl, flag in (("ACTUAL", r.get("ACTUAL BUYER IS APPROX")),
                                                          ("MID", r.get("MID BUYER IS APPROX"))) if flag]
            if seller_approx_labels and seller_approx_labels == buyer_approx_labels:
                rows_html += (f'<div class="sub2">Short and Long {" and ".join(seller_approx_labels)} approximated via '
                               f'intrinsic value - no live option quote (likely far OTM/illiquid)</div>')
            else:
                if seller_approx_labels:
                    rows_html += (f'<div class="sub2 short-block">Short {" and ".join(seller_approx_labels)} approximated via '
                                   f'intrinsic value - no live option quote (likely far OTM/illiquid)</div>')
                if buyer_approx_labels:
                    rows_html += (f'<div class="sub2">Long {" and ".join(buyer_approx_labels)} approximated via '
                                   f'intrinsic value - no live option quote (likely far OTM/illiquid)</div>')
            data_attrs = (
                f'data-kind="open" '
                f'data-norm-as="{attr(r[actual_norm_seller_key])}" data-norm-ab="{attr(r[actual_norm_buyer_key])}" '
                f'data-roi-as="{attr(r["ROI % (ACTUAL) IF SOLD (CSP)"])}" data-roi-ab="{attr(r["ROI % (ACTUAL) IF BOUGHT (long put)"])}" '
                f'data-ann-as="{attr(r["ANNUALIZED ROI % (ACTUAL) IF SOLD (CSP)"])}" data-ann-ab="{attr(r["ANNUALIZED ROI % (ACTUAL) IF BOUGHT (long put)"])}" '
                f'data-norm-ms="{attr(r[mid_norm_seller_key])}" data-norm-mb="{attr(r[mid_norm_buyer_key])}" '
                f'data-stock-long="{attr(r["STOCK LONG P/L"])}" data-stock-short="{attr(r["STOCK SHORT P/L"])}" '
                f'data-stock-pct="{attr(r["STOCK PCT CHANGE"])}" data-stock-pct-ann="{attr(r["STOCK PCT CHANGE ANN"])}" '
                f'data-cur-stock="{attr(r["CURRENT STOCK PRICE"])}" data-cur-bid="{attr(r["CURRENT OPTION BID"])}" '
                f'data-cur-ask="{attr(r["CURRENT OPTION ASK"])}" data-buyer-mid-exercise="{"1" if buyer_mid_is_exercise else "0"}"'
            )

        ann_return = r.get('BARCHART ANNUALIZED RETURN % (at selection)')
        pe = r.get('PE AT ENTRY')
        pe_text = f"{pe:.1f}" if pe is not None else "--"
        dte_entry = r.get('DTE AT ENTRY')
        # Today's run-of-the-day label (A/B/C) - only shown while the
        # position is still today's, purely to let a same-day Discord
        # message be visually matched to its webpage card. Gone the next
        # day the page regenerates, since r['ADDED'] no longer equals today.
        run_label = r.get('RUN LABEL')
        run_badge = (f'<span class="run-badge">{_html_escape(run_label)}</span>'
                     if run_label and not closed and r['ADDED'] == today.isoformat() else '')
        expiry_type = r.get('EXPIRY TYPE', 'monthly')
        weekly_badge = '<span class="weekly-badge">weekly</span>' if expiry_type == 'weekly' else ''
        portfolio_key = f"{r['SYMBOL']}|{attr(r['STRIKE'])}|{r['EXPIRATION']}"
        return f"""
        <div class="card" data-ann-return="{attr(ann_return)}" data-pe="{attr(pe)}" data-dte-entry="{attr(dte_entry)}" data-ask="{attr(r.get('ASK'))}" data-strike="{attr(r['STRIKE'])}" data-symbol="{_html_escape(r['SYMBOL'])}" data-added="{attr(r['ADDED'])}" data-expiry-type="{expiry_type}" {data_attrs}>
          <div class="card-head">
            <span class="sym">{_html_escape(r['SYMBOL'])}</span>
            <span class="strike">${r['STRIKE']:g}P</span>
            <span class="exp">{r['EXPIRATION']}</span>
            {weekly_badge}
            {run_badge}
          </div>
          <div class="sub">{days_line} &middot; Entry {r['ENTRY STOCK PRICE']:.2f} &middot; {price_line}
            &middot; bid {r['BID']:.2f}/{r['BID SOURCE']} &middot; ask {r['ASK']:.2f}/{r['ASK SOURCE']}</div>
          <div class="sub">Barchart ann. return at selection: {_fmt_pct(ann_return)} &middot; PE at entry: {pe_text} ({r.get('PE SOURCE', '')}) &middot; DTE at entry: {dte_entry if dte_entry is not None else '--'}</div>
          {rows_html}
          <label class="pf-check-label"><input type="checkbox" class="portfolio-check" data-key="{_html_escape(portfolio_key)}"> Add to my portfolio</label>
        </div>"""

    # Newest day first, and within the same day newest RUN first (C before
    # B before A) so the most recent Discord alert lines up with the top
    # of the list, not the bottom - positions.json preserves run order but
    # has no finer-grained timestamp than the date, so run_label is the
    # tiebreaker. Positions from before this field existed sort last
    # within their day (empty string sorts below any letter here).
    open_rows_newest_first = sorted(open_rows, key=lambda r: (r["ADDED"], r.get("RUN LABEL") or ""), reverse=True)
    open_cards = "\n".join(position_card(r, closed=False) for r in open_rows_newest_first) or '<p class="empty">No open positions.</p>'
    closed_cards = "\n".join(position_card(r, closed=True) for r in reversed(closed_rows)) or '<p class="empty">No closed positions yet.</p>'

    # Live, client-side-drawn chart (not the static PNG) so it redraws from
    # whatever closed cards are currently passing the filter bar - the PNG
    # is still generated (see plot_realized_pnl) as a non-interactive
    # snapshot, but no longer what the page itself shows.
    chart_html = ""
    if totals["png_path"]:
        chart_html = '<h2>Realized P&amp;L over time</h2><canvas id="realizedChart" class="chart" width="900" height="420"></canvas>'

    html = f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>CSP Tracker</title>
<style>
  :root {{ color-scheme: light dark; }}
  body {{ font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif;
          margin: 0; padding: 16px; max-width: 900px; margin-inline: auto;
          background: #0b0e14; color: #e6e9ef; }}
  h1 {{ font-size: 1.4rem; margin-bottom: 0; }}
  h2 {{ font-size: 1.1rem; margin-top: 28px; border-top: 1px solid #2a2f3a; padding-top: 16px;
        display: flex; align-items: center; gap: 10px; }}
  .expandbtn {{ padding: 4px 12px; border-radius: 6px; border: 1px solid #3ddc84; background: transparent;
                color: #3ddc84; font-weight: 700; font-size: 0.78rem; cursor: pointer; }}
  .tabbar {{ display: flex; gap: 8px; margin: 10px 0 18px; }}
  .tabbtn {{ padding: 6px 16px; border-radius: 8px 8px 0 0; border: 1px solid #2a2f3a; border-bottom: none;
             background: #161b25; color: #9aa4b2; font-weight: 700; font-size: 0.85rem; cursor: pointer; }}
  .tabbtn-active {{ background: #0b0e14; color: #3ddc84; border-color: #3ddc84; }}
  .card-title {{ font-weight: 600; margin-bottom: 6px; }}
  .updated {{ color: #9aa4b2; font-size: 0.85rem; margin-top: 2px; margin-bottom: 20px; }}
  table.runlog {{ width: 100%; border-collapse: collapse; font-size: 0.82rem; margin-top: 8px; }}
  table.runlog th, table.runlog td {{ text-align: left; padding: 5px 8px; border-bottom: 1px solid #2a2f3a; }}
  table.runlog tr.runlog-missing td {{ color: #ff6b6b; }}
  .totals {{ display: grid; grid-template-columns: repeat(auto-fit, minmax(240px, 1fr)); gap: 12px; margin-bottom: 8px; }}
  .totals .box {{ background: #161b25; border-radius: 10px; padding: 12px 14px; }}
  .cards {{ display: grid; grid-template-columns: repeat(auto-fit, minmax(300px, 1fr)); gap: 12px; }}
  .card {{ background: #161b25; border-radius: 12px; padding: 14px 16px; }}
  .card-head {{ display: flex; align-items: baseline; gap: 8px; font-weight: 600; }}
  .card-head .sym {{ font-size: 1.15rem; }}
  .card-head .strike {{ color: #9aa4b2; }}
  .card-head .exp {{ margin-left: auto; color: #9aa4b2; font-weight: 400; font-size: 0.9rem; }}
  .run-badge {{ display: inline-flex; align-items: center; justify-content: center; width: 1.4em; height: 1.4em;
    border-radius: 50%; background: #2563eb; color: #fff; font-size: 0.8rem; font-weight: 700; }}
  .weekly-badge {{ display: inline-flex; align-items: center; padding: 1px 7px; border-radius: 10px;
    background: #7c3aed; color: #fff; font-size: 0.68rem; font-weight: 700; letter-spacing: 0.03em; }}
  .pf-check-label {{ display: flex; align-items: center; gap: 6px; margin-top: 10px;
    font-size: 0.78rem; color: #9aa4b2; cursor: pointer; }}
  .portfolio-card .portfolio-fields {{ display: grid; grid-template-columns: 1fr 1fr; gap: 10px; margin-top: 10px; }}
  .portfolio-card .portfolio-fields label {{ display: flex; flex-direction: column; gap: 3px;
    font-size: 0.72rem; color: #9aa4b2; }}
  .portfolio-card .portfolio-fields input, .portfolio-card .portfolio-fields select {{
    padding: 6px 8px; border-radius: 6px; border: 1px solid #333a47; background: #0f131b;
    color: inherit; font-size: 0.9rem; }}
  .portfolio-card .pf-sold-field, .portfolio-card .pf-exercised-field {{ display: none !important; }}
  .portfolio-card[data-exit-type="sold"] .pf-sold-field {{ display: flex !important; }}
  .portfolio-card[data-exit-type="exercised"] .pf-exercised-field {{ display: flex !important; }}
  .portfolio-card .pf-live-field {{ display: none !important; margin-top: 10px; }}
  .portfolio-card[data-exit-type=""] .pf-live-field {{ display: block !important; }}
  .portfolio-card .pf-pnl {{ margin-top: 10px; font-size: 0.95rem; font-weight: 700; }}
  .portfolio-card .pf-remove {{ margin-top: 10px; }}
  .sub {{ color: #9aa4b2; font-size: 0.82rem; margin-top: 4px; }}
  .sub2 {{ color: #9aa4b2; font-size: 0.78rem; margin-top: 2px; }}
  .rowlabel {{ font-size: 0.72rem; letter-spacing: 0.03em; color: #9aa4b2; margin-top: 10px; }}
  .grid2 {{ display: grid; grid-template-columns: 1fr 1fr; gap: 10px; margin-top: 10px; }}
  .short-block {{ display: none; }}
  .short-inline {{ display: none; }}
  body.show-short .short-block {{ display: block; }}
  body.show-short .short-inline {{ display: inline; }}
  body:not(.show-short) .grid2 {{ grid-template-columns: 1fr; }}
  .box {{ background: #0f131b; border-radius: 8px; padding: 8px 10px; }}
  .label {{ font-size: 0.72rem; letter-spacing: 0.04em; color: #9aa4b2; }}
  .val {{ font-size: 1.15rem; font-weight: 700; }}
  .pos {{ color: #3ddc84; }}
  .neg {{ color: #ff6b6b; }}
  .empty {{ color: #9aa4b2; font-style: italic; }}
  .chart {{ width: 100%; height: auto; border-radius: 10px; margin-top: 10px; background: white; }}
  .filterbar {{ display: flex; flex-wrap: wrap; align-items: flex-end; gap: 10px;
                background: #161b25; border-radius: 10px; padding: 12px 14px; margin-bottom: 14px; }}
  .filterbar label {{ display: flex; flex-direction: column; gap: 3px; font-size: 0.75rem; color: #9aa4b2; }}
  .filterbar input {{ width: 90px; padding: 7px 8px; border-radius: 6px; border: 1px solid #333a47;
                       background: #0f131b; color: inherit; font-size: 0.95rem; }}
  .filterbar button {{ padding: 8px 16px; border-radius: 6px; border: none; background: #3ddc84;
                        color: #06240f; font-weight: 700; font-size: 0.9rem; cursor: pointer; }}
  .filterbar button.expirytogglebtn {{ background: #7c3aed; color: #fff; }}
  .filterbar a.editlink {{ padding: 8px 16px; border-radius: 6px; border: 1px solid #3ddc84;
                            background: transparent; color: #3ddc84; font-weight: 700;
                            font-size: 0.85rem; text-decoration: none; }}
  .filterbar .count {{ color: #9aa4b2; font-size: 0.8rem; margin-left: auto; align-self: center; }}
  @media (prefers-color-scheme: light) {{
    body {{ background: #f5f6f8; color: #1a1d23; }}
    .totals .box, .card, .box {{ background: #ffffff; box-shadow: 0 1px 3px rgba(0,0,0,0.08); }}
    .label, .sub, .sub2, .rowlabel, .updated, .card-head .exp, .card-head .strike {{ color: #6b7280; }}
    .filterbar {{ background: #ffffff; box-shadow: 0 1px 3px rgba(0,0,0,0.08); }}
    .filterbar label {{ color: #6b7280; }}
    .filterbar input {{ background: #f5f6f8; border-color: #d0d5dd; }}
    .filterbar a.editlink {{ border-color: #0969da; color: #0969da; }}
    .expandbtn {{ border-color: #0969da; color: #0969da; }}
    .filterbar .count {{ color: #6b7280; }}
    table.runlog th, table.runlog td {{ border-bottom-color: #e0e3e8; }}
    .tabbtn {{ background: #ffffff; border-color: #d0d5dd; color: #6b7280; }}
    .tabbtn-active {{ background: #f5f6f8; color: #0969da; border-color: #0969da; }}
  }}
</style>
</head>
<body>
  <h1>Barchart CSP Tracker</h1>
  <div class="tabbar">
    <button type="button" id="tabBtnCsp" class="tabbtn tabbtn-active">CSP</button>
    <button type="button" id="tabBtnBearCall" class="tabbtn">Bear Call Spread</button>
  </div>
  <div id="cspTabContent">
  <div class="updated">Last updated {today.isoformat()} &middot; {len(open_rows)} open &middot; {len(closed_rows)} closed</div>

  <div class="filterbar">
    <label>Min ROI % <input type="number" id="minRoi" step="any" placeholder="-&infin;" inputmode="decimal"></label>
    <label>Max ROI % <input type="number" id="maxRoi" step="any" placeholder="&infin;" inputmode="decimal"></label>
    <label>Min PE <input type="number" id="minPe" step="any" placeholder="-&infin;" inputmode="decimal"></label>
    <label>Max PE <input type="number" id="maxPe" step="any" placeholder="&infin;" inputmode="decimal"></label>
    <label>Min DTE@entry <input type="number" id="minDte" step="any" placeholder="-&infin;" inputmode="decimal"></label>
    <label>Max DTE@entry <input type="number" id="maxDte" step="any" placeholder="&infin;" inputmode="decimal"></label>
    <label>Base investment $ <input type="number" id="baseInvest" step="any" placeholder="e.g. 1000" inputmode="decimal"></label>
    <label>Min put strike <input type="number" id="minPutStrike" step="any" placeholder="-&infin;" inputmode="decimal"></label>
    <label>Max put strike <input type="number" id="maxPutStrike" step="any" placeholder="&infin;" inputmode="decimal"></label>
    <button type="button" id="expiryToggle" class="expirytogglebtn" data-state="monthly">Expirations: Monthly only</button>
    <button id="applyFilter" type="button">Filter</button>
    <a class="editlink" href="https://github.com/mkcan1973/barchart-csp-tracker/edit/master/discord_filter_config.json" target="_blank" rel="noopener">Edit filters on GitHub</a>
    <span class="count" id="filterCount"></span>
  </div>
  <div class="updated" style="margin-top:-6px;">ROI filters on Barchart's annualized return at selection; PE filters on trailing P/E at entry (both frozen at entry, always available)</div>
  <div class="updated" style="margin-top:-6px;">Below = option position, NOT shares. Long = bought the put (bearish - same side as shorting stock)<span class="short-inline">. Short = sold the CSP (bullish - same side as owning stock)</span>.</div>
  <button type="button" id="shortToggle" class="expandbtn" style="margin-bottom:12px;">Show seller/short (bullish) view</button>

  <h2 style="margin-top:0;">My portfolio (<span id="portfolioCount">0</span>)
    <button type="button" id="portfolioToggle" class="expandbtn">Expand</button>
  </h2>
  <div id="portfolioWrap" style="display:none;">
    <div class="updated" style="margin-top:0;">Your actual real-money long-put trades - separate from the simulated/live-quote figures below. Check the box on any open or closed card to add it here. Stored only in this browser's local storage, so nothing here is backed up automatically - use Export to save a copy, and Import to restore it or move it to another browser/device.</div>
    <div style="margin-bottom:14px;">
      <button type="button" id="portfolioUnlockBtn" class="expandbtn">Unlock editing</button>
      <button type="button" id="portfolioExport" class="expandbtn">Export portfolio (JSON)</button>
      <button type="button" id="portfolioImportBtn" class="expandbtn">Import portfolio (JSON)</button>
      <input type="file" id="portfolioImportFile" accept="application/json" style="display:none;">
    </div>
    <div class="totals" style="margin-bottom:14px;">
      <div class="box">
        <div class="label">PORTFOLIO TOTALS</div>
        <div class="val" id="portfolioRealizedTotal">--</div>
        <div class="sub2">Realized P&amp;L (sold + exercised positions)</div>
        <div class="val" id="portfolioUnrealizedTotal">--</div>
        <div class="sub2">Unrealized P&amp;L (live est., still-open positions)</div>
        <div class="val" id="portfolioOpenCost">--</div>
        <div class="sub2">Cost basis of still-open positions (qty &times; purchase price &times; 100)</div>
      </div>
    </div>
    <div class="cards" id="portfolioCards"></div>
  </div>

  <div class="totals">
    <div class="box">
      <div class="label">UNREALIZED - ACTUAL, worst case (<span id="openCount">{len(open_rows)}</span> open, normalized $<span class="norm-base-num">{NORMALIZED_RISK_USD:.0f}</span>/position)</div>
      <div class="val {_pnl_class(totals['unrealized_actual_buyer_total'])}" id="totalActualBuyer">Long <span id="totalActualBuyerAmt">{_fmt_money(totals['unrealized_actual_buyer_total'])}</span><span id="totalActualBuyerMid" class="{_pnl_class(totals['unrealized_mid_buyer_total'])}">{_fmt_money_paren(totals['unrealized_mid_buyer_total'])}</span></div>
      <div class="val short-block {_pnl_class(totals['unrealized_actual_seller_total'])}" id="totalActualSeller">Short <span id="totalActualSellerAmt">{_fmt_money(totals['unrealized_actual_seller_total'])}</span><span id="totalActualSellerMid" class="{_pnl_class(totals['unrealized_mid_seller_total'])}">{_fmt_money_paren(totals['unrealized_mid_seller_total'])}</span></div>
      <div class="sub2">avg ROI: <span class="short-inline">short <span id="avgActualSellerRoi">{_fmt_pct(totals['avg_unrealized_actual_seller_roi'])}</span> / </span>long <span id="avgActualBuyerRoi">{_fmt_pct(totals['avg_unrealized_actual_buyer_roi'])}</span></div>
      <div class="sub2">avg ann. ROI: <span class="short-inline">short <span id="avgActualSellerAnn">{_fmt_pct(totals['avg_unrealized_actual_seller_ann_roi'])}</span> / </span>long <span id="avgActualBuyerAnn">{_fmt_pct(totals['avg_unrealized_actual_buyer_ann_roi'])}</span></div>
      <div class="sub2">(mid) = less pessimistic reference using the mid price instead of crossing the spread</div>
    </div>
    <div class="box">
      <div class="label">REALIZED (<span id="realizedCount">{totals['settled_count']}</span> settled, normalized $<span class="norm-base-num">{NORMALIZED_RISK_USD:.0f}</span>/position)</div>
      <div class="val {_pnl_class(totals['realized_buyer_total'])}" id="totalRealizedBuyer">Long <span id="totalRealizedBuyerAmt">{_fmt_money(totals['realized_buyer_total'])}</span></div>
      <div class="val short-block {_pnl_class(totals['realized_seller_total'])}" id="totalRealizedSeller">Short <span id="totalRealizedSellerAmt">{_fmt_money(totals['realized_seller_total'])}</span></div>
      <div class="sub2">avg ROI: <span class="short-inline">short <span id="avgRealizedSellerRoi">{_fmt_pct(totals['avg_realized_seller_roi'])}</span> / </span>long <span id="avgRealizedBuyerRoi">{_fmt_pct(totals['avg_realized_buyer_roi'])}</span></div>
      <div class="sub2">avg ann. ROI: <span class="short-inline">short <span id="avgRealizedSellerAnn">{_fmt_pct(totals['avg_realized_seller_ann_roi'])}</span> / </span>long <span id="avgRealizedBuyerAnn">{_fmt_pct(totals['avg_realized_buyer_ann_roi'])}</span></div>
    </div>
    <div class="box">
      <div class="label">STOCK BENCHMARK (no options - buy/short $<span class="norm-base-num">{NORMALIZED_RISK_USD:.0f}</span> of shares at entry)</div>
      <div class="val {_pnl_class(totals['stock_unrealized_short_total'])}" id="totalStockUnrealShort">Open, Short <span id="totalStockUnrealShortAmt">{_fmt_money(totals['stock_unrealized_short_total'])}</span></div>
      <div class="val short-block {_pnl_class(totals['stock_unrealized_long_total'])}" id="totalStockUnrealLong">Open, Long <span id="totalStockUnrealLongAmt">{_fmt_money(totals['stock_unrealized_long_total'])}</span></div>
      <div class="sub2">avg price change (open): <span id="avgStockUnrealPct">{_fmt_pct(totals['avg_stock_unrealized_pct'])}</span> &middot; avg ann. ROI: <span id="avgStockUnrealAnn">{_fmt_pct(totals['avg_stock_unrealized_ann_roi'])}</span></div>
      <div class="val {_pnl_class(totals['stock_realized_short_total'])}" id="totalStockRealShort">Closed, Short <span id="totalStockRealShortAmt">{_fmt_money(totals['stock_realized_short_total'])}</span></div>
      <div class="val short-block {_pnl_class(totals['stock_realized_long_total'])}" id="totalStockRealLong">Closed, Long <span id="totalStockRealLongAmt">{_fmt_money(totals['stock_realized_long_total'])}</span></div>
      <div class="sub2">avg price change (closed): <span id="avgStockRealPct">{_fmt_pct(totals['avg_stock_realized_pct'])}</span> &middot; avg ann. ROI: <span id="avgStockRealAnn">{_fmt_pct(totals['avg_stock_realized_ann_roi'])}</span></div>
      <div class="sub2">Stock actually dropped from entry: <span id="stockDownOpen">{totals['stock_down_open']} of {len(open_rows)} open</span> &middot; <span id="stockDownClosed">{totals['stock_down_closed']} of {len(closed_rows)} closed</span></div>
      <div class="sub2">Indicator only - short assumes unlimited-risk shorting is actually available.</div>
    </div>
  </div>
  <div class="updated" id="filterNote" style="display:none;">Totals above reflect only the positions currently passing the filter.</div>

  {chart_html}

  <h2>Open positions (<span id="openSectionCount">{len(open_rows)}</span>)</h2>
  <div class="cards">
  {open_cards}
  </div>

  <h2>Closed positions (<span id="closedSectionCount">{len(closed_rows)}</span>)
    <button type="button" id="closedToggle" class="expandbtn">Expand</button>
  </h2>
  <div class="cards" id="closedCardsWrap" style="display:none;">
  {closed_cards}
  </div>

  <h2>Run log (last 10 weekdays)
    <button type="button" id="runLogToggle" class="expandbtn">Expand</button>
  </h2>
  <div id="runLogWrap" style="display:none;">
    <div class="updated" style="margin-top:0;">One row per actual script execution that passed the market-open check - a day with no rows means the scheduled trigger never ran that day (see GitHub Actions), not that nothing new was found.</div>
    {run_log_html()}
  </div>
  </div>

  <div id="bearCallTabContent" style="display:none;">
  <h2 style="margin-top:0;">Bear Call Spread candidates</h2>
  <a class="editlink" href="https://github.com/mkcan1973/barchart-csp-tracker/edit/master/bear_call_spread_config.json" target="_blank" rel="noopener">Edit thresholds on GitHub</a>
  {bear_call_html()}
  </div>

<script>
(function() {{
  var DEFAULT_FILTERS = {json.dumps(filter_cfg or DEFAULT_FILTER_CONFIG)};
  var DEFAULT_BEAR_CALL_FILTERS = {json.dumps((bear_call_data or {}).get("config") or DEFAULT_BEAR_CALL_CONFIG)};
  function fmtMoney(x) {{
    return x === null ? '--' : '$' + x.toLocaleString('en-US', {{minimumFractionDigits: 2, maximumFractionDigits: 2}});
  }}
  function fmtMoneyParen(x) {{
    return x === null ? '' : ' (mid: ' + fmtMoney(x) + ')';
  }}
  function fmtPct(x) {{
    return x === null ? '--' : (x >= 0 ? '+' : '') + x.toFixed(1) + '%';
  }}
  function pnlClass(x) {{
    return x === null ? '' : (x >= 0 ? 'pos' : 'neg');
  }}
  function readAttr(card, name) {{
    var v = card.getAttribute(name);
    if (v === null || v === '') return null;
    var f = parseFloat(v);
    return isNaN(f) ? null : f;
  }}
  function sumAttr(cards, name) {{
    var total = 0;
    cards.forEach(function(c) {{ total += (readAttr(c, name) || 0); }});
    return Math.round(total * 100) / 100;
  }}
  function avgAttr(cards, name) {{
    var vals = [];
    cards.forEach(function(c) {{ var v = readAttr(c, name); if (v !== null) vals.push(v); }});
    if (!vals.length) return null;
    return Math.round((vals.reduce(function(a, b) {{ return a + b; }}, 0) / vals.length) * 100) / 100;
  }}
  function setMoney(divId, amtId, val) {{
    var div = document.getElementById(divId);
    var amt = document.getElementById(amtId);
    if (div) {{
      // Only swap the pos/neg class - preserve every other class already on
      // the element (e.g. short-block), since this runs on every filter
      // change and would otherwise wipe out that server-rendered class.
      var keep = div.className.split(' ').filter(function(c) {{ return c !== 'pos' && c !== 'neg' && c !== ''; }});
      var cls = pnlClass(val);
      if (cls) keep.push(cls);
      div.className = keep.join(' ');
    }}
    if (amt) amt.textContent = fmtMoney(val);
  }}
  function setPct(id, val) {{
    var el = document.getElementById(id);
    if (el) el.textContent = fmtPct(val);
  }}

  function applyFilter() {{
    var minRoiRaw = document.getElementById('minRoi').value.trim();
    var maxRoiRaw = document.getElementById('maxRoi').value.trim();
    var minPeRaw = document.getElementById('minPe').value.trim();
    var maxPeRaw = document.getElementById('maxPe').value.trim();
    var minDteRaw = document.getElementById('minDte').value.trim();
    var maxDteRaw = document.getElementById('maxDte').value.trim();
    var baseInvestRaw = document.getElementById('baseInvest').value.trim();
    var minPutStrikeRaw = document.getElementById('minPutStrike').value.trim();
    var maxPutStrikeRaw = document.getElementById('maxPutStrike').value.trim();
    var noFilter = minRoiRaw === '' && maxRoiRaw === '' && minPeRaw === '' && maxPeRaw === ''
      && minDteRaw === '' && maxDteRaw === '' && baseInvestRaw === ''
      && minPutStrikeRaw === '' && maxPutStrikeRaw === '';
    var minRoi = minRoiRaw === '' ? -Infinity : parseFloat(minRoiRaw);
    var maxRoi = maxRoiRaw === '' ? Infinity : parseFloat(maxRoiRaw);
    var minPe = minPeRaw === '' ? -Infinity : parseFloat(minPeRaw);
    var maxPe = maxPeRaw === '' ? Infinity : parseFloat(maxPeRaw);
    var minDte = minDteRaw === '' ? -Infinity : parseFloat(minDteRaw);
    var maxDte = maxDteRaw === '' ? Infinity : parseFloat(maxDteRaw);
    var baseInvest = baseInvestRaw === '' ? Infinity : parseFloat(baseInvestRaw);
    var minPutStrike = minPutStrikeRaw === '' ? -Infinity : parseFloat(minPutStrikeRaw);
    var maxPutStrike = maxPutStrikeRaw === '' ? Infinity : parseFloat(maxPutStrikeRaw);
    var expiryFilter = (document.getElementById('expiryToggle').dataset.state) || 'monthly';
    // Separate from baseInvest (which uses Infinity as "no filter"): this is
    // what every "norm ($X risk)" figure on the page rescales against -
    // defaults to the server's own $NORMALIZED_RISK_USD baseline when the
    // box is empty, so the page looks identical to today's cards until you
    // actually type something.
    var normBase = baseInvestRaw === '' ? {NORMALIZED_RISK_USD:.0f} : parseFloat(baseInvestRaw);
    var normScale = normBase / {NORMALIZED_RISK_USD:.0f};
    var cards = document.querySelectorAll('.card[data-ann-return]');

    // Pass 1: which cards individually clear the ROI, PE, DTE@entry, AND
    // base-investment ranges? (A range with both bounds blank is treated
    // as "not filtering on this dimension," so e.g. setting only PE still
    // lets every ROI value through.)
    var passing = [];
    cards.forEach(function(card) {{
      var roiRaw = card.getAttribute('data-ann-return');
      var roiVal = roiRaw === '' ? null : parseFloat(roiRaw);
      var roiOk = (minRoiRaw === '' && maxRoiRaw === '')
        || (roiVal !== null && !isNaN(roiVal) && roiVal >= minRoi && roiVal <= maxRoi);

      // No trailing P/E ("--" on the card) means unprofitable/undefined,
      // not zero - treat it as infinite so it correctly fails a Max PE
      // cap but still passes a Min-PE-only filter (infinity clears any
      // finite floor).
      var peRaw = card.getAttribute('data-pe');
      var peVal = peRaw === '' ? Infinity : parseFloat(peRaw);
      var peOk = (minPeRaw === '' && maxPeRaw === '')
        || (!isNaN(peVal) && peVal >= minPe && peVal <= maxPe);

      // Base investment: the option's own premium x 100 is what it
      // actually costs to control one contract - exclude anything pricier
      // than this account size (NOT the strike-based CSP collateral,
      // which is a separate, much larger number).
      var askRaw = card.getAttribute('data-ask');
      var askVal = askRaw === '' ? null : parseFloat(askRaw);
      var investOk = baseInvestRaw === ''
        || (askVal !== null && !isNaN(askVal) && askVal * 100 <= baseInvest);

      // Put strike - lets you skip low-strike puts with little profit
      // potential on the long side, or cap how high a strike to consider.
      var strikeRaw = card.getAttribute('data-strike');
      var strikeVal = strikeRaw === '' ? null : parseFloat(strikeRaw);
      var putStrikeOk = (minPutStrikeRaw === '' && maxPutStrikeRaw === '')
        || (strikeVal !== null && !isNaN(strikeVal) && strikeVal >= minPutStrike && strikeVal <= maxPutStrike);

      var dteRaw = card.getAttribute('data-dte-entry');
      var dteVal = dteRaw === '' ? null : parseFloat(dteRaw);
      var dteOk = (minDteRaw === '' && maxDteRaw === '')
        || (dteVal !== null && !isNaN(dteVal) && dteVal >= minDte && dteVal <= maxDte);

      // Independent of every other dimension above (and of noFilter) - this
      // is a 3-way visibility gate (monthly only / weekly only / both), not
      // a quality threshold, so it applies even when nothing else is being
      // filtered on.
      var expiryOk = expiryFilter === 'both' || card.getAttribute('data-expiry-type') === expiryFilter;

      if (expiryOk && (noFilter || (roiOk && peOk && dteOk && investOk && putStrikeOk))) {{
        passing.push(card);
      }}
    }});

    // Pass 2: with an actual filter active, only one instance per symbol
    // PER OPEN/CLOSED BUCKET represents "the trade you'd have taken" - a
    // symbol can legitimately show once in OPEN (its current position) AND
    // once in CLOSED (an earlier, already-settled trade on the same stock)
    // at the same time, since those are two genuinely different, sequential
    // trades, not a duplicate of the same one. Open and closed never
    // compete with each other for a single slot. Within a bucket, if a
    // symbol has both a monthly and a weekly candidate, only the
    // chronologically FIRST one wins - a symbol can't occupy both monthly
    // and weekly within the same open-or-closed bucket at once.
    var selected;
    if (noFilter) {{
      selected = passing;
    }} else {{
      var firstForSymbol = {{}};
      passing.forEach(function(card) {{
        var sym = card.getAttribute('data-symbol');
        var kind = card.getAttribute('data-kind');
        var key = sym + '|' + kind;
        var added = card.getAttribute('data-added') || '';
        var current = firstForSymbol[key];
        if (!current || added < current.getAttribute('data-added')) {{
          firstForSymbol[key] = card;
        }}
      }});
      selected = Object.keys(firstForSymbol).map(function(key) {{ return firstForSymbol[key]; }});
    }}
    var selectedSet = new Set(selected);

    var openVisible = [];
    var closedVisible = [];
    var totalOpenCount = 0;
    var totalClosedCount = 0;
    cards.forEach(function(card) {{
      var isOpen = card.getAttribute('data-kind') === 'open';
      if (isOpen) {{ totalOpenCount++; }} else {{ totalClosedCount++; }}
      var visible = selectedSet.has(card);
      card.style.display = visible ? '' : 'none';
      if (visible) {{
        (isOpen ? openVisible : closedVisible).push(card);
      }}
    }});
    // Broken out by open/closed, not just one combined number, so this
    // reconciles directly with the open/closed counts shown elsewhere on
    // the page (the "Last updated" header, the section headers) instead
    // of leaving you to guess how a filtered total splits.
    var countEl = document.getElementById('filterCount');
    if (countEl) {{
      countEl.textContent = openVisible.length + ' open + ' + closedVisible.length + ' closed shown '
        + '(of ' + totalOpenCount + ' open, ' + totalClosedCount + ' closed total)';
    }}

    // Rescale every per-card "norm (...)" figure (and the box-label $
    // baselines) to normBase - these are tagged with data-src pointing at
    // the card's own $NORMALIZED_RISK_USD-basis data-norm-* attribute, so
    // the underlying P&L math never needs re-deriving in JS, just scaled.
    document.querySelectorAll('.norm-base-num').forEach(function(el) {{
      el.textContent = Math.round(normBase);
    }});
    cards.forEach(function(card) {{
      card.querySelectorAll('.norm-primary-num, .norm-mid-num').forEach(function(el) {{
        var src = el.getAttribute('data-src');
        if (!src) return;
        var raw = readAttr(card, src);
        var scaled = raw === null ? null : raw * normScale;
        el.textContent = fmtMoney(scaled);
        var keepClasses = el.className.split(' ').filter(function(c) {{ return c !== 'pos' && c !== 'neg' && c !== ''; }});
        var newCls = pnlClass(scaled);
        if (newCls) keepClasses.push(newCls);
        el.className = keepClasses.join(' ');
      }});
    }});

    // Recompute every total/average from only the currently-visible cards -
    // same sum/average math the Python side uses, just run over a subset.
    // Normalized $ totals also get rescaled by normScale so they stay on
    // the SAME basis as the per-card "norm (...)" figures below, not stuck
    // at the server's original $NORMALIZED_RISK_USD baseline.
    setMoney('totalActualSeller', 'totalActualSellerAmt', sumAttr(openVisible, 'data-norm-as') * normScale);
    setMoney('totalActualBuyer', 'totalActualBuyerAmt', sumAttr(openVisible, 'data-norm-ab') * normScale);
    var midSellerVal = sumAttr(openVisible, 'data-norm-ms') * normScale;
    var midBuyerVal = sumAttr(openVisible, 'data-norm-mb') * normScale;
    var midSellerEl = document.getElementById('totalActualSellerMid');
    var midBuyerEl = document.getElementById('totalActualBuyerMid');
    if (midSellerEl) {{ midSellerEl.textContent = fmtMoneyParen(midSellerVal); midSellerEl.className = pnlClass(midSellerVal); }}
    if (midBuyerEl) {{ midBuyerEl.textContent = fmtMoneyParen(midBuyerVal); midBuyerEl.className = pnlClass(midBuyerVal); }}
    setPct('avgActualSellerRoi', avgAttr(openVisible, 'data-roi-as'));
    setPct('avgActualBuyerRoi', avgAttr(openVisible, 'data-roi-ab'));
    setPct('avgActualSellerAnn', avgAttr(openVisible, 'data-ann-as'));
    setPct('avgActualBuyerAnn', avgAttr(openVisible, 'data-ann-ab'));

    setMoney('totalRealizedSeller', 'totalRealizedSellerAmt', sumAttr(closedVisible, 'data-norm-rs') * normScale);
    setMoney('totalRealizedBuyer', 'totalRealizedBuyerAmt', sumAttr(closedVisible, 'data-norm-rb') * normScale);
    setPct('avgRealizedSellerRoi', avgAttr(closedVisible, 'data-roi-rs'));
    setPct('avgRealizedBuyerRoi', avgAttr(closedVisible, 'data-roi-rb'));
    setPct('avgRealizedSellerAnn', avgAttr(closedVisible, 'data-ann-rs'));
    setPct('avgRealizedBuyerAnn', avgAttr(closedVisible, 'data-ann-rb'));

    setMoney('totalStockUnrealLong', 'totalStockUnrealLongAmt', sumAttr(openVisible, 'data-stock-long') * normScale);
    setMoney('totalStockUnrealShort', 'totalStockUnrealShortAmt', sumAttr(openVisible, 'data-stock-short') * normScale);
    setPct('avgStockUnrealPct', avgAttr(openVisible, 'data-stock-pct'));
    setPct('avgStockUnrealAnn', avgAttr(openVisible, 'data-stock-pct-ann'));
    setMoney('totalStockRealLong', 'totalStockRealLongAmt', sumAttr(closedVisible, 'data-stock-long') * normScale);
    setMoney('totalStockRealShort', 'totalStockRealShortAmt', sumAttr(closedVisible, 'data-stock-short') * normScale);
    setPct('avgStockRealPct', avgAttr(closedVisible, 'data-stock-pct'));
    setPct('avgStockRealAnn', avgAttr(closedVisible, 'data-stock-pct-ann'));

    function countStockDown(cards) {{
      var n = 0;
      cards.forEach(function(card) {{
        var v = parseFloat(card.getAttribute('data-stock-pct'));
        if (!isNaN(v) && v < 0) n++;
      }});
      return n;
    }}
    var stockDownOpenEl = document.getElementById('stockDownOpen');
    if (stockDownOpenEl) stockDownOpenEl.textContent = countStockDown(openVisible) + ' of ' + openVisible.length + ' open';
    var stockDownClosedEl = document.getElementById('stockDownClosed');
    if (stockDownClosedEl) stockDownClosedEl.textContent = countStockDown(closedVisible) + ' of ' + closedVisible.length + ' closed';

    var openCountEl = document.getElementById('openCount');
    if (openCountEl) openCountEl.textContent = openVisible.length;
    var realizedCountEl = document.getElementById('realizedCount');
    if (realizedCountEl) realizedCountEl.textContent = closedVisible.length;
    var openSectionCountEl = document.getElementById('openSectionCount');
    if (openSectionCountEl) openSectionCountEl.textContent = openVisible.length;
    var closedSectionCountEl = document.getElementById('closedSectionCount');
    if (closedSectionCountEl) closedSectionCountEl.textContent = closedVisible.length;

    var noteEl = document.getElementById('filterNote');
    if (noteEl) noteEl.style.display = noFilter ? 'none' : '';

    drawRealizedChart(closedVisible);
  }}

  // Redrawn from whatever closed cards are CURRENTLY passing the filter -
  // same per-expiration-date averaging as the server's plot_realized_pnl(),
  // just run client-side so it actually responds to the filter bar instead
  // of being a fixed snapshot from whenever the page was last generated.
  function drawRealizedChart(closedCards) {{
    var canvas = document.getElementById('realizedChart');
    if (!canvas) return;
    // Size the canvas's actual pixel buffer to its real on-screen CSS
    // width (plus devicePixelRatio for sharpness) rather than leaving it
    // at a fixed internal resolution - otherwise all the text/line widths
    // below are sized relative to that fixed resolution and end up tiny
    // once CSS scales a wide canvas down to a narrow phone screen.
    var dpr = window.devicePixelRatio || 1;
    var W = canvas.clientWidth || 900;
    var H = 320;
    canvas.width = W * dpr;
    canvas.height = H * dpr;
    canvas.style.height = H + 'px';
    var ctx = canvas.getContext('2d');
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.clearRect(0, 0, W, H);

    var byDate = {{}};
    closedCards.forEach(function(card) {{
      var d = card.getAttribute('data-expiration');
      if (!d) return;
      var bucket = byDate[d] || (byDate[d] = {{seller: [], buyer: [], n: 0}});
      var roiS = card.getAttribute('data-roi-rs');
      var roiB = card.getAttribute('data-roi-rb');
      if (roiS !== '' && roiS !== null) bucket.seller.push(parseFloat(roiS));
      if (roiB !== '' && roiB !== null) bucket.buyer.push(parseFloat(roiB));
      bucket.n++;
    }});
    var dates = Object.keys(byDate).sort();

    ctx.font = '13px -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif';
    if (!dates.length) {{
      ctx.fillStyle = '#9aa4b2';
      ctx.fillText('No closed positions match the current filter.', 20, H / 2);
      return;
    }}

    function avg(arr) {{ return arr.length ? arr.reduce(function(a, b) {{ return a + b; }}, 0) / arr.length : null; }}
    var sellerVals = dates.map(function(d) {{ return avg(byDate[d].seller); }});
    var buyerVals = dates.map(function(d) {{ return avg(byDate[d].buyer); }});
    var allVals = sellerVals.concat(buyerVals).filter(function(v) {{ return v !== null; }});
    var minV = Math.min(0, allVals.length ? Math.min.apply(null, allVals) : 0);
    var maxV = Math.max(0, allVals.length ? Math.max.apply(null, allVals) : 0);
    if (minV === maxV) {{ minV -= 1; maxV += 1; }}
    var padL = 55, padR = 20, padT = 24, padB = 70;
    var plotW = W - padL - padR, plotH = H - padT - padB;

    function xFor(i) {{ return padL + (dates.length <= 1 ? plotW / 2 : (i / (dates.length - 1)) * plotW); }}
    function yFor(v) {{ return padT + plotH - ((v - minV) / (maxV - minV)) * plotH; }}

    ctx.strokeStyle = '#2a2f3a';
    ctx.fillStyle = '#9aa4b2';
    ctx.textAlign = 'right';
    var steps = 5;
    for (var s = 0; s <= steps; s++) {{
      var v = minV + (maxV - minV) * (s / steps);
      var y = yFor(v);
      ctx.beginPath(); ctx.moveTo(padL, y); ctx.lineTo(W - padR, y);
      ctx.globalAlpha = 0.25; ctx.stroke(); ctx.globalAlpha = 1;
      ctx.fillText(v.toFixed(0) + '%', padL - 8, y + 4);
    }}
    ctx.strokeStyle = '#6b7280';
    ctx.beginPath(); ctx.moveTo(padL, yFor(0)); ctx.lineTo(W - padR, yFor(0)); ctx.stroke();

    function drawSeries(vals, color) {{
      ctx.strokeStyle = color; ctx.fillStyle = color; ctx.lineWidth = 2;
      ctx.beginPath();
      var started = false;
      vals.forEach(function(v, i) {{
        if (v === null) return;
        var x = xFor(i), y = yFor(v);
        if (!started) {{ ctx.moveTo(x, y); started = true; }} else {{ ctx.lineTo(x, y); }}
      }});
      ctx.stroke();
      vals.forEach(function(v, i) {{
        if (v === null) return;
        var x = xFor(i), y = yFor(v);
        ctx.beginPath(); ctx.arc(x, y, 3.5, 0, Math.PI * 2); ctx.fill();
      }});
    }}
    drawSeries(sellerVals, '#2563eb');
    drawSeries(buyerVals, '#f97316');

    ctx.fillStyle = '#9aa4b2';
    ctx.font = '10px -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif';
    dates.forEach(function(d, i) {{
      var x = xFor(i);
      ctx.save();
      ctx.translate(x, H - padB + 14);
      ctx.rotate(-Math.PI / 4);
      ctx.textAlign = 'right';
      ctx.fillText(d.slice(5) + ' (n=' + byDate[d].n + ')', 0, 0);
      ctx.restore();
    }});

    ctx.textAlign = 'left';
    ctx.font = '12px -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif';
    ctx.fillStyle = '#2563eb'; ctx.fillRect(padL, 4, 10, 10);
    ctx.fillStyle = '#9aa4b2'; ctx.fillText('Short (CSP seller)', padL + 14, 13);
    ctx.fillStyle = '#f97316'; ctx.fillRect(padL + 150, 4, 10, 10);
    ctx.fillStyle = '#9aa4b2'; ctx.fillText('Long (put buyer)', padL + 164, 13);
  }}

  var closedToggleBtn = document.getElementById('closedToggle');
  var closedWrap = document.getElementById('closedCardsWrap');
  if (closedToggleBtn && closedWrap) {{
    closedToggleBtn.addEventListener('click', function() {{
      var collapsed = closedWrap.style.display === 'none';
      closedWrap.style.display = collapsed ? '' : 'none';
      closedToggleBtn.textContent = collapsed ? 'Collapse' : 'Expand';
    }});
  }}

  var runLogToggleBtn = document.getElementById('runLogToggle');
  var runLogWrap = document.getElementById('runLogWrap');
  if (runLogToggleBtn && runLogWrap) {{
    runLogToggleBtn.addEventListener('click', function() {{
      var collapsed = runLogWrap.style.display === 'none';
      runLogWrap.style.display = collapsed ? '' : 'none';
      runLogToggleBtn.textContent = collapsed ? 'Collapse' : 'Expand';
    }});
  }}
  // Server renders UTC timestamps (it doesn't know the viewer's timezone) -
  // swap each one to the viewer's own local time/zone once, on load.
  document.querySelectorAll('.runlog-time').forEach(function(el) {{
    var utc = el.getAttribute('data-utc');
    if (!utc) return;
    var d = new Date(utc);
    if (!isNaN(d.getTime())) el.textContent = d.toLocaleString();
  }});

  // Long puts are the actual strategy here - short/CSP-seller figures are
  // hidden everywhere (totals boxes, every card) by default via the
  // short-block/short-inline CSS classes, and this one button reveals them
  // all at once instead of each card needing its own toggle.
  var shortToggleBtn = document.getElementById('shortToggle');
  if (shortToggleBtn) {{
    shortToggleBtn.addEventListener('click', function() {{
      var showing = document.body.classList.toggle('show-short');
      shortToggleBtn.textContent = showing ? 'Hide seller/short (bullish) view' : 'Show seller/short (bullish) view';
    }});
  }}

  // --- My portfolio: YOUR actual real-money trades, entered by hand -
  // entirely separate from the simulated/live-quote figures elsewhere on
  // the page. No backend exists (this is a static GitHub Pages site), so
  // this can only live in this browser's own localStorage - Export/Import
  // below are the only backup/cross-device path. Keyed by
  // "symbol|strike|expiration" so a checkbox on any card (open or closed)
  // maps straight to one portfolio entry.
  var PORTFOLIO_KEY = 'csp_portfolio_v1';
  function loadPortfolio() {{
    try {{
      var raw = localStorage.getItem(PORTFOLIO_KEY);
      return raw ? JSON.parse(raw) : {{}};
    }} catch (e) {{ return {{}}; }}
  }}
  function savePortfolio() {{
    try {{ localStorage.setItem(PORTFOLIO_KEY, JSON.stringify(portfolio)); }} catch (e) {{}}
  }}
  var portfolio = loadPortfolio();

  // Casual edit lock - NOT real security. The password is only kept as a
  // SHA-256 hash (via the browser's own crypto.subtle, no library needed)
  // so it isn't sitting in the page as plain text for a quick glance at
  // view-source to reveal - but this whole page's source, including this
  // exact check and hash, is still publicly visible on a public GitHub
  // repo, so anyone willing to hash a few guesses (or just read the code
  // and remove the disabled attributes themselves) can still get past it.
  // This only deters someone from idly clicking around on a shared link -
  // it keeps the portfolio viewable (unlocked or not) while gating edits.
  var PORTFOLIO_UNLOCK_KEY = 'csp_portfolio_unlocked';
  var PORTFOLIO_EDIT_PASSWORD_HASH = '8c6976e5b5410415bde908bd4dee15dfb167a9c873fc4bb8a81f6f2ab448a918';
  var portfolioUnlocked = sessionStorage.getItem(PORTFOLIO_UNLOCK_KEY) === '1';

  function sha256Hex(text) {{
    var data = new TextEncoder().encode(text);
    return crypto.subtle.digest('SHA-256', data).then(function(buf) {{
      return Array.prototype.map.call(new Uint8Array(buf), function(b) {{
        return b.toString(16).padStart(2, '0');
      }}).join('');
    }});
  }}

  function applyPortfolioLockState() {{
    var locked = !portfolioUnlocked;
    document.querySelectorAll('.portfolio-check').forEach(function(cb) {{ cb.disabled = locked; }});
    document.querySelectorAll('#portfolioCards input, #portfolioCards select, #portfolioCards button').forEach(function(el) {{
      el.disabled = locked;
    }});
    var importBtn = document.getElementById('portfolioImportBtn');
    if (importBtn) importBtn.disabled = locked;
    var unlockBtn = document.getElementById('portfolioUnlockBtn');
    if (unlockBtn) unlockBtn.textContent = locked ? 'Unlock editing' : 'Lock editing';
  }}

  var portfolioUnlockBtn = document.getElementById('portfolioUnlockBtn');
  if (portfolioUnlockBtn) {{
    portfolioUnlockBtn.addEventListener('click', function() {{
      if (portfolioUnlocked) {{
        portfolioUnlocked = false;
        sessionStorage.removeItem(PORTFOLIO_UNLOCK_KEY);
        applyPortfolioLockState();
        return;
      }}
      var entered = prompt('Enter the edit password:');
      if (entered === null) return;  // cancelled
      sha256Hex(entered.toLowerCase()).then(function(hash) {{
        if (hash === PORTFOLIO_EDIT_PASSWORD_HASH) {{
          portfolioUnlocked = true;
          sessionStorage.setItem(PORTFOLIO_UNLOCK_KEY, '1');
          applyPortfolioLockState();
        }} else {{
          alert('Incorrect password.');
        }}
      }});
    }});
  }}

  function portfolioPnl(entry, strike) {{
    var qty = entry.qty;
    var pp = entry.purchase_price;
    if (!qty || pp === null || pp === undefined) return null;
    if (entry.exit_type === 'sold') {{
      if (entry.exit_price === null || entry.exit_price === undefined) return null;
      return (entry.exit_price - pp) * 100 * qty;
    }}
    if (entry.exit_type === 'exercised') {{
      if (entry.stock_buy_price === null || entry.stock_buy_price === undefined) return null;
      return (strike - entry.stock_buy_price - pp) * 100 * qty;
    }}
    return null;  // still open - no realized P&L yet
  }}

  function keyParts(key) {{
    var parts = key.split('|');
    return {{ symbol: parts[0], strike: parseFloat(parts[1]), expiration: parts[2] }};
  }}

  function renderPortfolioCard(key, entry) {{
    var kp = keyParts(key);
    var exitType = entry.exit_type || '';
    function numAttr(v) {{ return (v === null || v === undefined) ? '' : v; }}
    return '' +
      '<div class="card portfolio-card" data-key="' + key + '" data-exit-type="' + exitType + '">' +
        '<div class="card-head"><span class="sym">' + kp.symbol + '</span>' +
        '<span class="strike">$' + kp.strike + 'P</span>' +
        '<span class="exp">' + kp.expiration + '</span></div>' +
        '<div class="portfolio-fields">' +
          '<label>Qty (contracts) <input type="number" min="0" step="1" data-field="qty" value="' + numAttr(entry.qty) + '"></label>' +
          '<label>Purchase price $/put <input type="number" step="any" data-field="purchase_price" value="' + numAttr(entry.purchase_price) + '" placeholder="e.g. 1.25"></label>' +
          '<label>Status <select data-field="exit_type">' +
            '<option value=""' + (exitType === '' ? ' selected' : '') + '>Still open</option>' +
            '<option value="sold"' + (exitType === 'sold' ? ' selected' : '') + '>Sold the put</option>' +
            '<option value="exercised"' + (exitType === 'exercised' ? ' selected' : '') + '>Exercised</option>' +
          '</select></label>' +
          '<label>Exit date <input type="date" data-field="exit_date" value="' + (entry.exit_date || '') + '"></label>' +
          '<label class="pf-sold-field">Sell price $/put <input type="number" step="any" data-field="exit_price" value="' + numAttr(entry.exit_price) + '" placeholder="e.g. 2.10"></label>' +
          '<label class="pf-exercised-field">Stock buy price $/share <input type="number" step="any" data-field="stock_buy_price" value="' + numAttr(entry.stock_buy_price) + '" placeholder="e.g. 14.50"></label>' +
        '</div>' +
        '<div class="sub2 pf-live-field">Now (stock): <span class="pf-cur-stock">--</span> &middot; put bid/ask: <span class="pf-cur-bid">--</span>/<span class="pf-cur-ask">--</span></div>' +
        '<div class="pf-pnl"><span class="pf-pnl-label">Unrealized P&amp;L (live est.)</span>: <span class="pf-pnl-val">--</span></div>' +
        '<button type="button" class="expandbtn pf-remove" data-action="remove">Remove from portfolio</button>' +
      '</div>';
  }}

  // Reuses the SAME live quote data already fetched server-side for this
  // exact contract's own open/closed card (data-cur-stock/-bid/-ask,
  // added alongside the portfolio checkbox) - no separate live fetch
  // needed, since a portfolio entry's key always matches one real card.
  function findOriginalCard(key) {{
    var cb = document.querySelector('.portfolio-check[data-key="' + CSS.escape(key) + '"]');
    return cb ? cb.closest('.card') : null;
  }}

  // Live unrealized estimate for a still-open entry, reusing the SAME
  // live quote data already fetched server-side for this exact contract's
  // own open card (data-cur-stock/-bid/-ask) - no separate fetch needed.
  // Mirrors the non-portfolio ACTUAL-vs-exercise logic: sell now at the
  // current bid unless exercising (intrinsic value) is actually better,
  // just computed against YOUR purchase price and quantity instead of the
  // simulated entry/normalized figures. Returns null fields when the
  // underlying card has no live quote (or is itself already closed).
  function portfolioLiveEstimate(key, entry, strike) {{
    var orig = findOriginalCard(key);
    var out = {{curStock: null, curBid: null, curAsk: null, pnl: null, useExercise: false}};
    if (!orig || orig.getAttribute('data-kind') !== 'open') return out;
    var curStockRaw = orig.getAttribute('data-cur-stock');
    var curBidRaw = orig.getAttribute('data-cur-bid');
    var curAskRaw = orig.getAttribute('data-cur-ask');
    out.curStock = curStockRaw ? parseFloat(curStockRaw) : null;
    out.curBid = curBidRaw ? parseFloat(curBidRaw) : null;
    out.curAsk = curAskRaw ? parseFloat(curAskRaw) : null;
    var qty = entry.qty, pp = entry.purchase_price;
    if (!qty || pp === null || pp === undefined) return out;
    var actualPnl = out.curBid === null ? null : (out.curBid - pp) * 100 * qty;
    var fictPnl = out.curStock === null ? null : (Math.max(strike - out.curStock, 0) - pp) * 100 * qty;
    var useExercise = fictPnl !== null && fictPnl > 0 && (actualPnl === null || fictPnl > actualPnl);
    out.pnl = useExercise ? fictPnl : actualPnl;
    out.useExercise = useExercise;
    return out;
  }}

  function updatePortfolioCardPnl(card) {{
    var key = card.getAttribute('data-key');
    var kp = keyParts(key);
    var entry = portfolio[key];
    if (!entry) return;
    var labelEl = card.querySelector('.pf-pnl-label');
    var el = card.querySelector('.pf-pnl-val');
    if (!el) return;

    if (entry.exit_type) {{
      if (labelEl) labelEl.textContent = 'Realized P&L';
      var pnl = portfolioPnl(entry, kp.strike);
      el.textContent = pnl === null ? '--' : fmtMoney(Math.round(pnl * 100) / 100);
      el.className = 'pf-pnl-val ' + (pnl === null ? '' : pnlClass(pnl));
      return;
    }}

    if (labelEl) labelEl.textContent = 'Unrealized P&L (live est.)';
    var est = portfolioLiveEstimate(key, entry, kp.strike);
    var curStockEl = card.querySelector('.pf-cur-stock');
    var curBidEl = card.querySelector('.pf-cur-bid');
    var curAskEl = card.querySelector('.pf-cur-ask');
    if (curStockEl) curStockEl.textContent = est.curStock === null ? '--' : est.curStock.toFixed(2);
    if (curBidEl) curBidEl.textContent = est.curBid === null ? '--' : est.curBid.toFixed(2);
    if (curAskEl) curAskEl.textContent = est.curAsk === null ? '--' : est.curAsk.toFixed(2);
    el.textContent = est.pnl === null ? '--' : fmtMoney(Math.round(est.pnl * 100) / 100) + (est.useExercise ? ' (exe)' : ' (sell now)');
    el.className = 'pf-pnl-val ' + (est.pnl === null ? '' : pnlClass(est.pnl));
  }}

  function updatePortfolioTotals() {{
    var totalRealized = 0, anyRealized = false;
    var totalOpenCost = 0, anyOpen = false;
    var totalUnrealized = 0, anyUnrealized = false;
    Object.keys(portfolio).forEach(function(key) {{
      var kp = keyParts(key);
      var entry = portfolio[key];
      var pnl = portfolioPnl(entry, kp.strike);
      if (pnl !== null) {{
        totalRealized += pnl; anyRealized = true;
        return;
      }}
      if (entry.qty && entry.purchase_price !== null && entry.purchase_price !== undefined) {{
        totalOpenCost += entry.qty * entry.purchase_price * 100; anyOpen = true;
      }}
      var est = portfolioLiveEstimate(key, entry, kp.strike);
      if (est.pnl !== null) {{ totalUnrealized += est.pnl; anyUnrealized = true; }}
    }});
    var realizedEl = document.getElementById('portfolioRealizedTotal');
    if (realizedEl) {{
      realizedEl.textContent = anyRealized ? fmtMoney(Math.round(totalRealized * 100) / 100) : '--';
      realizedEl.className = 'val' + (anyRealized ? ' ' + pnlClass(totalRealized) : '');
    }}
    var costEl = document.getElementById('portfolioOpenCost');
    if (costEl) costEl.textContent = anyOpen ? fmtMoney(Math.round(totalOpenCost * 100) / 100) : '--';
    var unrealizedEl = document.getElementById('portfolioUnrealizedTotal');
    if (unrealizedEl) {{
      unrealizedEl.textContent = anyUnrealized ? fmtMoney(Math.round(totalUnrealized * 100) / 100) : '--';
      unrealizedEl.className = 'val' + (anyUnrealized ? ' ' + pnlClass(totalUnrealized) : '');
    }}
    var countEl = document.getElementById('portfolioCount');
    if (countEl) countEl.textContent = Object.keys(portfolio).length;
  }}

  function renderPortfolio() {{
    var wrap = document.getElementById('portfolioCards');
    if (!wrap) return;
    var keys = Object.keys(portfolio).sort();
    wrap.innerHTML = keys.length
      ? keys.map(function(k) {{ return renderPortfolioCard(k, portfolio[k]); }}).join('')
      : '<p class="empty">No positions added yet - check the box on any open or closed card below to add it here.</p>';
    keys.forEach(function(k) {{
      var card = wrap.querySelector('.portfolio-card[data-key="' + CSS.escape(k) + '"]');
      if (card) updatePortfolioCardPnl(card);
    }});
    updatePortfolioTotals();
    applyPortfolioLockState();  // re-render rebuilds the cards from scratch - reapply disabled state
  }}

  var portfolioWrap = document.getElementById('portfolioCards');
  if (portfolioWrap) {{
    ['input', 'change'].forEach(function(evt) {{
      portfolioWrap.addEventListener(evt, function(e) {{
        var field = e.target.getAttribute('data-field');
        if (!field) return;
        var card = e.target.closest('.portfolio-card');
        var key = card.getAttribute('data-key');
        var entry = portfolio[key];
        if (!entry) return;
        var raw = e.target.value;
        if (field === 'qty' || field === 'purchase_price' || field === 'exit_price' || field === 'stock_buy_price') {{
          entry[field] = raw === '' ? null : parseFloat(raw);
        }} else {{
          entry[field] = raw || null;
        }}
        if (field === 'exit_type') {{
          card.setAttribute('data-exit-type', raw || '');
        }}
        savePortfolio();
        updatePortfolioCardPnl(card);
        updatePortfolioTotals();
      }});
    }});
    portfolioWrap.addEventListener('click', function(e) {{
      if (e.target.getAttribute('data-action') !== 'remove') return;
      var card = e.target.closest('.portfolio-card');
      var key = card.getAttribute('data-key');
      if (!confirm('Remove ' + key.replace(/\\|/g, ' ') + ' from your portfolio? Everything entered for it (qty, prices, exit info) will be deleted.')) {{
        return;
      }}
      delete portfolio[key];
      savePortfolio();
      var cb = document.querySelector('.portfolio-check[data-key="' + CSS.escape(key) + '"]');
      if (cb) cb.checked = false;
      renderPortfolio();
    }});
  }}

  document.querySelectorAll('.portfolio-check').forEach(function(cb) {{
    var key = cb.getAttribute('data-key');
    cb.checked = !!portfolio[key];
    cb.addEventListener('change', function() {{
      if (cb.checked) {{
        if (!portfolio[key]) {{
          portfolio[key] = {{
            qty: 1, purchase_price: null, exit_type: null,
            exit_price: null, stock_buy_price: null, exit_date: null,
          }};
        }}
      }} else {{
        if (!confirm('Remove ' + key.replace(/\\|/g, ' ') + ' from your portfolio? Everything entered for it (qty, prices, exit info) will be deleted.')) {{
          cb.checked = true;  // user backed out - undo the uncheck
          return;
        }}
        delete portfolio[key];
      }}
      savePortfolio();
      renderPortfolio();
    }});
  }});

  var portfolioToggleBtn = document.getElementById('portfolioToggle');
  var portfolioSectionWrap = document.getElementById('portfolioWrap');
  if (portfolioToggleBtn && portfolioSectionWrap) {{
    portfolioToggleBtn.addEventListener('click', function() {{
      var collapsed = portfolioSectionWrap.style.display === 'none';
      portfolioSectionWrap.style.display = collapsed ? '' : 'none';
      portfolioToggleBtn.textContent = collapsed ? 'Collapse' : 'Expand';
    }});
  }}

  var portfolioExportBtn = document.getElementById('portfolioExport');
  if (portfolioExportBtn) {{
    portfolioExportBtn.addEventListener('click', function() {{
      var blob = new Blob([JSON.stringify(portfolio, null, 2)], {{type: 'application/json'}});
      var url = URL.createObjectURL(blob);
      var a = document.createElement('a');
      a.href = url;
      a.download = 'csp_portfolio_' + new Date().toISOString().slice(0, 10) + '.json';
      document.body.appendChild(a);
      a.click();
      document.body.removeChild(a);
      URL.revokeObjectURL(url);
    }});
  }}
  var portfolioImportBtn = document.getElementById('portfolioImportBtn');
  var portfolioImportFile = document.getElementById('portfolioImportFile');
  if (portfolioImportBtn && portfolioImportFile) {{
    portfolioImportBtn.addEventListener('click', function() {{ portfolioImportFile.click(); }});
    portfolioImportFile.addEventListener('change', function() {{
      var file = portfolioImportFile.files[0];
      if (!file) return;
      var reader = new FileReader();
      reader.onload = function() {{
        try {{
          var imported = JSON.parse(reader.result);
          if (imported && typeof imported === 'object') {{
            Object.keys(imported).forEach(function(k) {{ portfolio[k] = imported[k]; }});
            savePortfolio();
            document.querySelectorAll('.portfolio-check').forEach(function(cb) {{
              cb.checked = !!portfolio[cb.getAttribute('data-key')];
            }});
            renderPortfolio();
            alert('Portfolio imported (' + Object.keys(imported).length + ' entries merged in).');
          }}
        }} catch (e) {{
          alert('Could not read that file as portfolio JSON: ' + e.message);
        }}
      }};
      reader.readAsText(file);
      portfolioImportFile.value = '';
    }});
  }}

  renderPortfolio();

  var btn = document.getElementById('applyFilter');
  if (btn) btn.addEventListener('click', applyFilter);
  ['minRoi', 'maxRoi', 'minPe', 'maxPe', 'minDte', 'maxDte', 'baseInvest', 'minPutStrike', 'maxPutStrike'].forEach(function(id) {{
    var el = document.getElementById(id);
    if (el) el.addEventListener('keydown', function(e) {{ if (e.key === 'Enter') applyFilter(); }});
  }});

  var EXPIRY_STATES = ['monthly', 'weekly', 'both'];
  var EXPIRY_LABELS = {{ monthly: 'Expirations: Monthly only', weekly: 'Expirations: Weekly only', both: 'Expirations: Both' }};
  function setExpiryState(state) {{
    var elBtn = document.getElementById('expiryToggle');
    if (!elBtn) return;
    if (EXPIRY_STATES.indexOf(state) === -1) state = 'monthly';
    elBtn.dataset.state = state;
    elBtn.textContent = EXPIRY_LABELS[state];
  }}
  var expiryBtn = document.getElementById('expiryToggle');
  if (expiryBtn) {{
    expiryBtn.addEventListener('click', function() {{
      var idx = EXPIRY_STATES.indexOf(expiryBtn.dataset.state || 'monthly');
      setExpiryState(EXPIRY_STATES[(idx + 1) % EXPIRY_STATES.length]);
      applyFilter();
    }});
  }}

  // Every page open starts from discord_filter_config.json's values (no
  // localStorage override) - edit that file to change what a fresh load shows.
  var fieldToCfgKey = {{
    minRoi: 'min_roi', maxRoi: 'max_roi',
    minPe: 'min_pe', maxPe: 'max_pe',
    minDte: 'min_dte_entry', maxDte: 'max_dte_entry',
    baseInvest: 'base_investment',
    minPutStrike: 'min_put_strike', maxPutStrike: 'max_put_strike'
  }};
  Object.keys(fieldToCfgKey).forEach(function(id) {{
    var cfgVal = DEFAULT_FILTERS[fieldToCfgKey[id]];
    if (cfgVal !== null && cfgVal !== undefined) document.getElementById(id).value = cfgVal;
  }});
  setExpiryState(DEFAULT_FILTERS.expiry_filter || 'monthly');
  applyFilter();

  var tabBtnCsp = document.getElementById('tabBtnCsp');
  var tabBtnBearCall = document.getElementById('tabBtnBearCall');
  var cspTab = document.getElementById('cspTabContent');
  var bearCallTab = document.getElementById('bearCallTabContent');
  function showTab(which) {{
    var csp = which === 'csp';
    if (cspTab) cspTab.style.display = csp ? '' : 'none';
    if (bearCallTab) bearCallTab.style.display = csp ? 'none' : '';
    if (tabBtnCsp) tabBtnCsp.className = 'tabbtn' + (csp ? ' tabbtn-active' : '');
    if (tabBtnBearCall) tabBtnBearCall.className = 'tabbtn' + (csp ? '' : ' tabbtn-active');
  }}
  if (tabBtnCsp) tabBtnCsp.addEventListener('click', function() {{ showTab('csp'); }});
  if (tabBtnBearCall) tabBtnBearCall.addEventListener('click', function() {{ showTab('bearcall'); }});

  function applyBearCallFilter() {{
    var minCreditRaw = document.getElementById('bcMinCreditPct').value.trim();
    var maxCollateralRaw = document.getElementById('bcMaxCollateral').value.trim();
    var minPeRaw = document.getElementById('bcMinPe').value.trim();
    var noBcFilter = minCreditRaw === '' && maxCollateralRaw === '' && minPeRaw === '';
    var minCredit = minCreditRaw === '' ? -Infinity : parseFloat(minCreditRaw);
    var maxCollateral = maxCollateralRaw === '' ? Infinity : parseFloat(maxCollateralRaw);
    var minPe = minPeRaw === '' ? -Infinity : parseFloat(minPeRaw);

    var allCards = document.querySelectorAll('#bearCallTabContent .card');
    var openVisible = [], closedVisible = [];
    var totalCount = 0;
    allCards.forEach(function(card) {{
      totalCount++;
      var isOpen = card.getAttribute('data-kind') === 'open';
      var creditVal = parseFloat(card.getAttribute('data-credit-pct'));
      var collateralVal = parseFloat(card.getAttribute('data-collateral'));
      var peRaw = card.getAttribute('data-pe');
      // Missing PE ("n/a" on the card) means undefined, not zero - treat as
      // infinite so it still passes a min-only filter, same convention as
      // the CSP tab's own PE filter.
      var peVal = peRaw === '' ? Infinity : parseFloat(peRaw);
      var ok = noBcFilter || (creditVal >= minCredit && collateralVal <= maxCollateral && peVal >= minPe);
      card.style.display = ok ? '' : 'none';
      if (ok) {{ (isOpen ? openVisible : closedVisible).push(card); }}
    }});

    var countEl = document.getElementById('bcFilterCount');
    if (countEl) countEl.textContent = (openVisible.length + closedVisible.length) + ' of ' + totalCount + ' shown';
    var noteEl = document.getElementById('bcFilterNote');
    if (noteEl) noteEl.style.display = noBcFilter ? 'none' : '';

    var bcOpenCountEl = document.getElementById('bcOpenCount');
    if (bcOpenCountEl) bcOpenCountEl.textContent = openVisible.length;
    var bcOpenSectionCountEl = document.getElementById('bcOpenSectionCount');
    if (bcOpenSectionCountEl) bcOpenSectionCountEl.textContent = openVisible.length;
    var bcRealizedCountEl = document.getElementById('bcRealizedCount');
    if (bcRealizedCountEl) bcRealizedCountEl.textContent = closedVisible.length;
    var bcClosedSectionCountEl = document.getElementById('bcClosedSectionCount');
    if (bcClosedSectionCountEl) bcClosedSectionCountEl.textContent = closedVisible.length;

    setMoney('bcTotalFict', 'bcTotalFictAmt', sumAttr(openVisible, 'data-norm-fict'));
    setPct('bcAvgFictRoi', avgAttr(openVisible, 'data-roi-fict'));
    setPct('bcAvgFictAnn', avgAttr(openVisible, 'data-ann-fict'));
    setMoney('bcTotalActual', 'bcTotalActualAmt', sumAttr(openVisible, 'data-norm-actual'));
    setPct('bcAvgActualRoi', avgAttr(openVisible, 'data-roi-actual'));
    setPct('bcAvgActualAnn', avgAttr(openVisible, 'data-ann-actual'));
    setMoney('bcTotalRealized', 'bcTotalRealizedAmt', sumAttr(closedVisible, 'data-norm-realized'));
    setPct('bcAvgRealizedRoi', avgAttr(closedVisible, 'data-roi-realized'));
    setPct('bcAvgRealizedAnn', avgAttr(closedVisible, 'data-ann-realized'));

    function countStockDown(cards) {{
      var n = 0;
      cards.forEach(function(card) {{
        var v = parseFloat(card.getAttribute('data-stock-pct'));
        if (!isNaN(v) && v < 0) n++;
      }});
      return n;
    }}
    var bcStockDownOpenEl = document.getElementById('bcStockDownOpen');
    if (bcStockDownOpenEl) bcStockDownOpenEl.textContent = countStockDown(openVisible) + ' of ' + openVisible.length + ' open';
    var bcStockDownClosedEl = document.getElementById('bcStockDownClosed');
    if (bcStockDownClosedEl) bcStockDownClosedEl.textContent = countStockDown(closedVisible) + ' of ' + closedVisible.length + ' closed';
  }}
  var bcBtn = document.getElementById('bcApplyFilter');
  if (bcBtn) bcBtn.addEventListener('click', applyBearCallFilter);
  ['bcMinCreditPct', 'bcMaxCollateral', 'bcMinPe'].forEach(function(id) {{
    var el = document.getElementById(id);
    if (el) el.addEventListener('keydown', function(e) {{ if (e.key === 'Enter') applyBearCallFilter(); }});
  }});
  var bcFieldToCfgKey = {{ bcMinCreditPct: 'min_credit_pct', bcMaxCollateral: 'max_collateral', bcMinPe: 'min_pe' }};
  Object.keys(bcFieldToCfgKey).forEach(function(id) {{
    var cfgVal = DEFAULT_BEAR_CALL_FILTERS[bcFieldToCfgKey[id]];
    if (cfgVal !== null && cfgVal !== undefined) document.getElementById(id).value = cfgVal;
  }});
  applyBearCallFilter();

  var bcClosedToggleBtn = document.getElementById('bcClosedToggle');
  var bcClosedWrap = document.getElementById('bcClosedCardsWrap');
  if (bcClosedToggleBtn && bcClosedWrap) {{
    bcClosedToggleBtn.addEventListener('click', function() {{
      var collapsed = bcClosedWrap.style.display === 'none';
      bcClosedWrap.style.display = collapsed ? '' : 'none';
      bcClosedToggleBtn.textContent = collapsed ? 'Collapse' : 'Expand';
    }});
  }}

  // Live "what if" fill-quality slider for OPEN bear call spreads' "actual"
  // (live-requote) P&L - 0 = pessimistic (cross the full bid-ask spread on
  // both legs, the same assumption entry credit uses by default), 100 =
  // optimistic, 50 = mid for both legs. Recomputes from each card's own raw
  // current bid/ask (already fetched server-side) - no new network calls,
  // purely a client-side "what if" exploration. Entry credit and closed/
  // realized P&L are NOT affected - only this unrealized figure.
  function bcCreditLegFill(bid, ask, pct) {{ return bid + (pct / 100) * (ask - bid); }}
  function bcDebitLegFill(bid, ask, pct) {{ return ask - (pct / 100) * (ask - bid); }}
  function recomputeBearCallActual(pct) {{
    document.querySelectorAll('#bcOpenCards .card').forEach(function(card) {{
      var netCredit = readAttr(card, 'data-net-credit');
      var collateral = readAttr(card, 'data-collateral');
      var shortBid = readAttr(card, 'data-cur-short-bid');
      var shortAsk = readAttr(card, 'data-cur-short-ask');
      var longBid = readAttr(card, 'data-cur-long-bid');
      var longAsk = readAttr(card, 'data-cur-long-ask');
      var daysHeld = readAttr(card, 'data-days-held');
      var pnl = null;
      if (netCredit !== null && shortBid !== null && shortAsk !== null && longBid !== null && longAsk !== null) {{
        var closeShortCost = bcDebitLegFill(shortBid, shortAsk, pct);
        var closeLongProceeds = bcCreditLegFill(longBid, longAsk, pct);
        pnl = Math.round((netCredit - (closeShortCost - closeLongProceeds)) * 100 * 100) / 100;
      }}
      var norm = (pnl !== null && collateral > 0) ? Math.round(pnl * ({NORMALIZED_RISK_USD:.0f} / collateral) * 100) / 100 : null;
      var roi = (pnl !== null && collateral > 0) ? Math.round(pnl / collateral * 100 * 100) / 100 : null;
      var ann = (roi !== null && daysHeld && daysHeld > 0) ? Math.round(roi * (365 / daysHeld) * 100) / 100 : null;
      card.setAttribute('data-norm-actual', norm === null ? '' : norm);
      card.setAttribute('data-roi-actual', roi === null ? '' : roi);
      card.setAttribute('data-ann-actual', ann === null ? '' : ann);
      var amtEl = card.querySelector('.bc-actual-amt');
      if (amtEl) amtEl.textContent = fmtMoney(norm);
      var roiEl = card.querySelector('.bc-actual-roi');
      if (roiEl) roiEl.textContent = fmtPct(roi);
      var annEl = card.querySelector('.bc-actual-ann');
      if (annEl) annEl.textContent = fmtPct(ann);
      var lineEl = card.querySelector('.bc-actual-line');
      if (lineEl) {{
        var keep = lineEl.className.split(' ').filter(function(c) {{ return c !== 'pos' && c !== 'neg' && c !== ''; }});
        var cls = pnlClass(norm);
        if (cls) keep.push(cls);
        lineEl.className = keep.join(' ');
      }}
    }});
    applyBearCallFilter();
  }}
  var bcFillPctEl = document.getElementById('bcFillPct');
  var bcFillPctLabelEl = document.getElementById('bcFillPctLabel');
  if (bcFillPctEl) {{
    bcFillPctEl.addEventListener('input', function() {{
      var pct = parseFloat(bcFillPctEl.value);
      if (bcFillPctLabelEl) bcFillPctLabelEl.textContent = pct;
      recomputeBearCallActual(pct);
    }});
  }}
}})();
</script>
</body>
</html>
"""
    SUMMARY_HTML.write_text(html, encoding="utf-8")
    return SUMMARY_HTML


def build_bear_call_summary(positions, today, fill_pct=0):
    """Same two-pass approach as build_summary (open positions marked to
    market two ways, closed positions locked at settlement) but for a
    single-valued credit spread instead of CSP's seller/buyer duality on one
    contract - there's no "other side" being tracked here, just the one
    strategy as actually entered.

    fill_pct (0=pessimistic/cross the spread, 100=optimistic, 50=mid) only
    affects the "actual" (live requote) unrealized P&L here - it does NOT
    change ENTRY pricing for already-tracked positions (that's locked in
    at add time using whatever fill_pct was configured then) and doesn't
    apply to closed positions at all (settlement is pure intrinsic value,
    no bid/ask involved)."""
    open_rows = []
    for p in positions:
        if p.get("settled"):
            continue
        exp_date = datetime.strptime(p["expiration"], "%Y-%m-%d").date()
        if exp_date < today:
            continue  # expired but not yet settled (price data lag)
        added_date_obj = datetime.strptime(p["added_date"], "%Y-%m-%d").date()
        days_held = (today - added_date_obj).days
        dte_at_entry = (exp_date - added_date_obj).days
        current_px = get_current_stock_price(p["symbol"])

        fict_pnl = fict_norm = fict_roi = fict_ann_roi = None
        if current_px is not None:
            fict_pnl = calc_bear_call_pnl_at_price(p["short_strike"], p["long_strike"], p["net_credit"], current_px)
            fict_norm = round(fict_pnl * (NORMALIZED_RISK_USD / p["collateral"]), 2) if p["collateral"] > 0 else None
            fict_roi = calc_roi_pct(fict_pnl, p["collateral"])
            fict_ann_roi = annualize_roi_pct(fict_roi, days_held)

        current_short_bid, current_short_ask = get_yahoo_call_quote(p["symbol"], p["expiration"], p["short_strike"])
        current_long_bid, current_long_ask = get_yahoo_call_quote(p["symbol"], p["expiration"], p["long_strike"])
        actual_pnl = calc_bear_call_actual_close_pnl(
            p["net_credit"], current_short_bid, current_short_ask, current_long_bid, current_long_ask, fill_pct)
        actual_is_approx = actual_pnl is None and fict_pnl is not None
        if actual_is_approx:
            actual_pnl = fict_pnl
        actual_norm = round(actual_pnl * (NORMALIZED_RISK_USD / p["collateral"]), 2) if actual_pnl is not None and p["collateral"] > 0 else None
        actual_roi = calc_roi_pct(actual_pnl, p["collateral"])
        actual_ann_roi = annualize_roi_pct(actual_roi, days_held)

        stock_pnl, stock_pct_change = calc_stock_equivalent(p["entry_stock_px"], current_px)
        stock_pct_change_ann = annualize_roi_pct(stock_pct_change, days_held)

        open_rows.append({
            "SYMBOL": p["symbol"],
            "SHORT STRIKE": p["short_strike"],
            "LONG STRIKE": p["long_strike"],
            "EXPIRATION": p["expiration"],
            "DAYS LEFT": (exp_date - today).days,
            "DAYS HELD": days_held,
            "DTE AT ENTRY": dte_at_entry,
            "RUN LABEL": p.get("run_label"),
            "ENTRY STOCK PRICE": p["entry_stock_px"],
            "CURRENT STOCK PRICE": current_px,
            "STOCK PCT CHANGE": stock_pct_change,
            "STOCK PCT CHANGE ANN": stock_pct_change_ann,
            "PE AT ENTRY": p.get("pe_at_entry"),
            "SHORT BID (entry)": p["short_bid"],
            "LONG ASK (entry)": p["long_ask"],
            "NET CREDIT (entry)": p["net_credit"],
            "WIDTH": p["width"],
            "COLLATERAL": p["collateral"],
            "CREDIT % OF WIDTH (entry)": round(p["net_credit"] / p["width"] * 100, 2) if p["width"] else None,
            "CURRENT SHORT BID": current_short_bid,
            "CURRENT SHORT ASK": current_short_ask,
            "CURRENT LONG BID": current_long_bid,
            "CURRENT LONG ASK": current_long_ask,
            "ACTUAL IS APPROX": actual_is_approx,
            "UNREALIZED P/L (FICTIONAL)": fict_pnl,
            f"NORM P/L (FICTIONAL) (${NORMALIZED_RISK_USD:.0f} risk)": fict_norm,
            "ROI % (FICTIONAL)": fict_roi,
            "ANNUALIZED ROI % (FICTIONAL)": fict_ann_roi,
            "UNREALIZED P/L (ACTUAL)": actual_pnl,
            f"NORM P/L (ACTUAL) (${NORMALIZED_RISK_USD:.0f} risk)": actual_norm,
            "ROI % (ACTUAL)": actual_roi,
            "ANNUALIZED ROI % (ACTUAL)": actual_ann_roi,
            "ADDED": p["added_date"],
        })

    settled = [p for p in positions if p.get("settled")]
    closed_rows = []
    cum_pnl = 0.0
    for i, p in enumerate(settled, start=1):
        pnl = p["settled_pnl"]
        norm = round(pnl * (NORMALIZED_RISK_USD / p["collateral"]), 2) if p["collateral"] > 0 else None
        cum_pnl = round(cum_pnl + (norm or 0), 2)
        roi = calc_roi_pct(pnl, p["collateral"])
        holding_days = (datetime.strptime(p["expiration"], "%Y-%m-%d").date()
                        - datetime.strptime(p["added_date"], "%Y-%m-%d").date()).days
        ann_roi = annualize_roi_pct(roi, holding_days)
        cum_roi = round(cum_pnl / (i * NORMALIZED_RISK_USD) * 100, 2)

        stock_pnl, stock_pct_change = calc_stock_equivalent(p["entry_stock_px"], p["final_stock_px"])
        stock_pct_change_ann = annualize_roi_pct(stock_pct_change, holding_days)

        closed_rows.append({
            "SYMBOL": p["symbol"],
            "SHORT STRIKE": p["short_strike"],
            "LONG STRIKE": p["long_strike"],
            "EXPIRATION": p["expiration"],
            "DTE AT ENTRY": holding_days,
            "ENTRY STOCK PRICE": p["entry_stock_px"],
            "FINAL STOCK PRICE": p["final_stock_px"],
            "STOCK PCT CHANGE": stock_pct_change,
            "STOCK PCT CHANGE ANN": stock_pct_change_ann,
            "PE AT ENTRY": p.get("pe_at_entry"),
            "NET CREDIT (entry)": p["net_credit"],
            "WIDTH": p["width"],
            "COLLATERAL": p["collateral"],
            "CREDIT % OF WIDTH (entry)": round(p["net_credit"] / p["width"] * 100, 2) if p["width"] else None,
            "REALIZED P/L": pnl,
            f"NORM P/L (${NORMALIZED_RISK_USD:.0f} risk)": norm,
            "ROI %": roi,
            "ANNUALIZED ROI %": ann_roi,
            "CUMULATIVE P/L": cum_pnl,
            "CUMULATIVE ROI %": cum_roi,
            "ADDED": p["added_date"],
            "SETTLED AT": p["settled_at"],
        })

    def avg(vals):
        vals = [v for v in vals if v is not None]
        return round(sum(vals) / len(vals), 2) if vals else None

    fict_norm_col = f"NORM P/L (FICTIONAL) (${NORMALIZED_RISK_USD:.0f} risk)"
    actual_norm_col = f"NORM P/L (ACTUAL) (${NORMALIZED_RISK_USD:.0f} risk)"
    realized_norm_col = f"NORM P/L (${NORMALIZED_RISK_USD:.0f} risk)"

    totals = {
        "unrealized_fict_total": round(sum(r[fict_norm_col] or 0 for r in open_rows), 2),
        "unrealized_actual_total": round(sum(r[actual_norm_col] or 0 for r in open_rows), 2),
        "avg_unrealized_fict_roi": avg(r["ROI % (FICTIONAL)"] for r in open_rows),
        "avg_unrealized_actual_roi": avg(r["ROI % (ACTUAL)"] for r in open_rows),
        "avg_unrealized_fict_ann_roi": avg(r["ANNUALIZED ROI % (FICTIONAL)"] for r in open_rows),
        "avg_unrealized_actual_ann_roi": avg(r["ANNUALIZED ROI % (ACTUAL)"] for r in open_rows),
        "realized_total": round(sum(r[realized_norm_col] or 0 for r in closed_rows), 2),
        "avg_realized_roi": avg(r["ROI %"] for r in closed_rows),
        "avg_realized_ann_roi": avg(r["ANNUALIZED ROI %"] for r in closed_rows),
        "settled_count": len(settled),
        "avg_stock_unrealized_pct": avg(r["STOCK PCT CHANGE"] for r in open_rows),
        "avg_stock_realized_pct": avg(r["STOCK PCT CHANGE"] for r in closed_rows),
        "stock_down_open": sum(1 for r in open_rows if r["STOCK PCT CHANGE"] is not None and r["STOCK PCT CHANGE"] < 0),
        "stock_down_closed": sum(1 for r in closed_rows if r["STOCK PCT CHANGE"] is not None and r["STOCK PCT CHANGE"] < 0),
    }
    return open_rows, closed_rows, totals


def build_summary(positions, today, filter_cfg=None, run_log=None, bear_call_data=None):
    open_rows = []
    open_roi_fict = []    # (seller_roi, buyer_roi, ann_seller_roi, ann_buyer_roi) per open position
    open_roi_actual = []  # same, for the "actual" (live requote) side
    open_norm_mid = []    # (norm_seller_mid, norm_buyer_mid) per open position
    for p in positions:
        if p.get("settled"):
            continue  # already in closed_rows below - same-day settlement
            # (now possible via settle_expired_positions' same_day_ok) means
            # exp_date < today alone isn't enough to exclude it here, since
            # a position settled TODAY has exp_date == today, not < today.
        exp_date = datetime.strptime(p["expiration"], "%Y-%m-%d").date()
        if exp_date < today:
            continue  # expired but not yet settled (e.g. price data lag) - stays out of both lists until it settles
        added_date_obj = datetime.strptime(p["added_date"], "%Y-%m-%d").date()
        days_held = (today - added_date_obj).days
        dte_at_entry = (exp_date - added_date_obj).days
        current_px = get_current_stock_price(p["symbol"])

        # "Fictional": intrinsic value at today's stock price only - ignores
        # time value, so it's what settlement would be if expiring right now.
        fict_seller_pnl = fict_buyer_pnl = None
        fict_norm_seller = fict_norm_buyer = None
        fict_seller_roi = fict_buyer_roi = fict_ann_seller_roi = fict_ann_buyer_roi = None
        if current_px is not None:
            fict_seller_pnl, fict_buyer_pnl = calc_pnl_at_price(p["strike"], p["bid"], p["ask"], current_px)
            fict_norm_seller, fict_norm_buyer = normalize_pnl(fict_seller_pnl, fict_buyer_pnl, p["strike"], p["ask"])
            fict_seller_roi = calc_roi_pct(fict_seller_pnl, p["strike"] * 100)
            fict_buyer_roi = calc_roi_pct(fict_buyer_pnl, p["ask"] * 100)
            fict_ann_seller_roi = annualize_roi_pct(fict_seller_roi, days_held)
            fict_ann_buyer_roi = annualize_roi_pct(fict_buyer_roi, days_held)
        open_roi_fict.append((fict_seller_roi, fict_buyer_roi, fict_ann_seller_roi, fict_ann_buyer_roi))

        # "Actual": what closing the position today would really cost/pay,
        # crossing the spread - a fresh live option-chain requote, not just
        # the stock price.
        current_bid, current_ask = get_yahoo_quote(p["symbol"], p["expiration"], p["strike"])
        actual_seller_pnl, actual_buyer_pnl = calc_actual_close_pnl(p["bid"], p["ask"], current_bid, current_ask)
        # If no live quote exists at all (common once a contract is deep OTM
        # and essentially untraded - e.g. the underlying rallied far past the
        # strike), falling back to None understates the real picture: a
        # worthless-in-practice option IS close to a total loss for the
        # long side (and close to max profit for the short side), not an
        # unknown/neutral zero. Fall back to the intrinsic-value ("fictional")
        # estimate in that case - flagged, same spirit as the bid/ask
        # approximation fallbacks used elsewhere in this script.
        actual_seller_is_approx = actual_seller_pnl is None and fict_seller_pnl is not None
        actual_buyer_is_approx = actual_buyer_pnl is None and fict_buyer_pnl is not None
        if actual_seller_is_approx:
            actual_seller_pnl = fict_seller_pnl
        if actual_buyer_is_approx:
            actual_buyer_pnl = fict_buyer_pnl
        actual_norm_seller, actual_norm_buyer = normalize_pnl(actual_seller_pnl, actual_buyer_pnl, p["strike"], p["ask"])
        actual_seller_roi = calc_roi_pct(actual_seller_pnl, p["strike"] * 100)
        actual_buyer_roi = calc_roi_pct(actual_buyer_pnl, p["ask"] * 100)
        actual_ann_seller_roi = annualize_roi_pct(actual_seller_roi, days_held)
        actual_ann_buyer_roi = annualize_roi_pct(actual_buyer_roi, days_held)
        open_roi_actual.append((actual_seller_roi, actual_buyer_roi, actual_ann_seller_roi, actual_ann_buyer_roi))

        # "Mid": same live quote as "actual," but priced at the mid rather
        # than crossing the spread - a less pessimistic reference figure,
        # shown only as a parenthetical alongside the "actual" totals.
        #
        # LONG/buyer side exception: once buying shares and exercising the
        # put is profitable on pure intrinsic value alone, that's a
        # guaranteed floor worth comparing against the realistic exit of
        # just selling the put at its current bid (actual_buyer_pnl) -
        # remaining time value sometimes makes selling the better of the
        # two, so take whichever is actually higher rather than always
        # preferring exercise. Only relabel "exe" (vs. the generic "mid")
        # when exercise genuinely wins that comparison.
        mid_seller_pnl, mid_buyer_pnl = calc_mid_close_pnl(p["bid"], p["ask"], current_bid, current_ask)
        mid_norm_seller, mid_norm_buyer = normalize_pnl(mid_seller_pnl, mid_buyer_pnl, p["strike"], p["ask"])
        buyer_mid_is_exercise = (fict_buyer_pnl is not None and actual_buyer_pnl is not None
                                  and fict_buyer_pnl > 0 and fict_buyer_pnl > actual_buyer_pnl)
        if buyer_mid_is_exercise:
            mid_buyer_pnl = fict_buyer_pnl
            mid_norm_buyer = fict_norm_buyer
        # Same no-live-quote situation as "actual" above - mid needs BOTH
        # current_bid and current_ask, so it can go missing even on a leg
        # whose "actual" side didn't (e.g. only the ask is quoted). Fall
        # back to intrinsic value here too so the mid parenthetical doesn't
        # silently read as a contradictory $0 next to a real loss/gain.
        mid_seller_is_approx = mid_seller_pnl is None and fict_seller_pnl is not None
        mid_buyer_is_approx = (not buyer_mid_is_exercise) and mid_buyer_pnl is None and fict_buyer_pnl is not None
        if mid_seller_is_approx:
            mid_seller_pnl = fict_seller_pnl
            mid_norm_seller = fict_norm_seller
        if mid_buyer_is_approx:
            mid_buyer_pnl = fict_buyer_pnl
            mid_norm_buyer = fict_norm_buyer
        open_norm_mid.append((mid_norm_seller, mid_norm_buyer))

        # Pure stock benchmark, no options: what if you'd just bought (or
        # shorted) NORMALIZED_RISK_USD of shares at entry instead? Short is
        # always the exact negative of long.
        stock_long_pnl, stock_pct_change = calc_stock_equivalent(p["entry_stock_px"], current_px)
        stock_pct_change_ann = annualize_roi_pct(stock_pct_change, days_held)

        open_rows.append({
            "SYMBOL": p["symbol"],
            "STRIKE": p["strike"],
            "EXPIRATION": p["expiration"],
            "DAYS LEFT": (exp_date - today).days,
            "DTE AT ENTRY": dte_at_entry,
            "RUN LABEL": p.get("run_label"),
            "EXPIRY TYPE": p.get("expiry_type", "monthly"),
            "ENTRY STOCK PRICE": p["entry_stock_px"],
            "CURRENT STOCK PRICE": current_px,
            "STOCK LONG P/L": stock_long_pnl,
            "STOCK SHORT P/L": None if stock_long_pnl is None else -stock_long_pnl,
            "STOCK PCT CHANGE": stock_pct_change,
            "STOCK PCT CHANGE ANN": stock_pct_change_ann,
            "ACTUAL SELLER IS APPROX": actual_seller_is_approx,
            "ACTUAL BUYER IS APPROX": actual_buyer_is_approx,
            "MID SELLER IS APPROX": mid_seller_is_approx,
            "MID BUYER IS APPROX": mid_buyer_is_approx,
            "BARCHART BID (reference)": p["barchart_bid"],
            "BARCHART RETURN % (at selection)": p.get("potential_return_pct"),
            "BARCHART ANNUALIZED RETURN % (at selection)": p.get("potential_return_annual_pct"),
            "PE AT ENTRY": p.get("pe_at_entry"),
            "PE SOURCE": "approx (backfilled)" if p.get("pe_at_entry_is_approx") else "yahoo",
            "BID": p["bid"],
            "BID SOURCE": "approx (barchart)" if p["bid_is_approx"] else "yahoo",
            "ASK": p["ask"],
            "ASK SOURCE": "approx (bid x 1.2)" if p["ask_is_approx"] else "yahoo",
            "CURRENT OPTION BID": current_bid,
            "CURRENT OPTION ASK": current_ask,
            "UNREALIZED P/L (FICTIONAL) IF SOLD (CSP)": fict_seller_pnl,
            "UNREALIZED P/L (FICTIONAL) IF BOUGHT (long put)": fict_buyer_pnl,
            f"NORM P/L (FICTIONAL) IF SOLD (${NORMALIZED_RISK_USD:.0f} risk)": fict_norm_seller,
            f"NORM P/L (FICTIONAL) IF BOUGHT (${NORMALIZED_RISK_USD:.0f} risk)": fict_norm_buyer,
            "ROI % (FICTIONAL) IF SOLD (CSP)": fict_seller_roi,
            "ROI % (FICTIONAL) IF BOUGHT (long put)": fict_buyer_roi,
            "ANNUALIZED ROI % (FICTIONAL) IF SOLD (CSP)": fict_ann_seller_roi,
            "ANNUALIZED ROI % (FICTIONAL) IF BOUGHT (long put)": fict_ann_buyer_roi,
            "UNREALIZED P/L (ACTUAL) IF SOLD (CSP)": actual_seller_pnl,
            "UNREALIZED P/L (ACTUAL) IF BOUGHT (long put)": actual_buyer_pnl,
            f"NORM P/L (ACTUAL) IF SOLD (${NORMALIZED_RISK_USD:.0f} risk)": actual_norm_seller,
            f"NORM P/L (ACTUAL) IF BOUGHT (${NORMALIZED_RISK_USD:.0f} risk)": actual_norm_buyer,
            "ROI % (ACTUAL) IF SOLD (CSP)": actual_seller_roi,
            "ROI % (ACTUAL) IF BOUGHT (long put)": actual_buyer_roi,
            "ANNUALIZED ROI % (ACTUAL) IF SOLD (CSP)": actual_ann_seller_roi,
            "ANNUALIZED ROI % (ACTUAL) IF BOUGHT (long put)": actual_ann_buyer_roi,
            "UNREALIZED P/L (MID) IF SOLD (CSP)": mid_seller_pnl,
            "UNREALIZED P/L (MID) IF BOUGHT (long put)": mid_buyer_pnl,
            f"NORM P/L (MID) IF SOLD (${NORMALIZED_RISK_USD:.0f} risk)": mid_norm_seller,
            f"NORM P/L (MID) IF BOUGHT (${NORMALIZED_RISK_USD:.0f} risk)": mid_norm_buyer,
            "BUYER MID IS EXERCISE": buyer_mid_is_exercise,
            "ADDED": p["added_date"],
        })

    # ---- closed (settled) positions, chronological by expiration - the
    # natural order for a "P&L over time" cumulative track record ----
    settled = sorted((p for p in positions if p.get("settled")), key=lambda p: p["expiration"])
    closed_rows = []
    cum_seller = 0.0
    cum_buyer = 0.0
    for i, p in enumerate(settled, start=1):
        seller_pnl, buyer_pnl = p["settled_seller_pnl"], p["settled_buyer_pnl"]
        norm_seller, norm_buyer = normalize_pnl(seller_pnl, buyer_pnl, p["strike"], p["ask"])
        cum_seller = round(cum_seller + (norm_seller or 0), 2)
        cum_buyer = round(cum_buyer + (norm_buyer or 0), 2)
        seller_roi = calc_roi_pct(seller_pnl, p["strike"] * 100)
        buyer_roi = calc_roi_pct(buyer_pnl, p["ask"] * 100)
        holding_days = (datetime.strptime(p["expiration"], "%Y-%m-%d").date()
                         - datetime.strptime(p["added_date"], "%Y-%m-%d").date()).days
        ann_seller_roi = annualize_roi_pct(seller_roi, holding_days)
        ann_buyer_roi = annualize_roi_pct(buyer_roi, holding_days)
        # Cumulative ROI: cumulative normalized $ return vs. cumulative
        # capital deployed, assuming NORMALIZED_RISK_USD was risked on each
        # closed trade to date - a running "portfolio ROI so far."
        cum_seller_roi = round(cum_seller / (i * NORMALIZED_RISK_USD) * 100, 2)
        cum_buyer_roi = round(cum_buyer / (i * NORMALIZED_RISK_USD) * 100, 2)

        stock_long_pnl, stock_pct_change = calc_stock_equivalent(p["entry_stock_px"], p["final_stock_px"])
        stock_pct_change_ann = annualize_roi_pct(stock_pct_change, holding_days)

        closed_rows.append({
            "SYMBOL": p["symbol"],
            "STRIKE": p["strike"],
            "EXPIRATION": p["expiration"],
            "DTE AT ENTRY": holding_days,
            "EXPIRY TYPE": p.get("expiry_type", "monthly"),
            "ENTRY STOCK PRICE": p["entry_stock_px"],
            "FINAL STOCK PRICE": p["final_stock_px"],
            "STOCK LONG P/L": stock_long_pnl,
            "STOCK SHORT P/L": None if stock_long_pnl is None else -stock_long_pnl,
            "STOCK PCT CHANGE": stock_pct_change,
            "STOCK PCT CHANGE ANN": stock_pct_change_ann,
            "BARCHART BID (reference)": p["barchart_bid"],
            "BARCHART RETURN % (at selection)": p.get("potential_return_pct"),
            "BARCHART ANNUALIZED RETURN % (at selection)": p.get("potential_return_annual_pct"),
            "PE AT ENTRY": p.get("pe_at_entry"),
            "PE SOURCE": "approx (backfilled)" if p.get("pe_at_entry_is_approx") else "yahoo",
            "BID": p["bid"],
            "BID SOURCE": "approx (barchart)" if p["bid_is_approx"] else "yahoo",
            "ASK": p["ask"],
            "ASK SOURCE": "approx (bid x 1.2)" if p["ask_is_approx"] else "yahoo",
            "REALIZED P/L IF SOLD (CSP)": seller_pnl,
            "REALIZED P/L IF BOUGHT (long put)": buyer_pnl,
            f"NORM P/L IF SOLD (${NORMALIZED_RISK_USD:.0f} risk)": norm_seller,
            f"NORM P/L IF BOUGHT (${NORMALIZED_RISK_USD:.0f} risk)": norm_buyer,
            "ROI % IF SOLD (CSP)": seller_roi,
            "ROI % IF BOUGHT (long put)": buyer_roi,
            "ANNUALIZED ROI % IF SOLD (CSP)": ann_seller_roi,
            "ANNUALIZED ROI % IF BOUGHT (long put)": ann_buyer_roi,
            "CUMULATIVE P/L IF SOLD": cum_seller,
            "CUMULATIVE P/L IF BOUGHT": cum_buyer,
            "CUMULATIVE ROI % IF SOLD": cum_seller_roi,
            "CUMULATIVE ROI % IF BOUGHT": cum_buyer_roi,
            "ADDED": p["added_date"],
            "SETTLED AT": p["settled_at"],
        })

    def avg(vals):
        vals = [v for v in vals if v is not None]
        return round(sum(vals) / len(vals), 2) if vals else None

    fict_norm_seller_col = f"NORM P/L (FICTIONAL) IF SOLD (${NORMALIZED_RISK_USD:.0f} risk)"
    fict_norm_buyer_col = f"NORM P/L (FICTIONAL) IF BOUGHT (${NORMALIZED_RISK_USD:.0f} risk)"
    actual_norm_seller_col = f"NORM P/L (ACTUAL) IF SOLD (${NORMALIZED_RISK_USD:.0f} risk)"
    actual_norm_buyer_col = f"NORM P/L (ACTUAL) IF BOUGHT (${NORMALIZED_RISK_USD:.0f} risk)"
    realized_norm_seller_col = f"NORM P/L IF SOLD (${NORMALIZED_RISK_USD:.0f} risk)"
    realized_norm_buyer_col = f"NORM P/L IF BOUGHT (${NORMALIZED_RISK_USD:.0f} risk)"

    unrealized_fict_seller_total = round(sum(r[fict_norm_seller_col] or 0 for r in open_rows), 2)
    unrealized_fict_buyer_total = round(sum(r[fict_norm_buyer_col] or 0 for r in open_rows), 2)
    unrealized_actual_seller_total = round(sum(r[actual_norm_seller_col] or 0 for r in open_rows), 2)
    unrealized_actual_buyer_total = round(sum(r[actual_norm_buyer_col] or 0 for r in open_rows), 2)
    unrealized_mid_seller_total = round(sum(m[0] or 0 for m in open_norm_mid), 2)
    unrealized_mid_buyer_total = round(sum(m[1] or 0 for m in open_norm_mid), 2)
    realized_seller_total = cum_seller  # last row's cumulative == grand total
    realized_buyer_total = cum_buyer

    avg_unrealized_fict_seller_roi = avg(r[0] for r in open_roi_fict)
    avg_unrealized_fict_buyer_roi = avg(r[1] for r in open_roi_fict)
    avg_unrealized_fict_seller_ann_roi = avg(r[2] for r in open_roi_fict)
    avg_unrealized_fict_buyer_ann_roi = avg(r[3] for r in open_roi_fict)
    avg_unrealized_actual_seller_roi = avg(r[0] for r in open_roi_actual)
    avg_unrealized_actual_buyer_roi = avg(r[1] for r in open_roi_actual)
    avg_unrealized_actual_seller_ann_roi = avg(r[2] for r in open_roi_actual)
    avg_unrealized_actual_buyer_ann_roi = avg(r[3] for r in open_roi_actual)
    avg_realized_seller_roi = avg(r["ROI % IF SOLD (CSP)"] for r in closed_rows)
    avg_realized_buyer_roi = avg(r["ROI % IF BOUGHT (long put)"] for r in closed_rows)
    avg_realized_seller_ann_roi = avg(r["ANNUALIZED ROI % IF SOLD (CSP)"] for r in closed_rows)
    avg_realized_buyer_ann_roi = avg(r["ANNUALIZED ROI % IF BOUGHT (long put)"] for r in closed_rows)

    # Pure stock benchmark totals - no options involved at all, just what
    # buying/shorting $NORMALIZED_RISK_USD of shares at entry would have done.
    stock_unrealized_long_total = round(sum(r["STOCK LONG P/L"] or 0 for r in open_rows), 2)
    stock_unrealized_short_total = round(sum(r["STOCK SHORT P/L"] or 0 for r in open_rows), 2)
    stock_realized_long_total = round(sum(r["STOCK LONG P/L"] or 0 for r in closed_rows), 2)
    stock_realized_short_total = round(sum(r["STOCK SHORT P/L"] or 0 for r in closed_rows), 2)
    avg_stock_unrealized_pct = avg(r["STOCK PCT CHANGE"] for r in open_rows)
    avg_stock_realized_pct = avg(r["STOCK PCT CHANGE"] for r in closed_rows)
    avg_stock_unrealized_ann_roi = avg(r["STOCK PCT CHANGE ANN"] for r in open_rows)
    avg_stock_realized_ann_roi = avg(r["STOCK PCT CHANGE ANN"] for r in closed_rows)

    # How many of these screened "crappy stock" picks actually dropped from
    # entry - a sanity check on the short-biased thesis itself (long puts/
    # bear call spreads both only profit if the stock stays flat or falls),
    # independent of the options P&L math above.
    stock_down_open = sum(1 for r in open_rows if r["STOCK PCT CHANGE"] is not None and r["STOCK PCT CHANGE"] < 0)
    stock_down_closed = sum(1 for r in closed_rows if r["STOCK PCT CHANGE"] is not None and r["STOCK PCT CHANGE"] < 0)

    if open_rows or closed_rows:
        blank = pd.DataFrame([{}])
        sections = []

        open_df = (pd.DataFrame(open_rows).sort_values("DAYS LEFT") if open_rows
                   else pd.DataFrame([{"SYMBOL": "(no open positions)"}]))
        sections.append(open_df)
        sections.append(blank)

        closed_df = (pd.DataFrame(closed_rows) if closed_rows
                     else pd.DataFrame([{"SYMBOL": "(no closed positions)"}]))
        sections.append(closed_df)
        sections.append(blank)

        sections.append(pd.DataFrame([{
            "SYMBOL": f"OPEN P/L - UNREALIZED, FICTIONAL (normalized to ${NORMALIZED_RISK_USD:.0f} risk each)",
            fict_norm_seller_col: unrealized_fict_seller_total,
            fict_norm_buyer_col: unrealized_fict_buyer_total,
            "ROI % (FICTIONAL) IF SOLD (CSP)": avg_unrealized_fict_seller_roi,
            "ROI % (FICTIONAL) IF BOUGHT (long put)": avg_unrealized_fict_buyer_roi,
            "ANNUALIZED ROI % (FICTIONAL) IF SOLD (CSP)": avg_unrealized_fict_seller_ann_roi,
            "ANNUALIZED ROI % (FICTIONAL) IF BOUGHT (long put)": avg_unrealized_fict_buyer_ann_roi,
        }]))
        sections.append(blank)

        sections.append(pd.DataFrame([{
            "SYMBOL": f"OPEN P/L - UNREALIZED, ACTUAL (normalized to ${NORMALIZED_RISK_USD:.0f} risk each)",
            actual_norm_seller_col: unrealized_actual_seller_total,
            actual_norm_buyer_col: unrealized_actual_buyer_total,
            "ROI % (ACTUAL) IF SOLD (CSP)": avg_unrealized_actual_seller_roi,
            "ROI % (ACTUAL) IF BOUGHT (long put)": avg_unrealized_actual_buyer_roi,
            "ANNUALIZED ROI % (ACTUAL) IF SOLD (CSP)": avg_unrealized_actual_seller_ann_roi,
            "ANNUALIZED ROI % (ACTUAL) IF BOUGHT (long put)": avg_unrealized_actual_buyer_ann_roi,
        }]))
        sections.append(blank)

        sections.append(pd.DataFrame([{
            "SYMBOL": f"CLOSED P/L - REALIZED, {len(closed_rows)} settled (normalized to ${NORMALIZED_RISK_USD:.0f} risk each)",
            realized_norm_seller_col: realized_seller_total,
            realized_norm_buyer_col: realized_buyer_total,
            "ROI % IF SOLD (CSP)": avg_realized_seller_roi,
            "ROI % IF BOUGHT (long put)": avg_realized_buyer_roi,
            "ANNUALIZED ROI % IF SOLD (CSP)": avg_realized_seller_ann_roi,
            "ANNUALIZED ROI % IF BOUGHT (long put)": avg_realized_buyer_ann_roi,
        }]))

        combined = pd.concat(sections, ignore_index=True)
        combined.to_csv(SUMMARY_CSV, index=False)

    # The chart only tracks closed positions that actually passed the active
    # filter config (same filter the webpage opens with / Discord notifies
    # on) - a position that was never "interesting" by that filter shouldn't
    # count toward the realized-performance track record shown here. Every
    # other closed-position stat (CSV, totals, cards) still covers ALL
    # closed positions - only this chart is narrowed.
    #
    # This has to replicate the webpage's OWN two-pass filter exactly (see
    # applyFilter()'s "Pass 2" in generate_html_summary), not just the raw
    # per-position check: once any filter dimension is active, only the
    # earliest-added instance per symbol PER OPEN/CLOSED BUCKET counts as
    # "the trade you'd have taken" - a symbol can legitimately appear once
    # in open (its current position) and once in closed (an earlier,
    # already-settled trade on the same stock), since those are two
    # genuinely different, sequential trades. Skipping this second pass
    # would let a since-re-qualified symbol's LATER settlement double up
    # in the chart even though the webpage only ever shows one closed card
    # per symbol, making the chart's n= disagree with the page's own count.
    if filter_cfg is not None and any(v is not None for v in filter_cfg.values()):
        first_for_key = {}
        for p in positions:
            if not position_passes_filter_config(p, filter_cfg):
                continue
            key = (p["symbol"], bool(p.get("settled")))
            current = first_for_key.get(key)
            if current is None or p["added_date"] < current["added_date"]:
                first_for_key[key] = p
        selected_keys = {(p["symbol"], p["strike"], p["expiration"]) for p in first_for_key.values()}
        closed_rows_for_chart = [
            r for p, r in zip(settled, closed_rows)
            if (p["symbol"], p["strike"], p["expiration"]) in selected_keys
        ]
    else:
        closed_rows_for_chart = closed_rows
    png_path = plot_realized_pnl(closed_rows_for_chart)

    totals = {
        "unrealized_fict_seller_total": unrealized_fict_seller_total,
        "unrealized_fict_buyer_total": unrealized_fict_buyer_total,
        "unrealized_actual_seller_total": unrealized_actual_seller_total,
        "unrealized_actual_buyer_total": unrealized_actual_buyer_total,
        "unrealized_mid_seller_total": unrealized_mid_seller_total,
        "unrealized_mid_buyer_total": unrealized_mid_buyer_total,
        "realized_seller_total": realized_seller_total,
        "realized_buyer_total": realized_buyer_total,
        "avg_unrealized_fict_seller_roi": avg_unrealized_fict_seller_roi,
        "avg_unrealized_fict_buyer_roi": avg_unrealized_fict_buyer_roi,
        "avg_unrealized_fict_seller_ann_roi": avg_unrealized_fict_seller_ann_roi,
        "avg_unrealized_fict_buyer_ann_roi": avg_unrealized_fict_buyer_ann_roi,
        "avg_unrealized_actual_seller_roi": avg_unrealized_actual_seller_roi,
        "avg_unrealized_actual_buyer_roi": avg_unrealized_actual_buyer_roi,
        "avg_unrealized_actual_seller_ann_roi": avg_unrealized_actual_seller_ann_roi,
        "avg_unrealized_actual_buyer_ann_roi": avg_unrealized_actual_buyer_ann_roi,
        "avg_realized_seller_roi": avg_realized_seller_roi,
        "avg_realized_buyer_roi": avg_realized_buyer_roi,
        "avg_realized_seller_ann_roi": avg_realized_seller_ann_roi,
        "avg_realized_buyer_ann_roi": avg_realized_buyer_ann_roi,
        "stock_unrealized_long_total": stock_unrealized_long_total,
        "stock_unrealized_short_total": stock_unrealized_short_total,
        "stock_realized_long_total": stock_realized_long_total,
        "stock_realized_short_total": stock_realized_short_total,
        "avg_stock_unrealized_pct": avg_stock_unrealized_pct,
        "avg_stock_realized_pct": avg_stock_realized_pct,
        "avg_stock_unrealized_ann_roi": avg_stock_unrealized_ann_roi,
        "avg_stock_realized_ann_roi": avg_stock_realized_ann_roi,
        "stock_down_open": stock_down_open,
        "stock_down_closed": stock_down_closed,
        "settled_count": len(settled),
        "png_path": png_path,
    }
    html_path = generate_html_summary(open_rows, closed_rows, totals, today, filter_cfg, run_log, bear_call_data)
    totals["html_path"] = html_path

    return open_rows, closed_rows, totals


def main():
    ensure_deps()
    # The exchange's own calendar date, not the runner's raw system clock -
    # GitHub Actions runners are UTC, and the new ~5pm Pacific/8pm Eastern
    # run crosses UTC midnight (00:00 UTC is already the next UTC day while
    # still the same US trading day) - using America/New_York here keeps
    # "today" correct for every scheduled run time, not just the earlier
    # ones that happened to avoid that rollover.
    now_et = datetime.now(ZoneInfo("America/New_York"))
    today = now_et.date()
    # Only the evening run (well after the 4:00pm ET close) is allowed to
    # settle a position that expires TODAY - the daytime runs would risk
    # locking in yfinance's still-moving intraday price instead of the
    # actual final close.
    same_day_settle_ok = now_et.hour >= 16

    if not is_us_market_open_today(today):
        print(f"  US markets are closed today ({today.isoformat()}) - skipping this run.")
        return

    run_log = load_run_log()
    positions = load_positions()
    filter_cfg = load_filter_config()
    bear_call_positions = load_bear_call_positions()
    bear_call_cfg = load_bear_call_config()

    if ensure_pe_at_entry(positions):
        save_positions(positions)

    # The evening run (well after the 4:00pm ET close) is an end-of-day
    # true-up only: markets are shut, so there's nothing new to screen for
    # - just settle anything that expired today and refresh every open
    # position's live data. No new positions are added and no Discord
    # notifications are sent on this run; those only happen on the
    # daytime runs while the screener's data actually reflects a
    # tradable market.
    if same_day_settle_ok:
        print("-- End-of-day run: updating existing positions only, no new candidates --")
        run_log.append({
            "date": today.isoformat(),
            "time_utc": now_et.astimezone(ZoneInfo("UTC")).isoformat(),
            "run_label": None,
            "new_candidates": 0,
            "note": "eod_update_only",
        })
        save_run_log(run_log)
    else:
        print("-- Scraping Barchart top naked puts --------------------------------------")
        barchart_rows = scrape_barchart_top20()
        if not barchart_rows:
            print("  No rows scraped - aborting.")
            run_log.append({
                "date": today.isoformat(),
                "time_utc": now_et.astimezone(ZoneInfo("UTC")).isoformat(),
                "run_label": None,
                "new_candidates": None,
                "note": "scrape_failed",
            })
            save_run_log(run_log)
            return
        print(f"  Scraped {len(barchart_rows)} candidates (ranked by annualized potential return desc)")

        print("-- Scanning Yahoo for earlier (non-monthly) expirations on those symbols --")
        yahoo_weekly_rows = scrape_yahoo_weeklies(barchart_rows, today)
        print(f"  Found {len(yahoo_weekly_rows)} additional weekly candidate(s)")
        all_rows = barchart_rows + yahoo_weekly_rows

        print("-- Scanning the same symbols for bear call spread candidates --")
        bear_call_candidates = scan_bear_call_spreads(all_rows, today, bear_call_cfg)
        print(f"  Found {len(bear_call_candidates)} structurally valid bear call spread(s)")

        # Markets run this script up to 3x/day - label each run's additions
        # A, B, C (next unused letter among today's existing positions) purely
        # so a same-day Discord message and its webpage card can be visually
        # matched to "which of today's screening passes" produced it. Only
        # meaningful for today - once a position is no longer today's, the
        # card stops showing its letter (see position_card()).
        todays_run_labels = sorted(set(
            p.get("run_label") for p in positions
            if p.get("added_date") == today.isoformat() and p.get("run_label")
        ))
        run_label = chr(ord("A") + len(todays_run_labels))

        new_bear_call_candidates = pick_new_bear_call_candidates(bear_call_candidates, bear_call_positions, today)
        if new_bear_call_candidates:
            print(f"  Adding {len(new_bear_call_candidates)} new bear call spread position(s):")
            for c in new_bear_call_candidates:
                print(f"    {c['symbol']} short ${c['short_strike']:g}C / long ${c['long_strike']:g}C "
                      f"exp {c['expiration']} (credit {c['credit_pct']:.1f}% of ${c['width']:g} width)")
                bc_position = add_new_bear_call_position(c, today)
                bc_position["run_label"] = run_label
                bear_call_positions.append(bc_position)
            save_bear_call_positions(bear_call_positions)
        else:
            print("  No new bear call spread positions (all already tracked).")

        candidates = pick_new_candidates(all_rows, positions, today)
        run_log.append({
            "date": today.isoformat(),
            "time_utc": now_et.astimezone(ZoneInfo("UTC")).isoformat(),
            "run_label": run_label if candidates else None,
            "new_candidates": len(candidates),
        })
        save_run_log(run_log)
        if not candidates:
            print("\n  All of Barchart's top candidates are already open positions - nothing new to add.")
        else:
            print(f"\n  Adding {len(candidates)} new candidate(s) (run {run_label}):")
            for candidate in candidates:
                src_label = "yahoo weekly" if candidate.get("expiry_type") == "weekly" else "barchart"
                print(f"    {candidate['symbol']} ${candidate['strike']}P exp {candidate['expiration']} "
                      f"({src_label} bid {candidate['barchart_bid']:.2f}, annualized return "
                      f"{candidate.get('potential_return_annual_pct') or 0:.1f}%)")
                # Was this symbol ALREADY good enough to notify on, via any
                # still-OPEN earlier position (same run or a prior day)? Mirrors
                # the webpage's own per-(symbol, open/closed-bucket) dedup
                # exactly: a settled position no longer occupies the open
                # bucket's "first qualifying instance" slot, so once an earlier
                # qualifier on this symbol closes out, a new one is a fresh
                # signal again and should notify - same as it'd newly appear as
                # the visible card under a filter on the page.
                symbol_already_qualified = any(
                    p["symbol"] == candidate["symbol"] and not p.get("settled")
                    and position_passes_filter_config(p, filter_cfg)
                    for p in positions
                )
                position = add_new_position(candidate, today)
                position["run_label"] = run_label
                bid_source = "approx (barchart)" if position["bid_is_approx"] else "yahoo"
                ask_source = "approx (bid x 1.2)" if position["ask_is_approx"] else "yahoo"
                print(f"      bid: {position['bid']:.2f} ({bid_source})   ask: {position['ask']:.2f} ({ask_source})")
                positions.append(position)
                save_positions(positions)
                ann_return = candidate.get("potential_return_annual_pct") or 0
                if position_passes_filter_config(position, filter_cfg) and not symbol_already_qualified:
                    pe = position.get("pe_at_entry")
                    pe_text = f"{pe:.1f}" if pe is not None else "n/a"
                    mid_entry = round((position["bid"] + position["ask"]) / 2, 2)
                    weekly_tag = " [weekly]" if position.get("expiry_type") == "weekly" else ""
                    notify_discord(
                        f"**[{run_label}]{weekly_tag} New CSP candidate: {position['symbol']} ${position['strike']:g}P exp {position['expiration']}**\n"
                        f"{src_label.capitalize()} ann. return: {ann_return:.1f}% "
                        f"· PE: {pe_text} · Entry stock px {position['entry_stock_px']:.2f}\n"
                        f"Bid {position['bid']:.2f} ({bid_source})\n"
                        f"```diff\n+ Ask {position['ask']:.2f} ({ask_source})  (mid, buy: {mid_entry:.2f})\n```\n"
                        f"<{SUMMARY_HTML_URL}>"
                    )

    if settle_expired_positions(positions, today, same_day_ok=same_day_settle_ok):
        save_positions(positions)
    if settle_expired_bear_call_positions(bear_call_positions, today, same_day_ok=same_day_settle_ok):
        save_bear_call_positions(bear_call_positions)

    print("\n-- Rebuilding summary for all open positions -----------------------------")
    bc_open_rows, bc_closed_rows, bc_totals = build_bear_call_summary(
        bear_call_positions, today, fill_pct=bear_call_cfg.get("fill_pct") or 0)
    bear_call_data = {
        "open_rows": bc_open_rows,
        "closed_rows": bc_closed_rows,
        "totals": bc_totals,
        "config": bear_call_cfg,
    }
    print(f"  Bear call spreads: {len(bc_open_rows)} open, {bc_totals['settled_count']} closed")
    open_rows, closed_rows, totals = build_summary(positions, today, filter_cfg, run_log, bear_call_data)
    if not open_rows and not totals["settled_count"]:
        print("  No positions to summarize.")
        return

    if open_rows:
        df = pd.DataFrame(open_rows).sort_values("DAYS LEFT")
        print(df.to_string(index=False))
    else:
        print("  No open positions right now.")

    def pct(x):
        return f"{x:+.2f}%" if x is not None else "--"

    print(f"\n  TOTAL UNREALIZED - FICTIONAL (open, normalized to ${NORMALIZED_RISK_USD:.0f} risk each): "
          f"sold {totals['unrealized_fict_seller_total']:+.2f}  bought {totals['unrealized_fict_buyer_total']:+.2f}")
    print(f"    avg ROI: sold {pct(totals['avg_unrealized_fict_seller_roi'])}  bought {pct(totals['avg_unrealized_fict_buyer_roi'])}"
          f"   |   avg annualized ROI: sold {pct(totals['avg_unrealized_fict_seller_ann_roi'])}"
          f"  bought {pct(totals['avg_unrealized_fict_buyer_ann_roi'])}")
    print(f"\n  TOTAL UNREALIZED - ACTUAL (open, normalized to ${NORMALIZED_RISK_USD:.0f} risk each): "
          f"sold {totals['unrealized_actual_seller_total']:+.2f}  bought {totals['unrealized_actual_buyer_total']:+.2f}")
    print(f"    avg ROI: sold {pct(totals['avg_unrealized_actual_seller_roi'])}  bought {pct(totals['avg_unrealized_actual_buyer_roi'])}"
          f"   |   avg annualized ROI: sold {pct(totals['avg_unrealized_actual_seller_ann_roi'])}"
          f"  bought {pct(totals['avg_unrealized_actual_buyer_ann_roi'])}")
    print(f"  TOTAL REALIZED ({totals['settled_count']} settled, normalized to ${NORMALIZED_RISK_USD:.0f} risk each): "
          f"sold {totals['realized_seller_total']:+.2f}  bought {totals['realized_buyer_total']:+.2f}")
    print(f"    avg ROI: sold {pct(totals['avg_realized_seller_roi'])}  bought {pct(totals['avg_realized_buyer_roi'])}"
          f"   |   avg annualized ROI: sold {pct(totals['avg_realized_seller_ann_roi'])}"
          f"  bought {pct(totals['avg_realized_buyer_ann_roi'])}")
    print(f"\n  Saved {len(open_rows)} open + {len(closed_rows)} closed position(s) to {SUMMARY_CSV}")
    if totals["png_path"]:
        print(f"  Realized P&L chart saved to {totals['png_path']}")
    print(f"  HTML summary saved to {totals['html_path']}")


if __name__ == "__main__":
    main()
