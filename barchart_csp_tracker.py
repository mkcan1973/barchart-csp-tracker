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

# Single source of truth for "what counts as a good opportunity" - edit
# this file (not the script) to change which new candidates trigger a
# Discord ping AND what the webpage's filter boxes default to on first
# load (before any per-browser localStorage customization overrides it).
# Same fields/semantics as the webpage's own filter boxes; null/missing
# means no bound on that dimension. Every new candidate is still tracked
# and shown on the dashboard regardless - this only gates the notification.
FILTER_CONFIG_FILE = Path("discord_filter_config.json")
DEFAULT_FILTER_CONFIG = {
    "min_roi": 150, "max_roi": None,
    "min_pe": None, "max_pe": None,
    "min_dte_entry": None, "max_dte_entry": None,
    "base_investment": None,
    "min_put_price": None, "max_put_price": None,
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
    base investment/put price-as-strike) - works on either a freshly-built
    candidate position or an already-stored one, since both carry the same
    field names."""
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
    if cfg.get("min_put_price") is not None and (strike is None or strike < cfg["min_put_price"]):
        return False
    if cfg.get("max_put_price") is not None and (strike is None or strike > cfg["max_put_price"]):
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
        })

    return rows_out

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
    }
    return position

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
    for r in closed_rows:
        d = datetime.strptime(r["EXPIRATION"], "%Y-%m-%d").date()
        bucket = by_date.setdefault(d, {"seller": [], "buyer": []})
        if r["ROI % IF SOLD (CSP)"] is not None:
            bucket["seller"].append(r["ROI % IF SOLD (CSP)"])
        if r["ROI % IF BOUGHT (long put)"] is not None:
            bucket["buyer"].append(r["ROI % IF BOUGHT (long put)"])

    dates = sorted(by_date)
    avg_seller = [sum(by_date[d]["seller"]) / len(by_date[d]["seller"]) if by_date[d]["seller"] else None for d in dates]
    avg_buyer = [sum(by_date[d]["buyer"]) / len(by_date[d]["buyer"]) if by_date[d]["buyer"] else None for d in dates]

    fig, ax = plt.subplots(figsize=(9, 5))
    ax.plot(dates, avg_seller, marker="o", label="Short (CSP seller)")
    ax.plot(dates, avg_buyer, marker="o", label="Long (put buyer)")
    ax.axhline(0, color="gray", linewidth=0.8)
    ax.set_xlabel("Settlement (expiration) date")
    ax.set_ylabel("Avg ROI % for that period's settlements")
    ax.set_title("Realized CSP ROI by settlement period")
    ax.legend()
    ax.grid(True, alpha=0.3)
    fig.autofmt_xdate()
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


def generate_html_summary(open_rows, closed_rows, totals, today, filter_cfg=None):
    """Single self-contained HTML file - a card per position (readable on a
    phone, unlike the 20+ column CSV) plus the totals and the realized P&L
    chart if one exists. No build step, no external assets - just open it in
    a browser (or serve it as-is via GitHub Pages)."""

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
              <div class="label">SHORT (sold CSP) - bullish, same side as long stock</div>
              <div class="val {_pnl_class(seller_pnl)}">{_fmt_money(seller_pnl)}<span class="{_pnl_class(seller_mid)}">{_fmt_money_paren(seller_mid, seller_mid_label)}</span></div>
              <div class="sub2">ROI {_fmt_pct(seller_roi)} &middot; ann {_fmt_pct(ann_seller_roi)}</div>
              <div class="sub2">norm (<span class="norm-base-num">{NORMALIZED_RISK_USD:.0f}</span> risk): <span class="{_pnl_class(norm_seller)} norm-primary-num" data-src="{norm_seller_key}">{_fmt_money(norm_seller)}</span>{f' ({seller_mid_label}: ' + seller_mid_num_html + ')' if seller_mid_num_html else ''}</div>
              {seller_quote_html}
            </div>
            <div class="box">
              <div class="label">LONG (bought put) - bearish, same side as short stock</div>
              <div class="val {_pnl_class(buyer_pnl)}">{_fmt_money(buyer_pnl)}<span class="{_pnl_class(buyer_mid)}">{_fmt_money_paren(buyer_mid, buyer_mid_label)}</span></div>
              <div class="sub2">ROI {_fmt_pct(buyer_roi)} &middot; ann {_fmt_pct(ann_buyer_roi)}</div>
              <div class="sub2">norm (<span class="norm-base-num">{NORMALIZED_RISK_USD:.0f}</span> risk): <span class="{_pnl_class(norm_buyer)} norm-primary-num" data-src="{norm_buyer_key}">{_fmt_money(norm_buyer)}</span>{f' ({buyer_mid_label}: ' + buyer_mid_num_html + ')' if buyer_mid_num_html else ''}</div>
              {buyer_quote_html}
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
                f'data-kind="closed" '
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
                    rows_html += (f'<div class="sub2">Short {" and ".join(seller_approx_labels)} approximated via '
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
                f'data-stock-pct="{attr(r["STOCK PCT CHANGE"])}" data-stock-pct-ann="{attr(r["STOCK PCT CHANGE ANN"])}"'
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
        return f"""
        <div class="card" data-ann-return="{attr(ann_return)}" data-pe="{attr(pe)}" data-dte-entry="{attr(dte_entry)}" data-ask="{attr(r.get('ASK'))}" data-strike="{attr(r['STRIKE'])}" data-symbol="{_html_escape(r['SYMBOL'])}" data-added="{attr(r['ADDED'])}" {data_attrs}>
          <div class="card-head">
            <span class="sym">{_html_escape(r['SYMBOL'])}</span>
            <span class="strike">${r['STRIKE']:g}P</span>
            <span class="exp">{r['EXPIRATION']}</span>
            {run_badge}
          </div>
          <div class="sub">{days_line} &middot; Entry {r['ENTRY STOCK PRICE']:.2f} &middot; {price_line}
            &middot; bid {r['BID']:.2f}/{r['BID SOURCE']} &middot; ask {r['ASK']:.2f}/{r['ASK SOURCE']}</div>
          <div class="sub">Barchart ann. return at selection: {_fmt_pct(ann_return)} &middot; PE at entry: {pe_text} ({r.get('PE SOURCE', '')}) &middot; DTE at entry: {dte_entry if dte_entry is not None else '--'}</div>
          {rows_html}
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

    chart_html = ""
    if totals["png_path"]:
        chart_html = f'<h2>Realized P&amp;L over time</h2><img class="chart" src="{REALIZED_PNL_PNG.name}" alt="Realized P&L chart">'

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
  h2 {{ font-size: 1.1rem; margin-top: 28px; border-top: 1px solid #2a2f3a; padding-top: 16px; }}
  .updated {{ color: #9aa4b2; font-size: 0.85rem; margin-top: 2px; margin-bottom: 20px; }}
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
  .sub {{ color: #9aa4b2; font-size: 0.82rem; margin-top: 4px; }}
  .sub2 {{ color: #9aa4b2; font-size: 0.78rem; margin-top: 2px; }}
  .rowlabel {{ font-size: 0.72rem; letter-spacing: 0.03em; color: #9aa4b2; margin-top: 10px; }}
  .grid2 {{ display: grid; grid-template-columns: 1fr 1fr; gap: 10px; margin-top: 10px; }}
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
  .filterbar .count {{ color: #9aa4b2; font-size: 0.8rem; margin-left: auto; align-self: center; }}
  @media (prefers-color-scheme: light) {{
    body {{ background: #f5f6f8; color: #1a1d23; }}
    .totals .box, .card, .box {{ background: #ffffff; box-shadow: 0 1px 3px rgba(0,0,0,0.08); }}
    .label, .sub, .sub2, .rowlabel, .updated, .card-head .exp, .card-head .strike {{ color: #6b7280; }}
    .filterbar {{ background: #ffffff; box-shadow: 0 1px 3px rgba(0,0,0,0.08); }}
    .filterbar label {{ color: #6b7280; }}
    .filterbar input {{ background: #f5f6f8; border-color: #d0d5dd; }}
    .filterbar .count {{ color: #6b7280; }}
  }}
</style>
</head>
<body>
  <h1>Barchart CSP Tracker</h1>
  <div class="updated">Last updated {today.isoformat()} &middot; {len(open_rows)} open &middot; {len(closed_rows)} closed</div>

  <div class="filterbar">
    <label>Min ROI % <input type="number" id="minRoi" step="any" placeholder="-&infin;" inputmode="decimal"></label>
    <label>Max ROI % <input type="number" id="maxRoi" step="any" placeholder="&infin;" inputmode="decimal"></label>
    <label>Min PE <input type="number" id="minPe" step="any" placeholder="-&infin;" inputmode="decimal"></label>
    <label>Max PE <input type="number" id="maxPe" step="any" placeholder="&infin;" inputmode="decimal"></label>
    <label>Min DTE@entry <input type="number" id="minDte" step="any" placeholder="-&infin;" inputmode="decimal"></label>
    <label>Max DTE@entry <input type="number" id="maxDte" step="any" placeholder="&infin;" inputmode="decimal"></label>
    <label>Base investment $ <input type="number" id="baseInvest" step="any" placeholder="e.g. 1000" inputmode="decimal"></label>
    <label>Min put price <input type="number" id="minPutPrice" step="any" placeholder="-&infin;" inputmode="decimal"></label>
    <label>Max put price <input type="number" id="maxPutPrice" step="any" placeholder="&infin;" inputmode="decimal"></label>
    <button id="applyFilter" type="button">Filter</button>
    <span class="count" id="filterCount"></span>
  </div>
  <div class="updated" style="margin-top:-6px;">ROI filters on Barchart's annualized return at selection; PE filters on trailing P/E at entry (both frozen at entry, always available)</div>
  <div class="updated" style="margin-top:-6px;">Short/Long below = option position, NOT shares: Short = sold the CSP (bullish - same side as owning stock). Long = bought the put (bearish - same side as shorting stock).</div>

  <div class="totals">
    <div class="box">
      <div class="label">UNREALIZED - ACTUAL, worst case (<span id="openCount">{len(open_rows)}</span> open, normalized $<span class="norm-base-num">{NORMALIZED_RISK_USD:.0f}</span>/position)</div>
      <div class="val {_pnl_class(totals['unrealized_actual_seller_total'])}" id="totalActualSeller">Short <span id="totalActualSellerAmt">{_fmt_money(totals['unrealized_actual_seller_total'])}</span><span id="totalActualSellerMid" class="{_pnl_class(totals['unrealized_mid_seller_total'])}">{_fmt_money_paren(totals['unrealized_mid_seller_total'])}</span></div>
      <div class="val {_pnl_class(totals['unrealized_actual_buyer_total'])}" id="totalActualBuyer">Long <span id="totalActualBuyerAmt">{_fmt_money(totals['unrealized_actual_buyer_total'])}</span><span id="totalActualBuyerMid" class="{_pnl_class(totals['unrealized_mid_buyer_total'])}">{_fmt_money_paren(totals['unrealized_mid_buyer_total'])}</span></div>
      <div class="sub2">avg ROI: short <span id="avgActualSellerRoi">{_fmt_pct(totals['avg_unrealized_actual_seller_roi'])}</span> / long <span id="avgActualBuyerRoi">{_fmt_pct(totals['avg_unrealized_actual_buyer_roi'])}</span></div>
      <div class="sub2">avg ann. ROI: short <span id="avgActualSellerAnn">{_fmt_pct(totals['avg_unrealized_actual_seller_ann_roi'])}</span> / long <span id="avgActualBuyerAnn">{_fmt_pct(totals['avg_unrealized_actual_buyer_ann_roi'])}</span></div>
      <div class="sub2">(mid) = less pessimistic reference using the mid price instead of crossing the spread</div>
    </div>
    <div class="box">
      <div class="label">REALIZED (<span id="realizedCount">{totals['settled_count']}</span> settled, normalized $<span class="norm-base-num">{NORMALIZED_RISK_USD:.0f}</span>/position)</div>
      <div class="val {_pnl_class(totals['realized_seller_total'])}" id="totalRealizedSeller">Short <span id="totalRealizedSellerAmt">{_fmt_money(totals['realized_seller_total'])}</span></div>
      <div class="val {_pnl_class(totals['realized_buyer_total'])}" id="totalRealizedBuyer">Long <span id="totalRealizedBuyerAmt">{_fmt_money(totals['realized_buyer_total'])}</span></div>
      <div class="sub2">avg ROI: short <span id="avgRealizedSellerRoi">{_fmt_pct(totals['avg_realized_seller_roi'])}</span> / long <span id="avgRealizedBuyerRoi">{_fmt_pct(totals['avg_realized_buyer_roi'])}</span></div>
      <div class="sub2">avg ann. ROI: short <span id="avgRealizedSellerAnn">{_fmt_pct(totals['avg_realized_seller_ann_roi'])}</span> / long <span id="avgRealizedBuyerAnn">{_fmt_pct(totals['avg_realized_buyer_ann_roi'])}</span></div>
    </div>
    <div class="box">
      <div class="label">STOCK BENCHMARK (no options - buy/short $<span class="norm-base-num">{NORMALIZED_RISK_USD:.0f}</span> of shares at entry)</div>
      <div class="val {_pnl_class(totals['stock_unrealized_long_total'])}" id="totalStockUnrealLong">Open, Long <span id="totalStockUnrealLongAmt">{_fmt_money(totals['stock_unrealized_long_total'])}</span></div>
      <div class="val {_pnl_class(totals['stock_unrealized_short_total'])}" id="totalStockUnrealShort">Open, Short <span id="totalStockUnrealShortAmt">{_fmt_money(totals['stock_unrealized_short_total'])}</span></div>
      <div class="sub2">avg price change (open): <span id="avgStockUnrealPct">{_fmt_pct(totals['avg_stock_unrealized_pct'])}</span> &middot; avg ann. ROI: <span id="avgStockUnrealAnn">{_fmt_pct(totals['avg_stock_unrealized_ann_roi'])}</span></div>
      <div class="val {_pnl_class(totals['stock_realized_long_total'])}" id="totalStockRealLong">Closed, Long <span id="totalStockRealLongAmt">{_fmt_money(totals['stock_realized_long_total'])}</span></div>
      <div class="val {_pnl_class(totals['stock_realized_short_total'])}" id="totalStockRealShort">Closed, Short <span id="totalStockRealShortAmt">{_fmt_money(totals['stock_realized_short_total'])}</span></div>
      <div class="sub2">avg price change (closed): <span id="avgStockRealPct">{_fmt_pct(totals['avg_stock_realized_pct'])}</span> &middot; avg ann. ROI: <span id="avgStockRealAnn">{_fmt_pct(totals['avg_stock_realized_ann_roi'])}</span></div>
      <div class="sub2">Indicator only - short assumes unlimited-risk shorting is actually available.</div>
    </div>
  </div>
  <div class="updated" id="filterNote" style="display:none;">Totals above reflect only the positions currently passing the filter.</div>

  {chart_html}

  <h2>Open positions (<span id="openSectionCount">{len(open_rows)}</span>)</h2>
  <div class="cards">
  {open_cards}
  </div>

  <h2>Closed positions (<span id="closedSectionCount">{len(closed_rows)}</span>)</h2>
  <div class="cards">
  {closed_cards}
  </div>

<script>
(function() {{
  var DEFAULT_FILTERS = {json.dumps(filter_cfg or DEFAULT_FILTER_CONFIG)};
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
    if (div) div.className = 'val ' + pnlClass(val);
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
    var minPutPriceRaw = document.getElementById('minPutPrice').value.trim();
    var maxPutPriceRaw = document.getElementById('maxPutPrice').value.trim();
    var noFilter = minRoiRaw === '' && maxRoiRaw === '' && minPeRaw === '' && maxPeRaw === ''
      && minDteRaw === '' && maxDteRaw === '' && baseInvestRaw === ''
      && minPutPriceRaw === '' && maxPutPriceRaw === '';
    var minRoi = minRoiRaw === '' ? -Infinity : parseFloat(minRoiRaw);
    var maxRoi = maxRoiRaw === '' ? Infinity : parseFloat(maxRoiRaw);
    var minPe = minPeRaw === '' ? -Infinity : parseFloat(minPeRaw);
    var maxPe = maxPeRaw === '' ? Infinity : parseFloat(maxPeRaw);
    var minDte = minDteRaw === '' ? -Infinity : parseFloat(minDteRaw);
    var maxDte = maxDteRaw === '' ? Infinity : parseFloat(maxDteRaw);
    var baseInvest = baseInvestRaw === '' ? Infinity : parseFloat(baseInvestRaw);
    var minPutPrice = minPutPriceRaw === '' ? -Infinity : parseFloat(minPutPriceRaw);
    var maxPutPrice = maxPutPriceRaw === '' ? Infinity : parseFloat(maxPutPriceRaw);
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

      // Put price = the STRIKE (not the premium/ask) - lets you skip
      // low-strike puts with little profit potential on the long side, or
      // cap how high a strike you want to consider.
      var strikeRaw = card.getAttribute('data-strike');
      var strikeVal = strikeRaw === '' ? null : parseFloat(strikeRaw);
      var putPriceOk = (minPutPriceRaw === '' && maxPutPriceRaw === '')
        || (strikeVal !== null && !isNaN(strikeVal) && strikeVal >= minPutPrice && strikeVal <= maxPutPrice);

      var dteRaw = card.getAttribute('data-dte-entry');
      var dteVal = dteRaw === '' ? null : parseFloat(dteRaw);
      var dteOk = (minDteRaw === '' && maxDteRaw === '')
        || (dteVal !== null && !isNaN(dteVal) && dteVal >= minDte && dteVal <= maxDte);

      if (noFilter || (roiOk && peOk && dteOk && investOk && putPriceOk)) {{
        passing.push(card);
      }}
    }});

    // Pass 2: with an actual filter active, only the chronologically FIRST
    // passing instance per symbol represents "the trade you'd have taken"
    // on a real entry signal - a later instance of the same symbol that
    // also clears the bar is suppressed, so one stock can't occupy (or
    // count toward) the summary more than once at a time.
    var selected;
    if (noFilter) {{
      selected = passing;
    }} else {{
      var firstForSymbol = {{}};
      passing.forEach(function(card) {{
        var sym = card.getAttribute('data-symbol');
        var added = card.getAttribute('data-added') || '';
        var current = firstForSymbol[sym];
        if (!current || added < current.getAttribute('data-added')) {{
          firstForSymbol[sym] = card;
        }}
      }});
      selected = Object.keys(firstForSymbol).map(function(sym) {{ return firstForSymbol[sym]; }});
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

    try {{
      localStorage.setItem('csp_filter_min_roi', minRoiRaw);
      localStorage.setItem('csp_filter_max_roi', maxRoiRaw);
      localStorage.setItem('csp_filter_min_pe', minPeRaw);
      localStorage.setItem('csp_filter_max_pe', maxPeRaw);
      localStorage.setItem('csp_filter_min_dte', minDteRaw);
      localStorage.setItem('csp_filter_max_dte', maxDteRaw);
      localStorage.setItem('csp_filter_base_invest', baseInvestRaw);
      localStorage.setItem('csp_filter_min_put_price', minPutPriceRaw);
      localStorage.setItem('csp_filter_max_put_price', maxPutPriceRaw);
    }} catch (e) {{}}
  }}

  var btn = document.getElementById('applyFilter');
  if (btn) btn.addEventListener('click', applyFilter);
  ['minRoi', 'maxRoi', 'minPe', 'maxPe', 'minDte', 'maxDte', 'baseInvest', 'minPutPrice', 'maxPutPrice'].forEach(function(id) {{
    var el = document.getElementById(id);
    if (el) el.addEventListener('keydown', function(e) {{ if (e.key === 'Enter') applyFilter(); }});
  }});

  var fieldToCfgKey = {{
    minRoi: 'min_roi', maxRoi: 'max_roi',
    minPe: 'min_pe', maxPe: 'max_pe',
    minDte: 'min_dte_entry', maxDte: 'max_dte_entry',
    baseInvest: 'base_investment',
    minPutPrice: 'min_put_price', maxPutPrice: 'max_put_price'
  }};
  try {{
    var saved = {{
      minRoi: localStorage.getItem('csp_filter_min_roi'),
      maxRoi: localStorage.getItem('csp_filter_max_roi'),
      minPe: localStorage.getItem('csp_filter_min_pe'),
      maxPe: localStorage.getItem('csp_filter_max_pe'),
      minDte: localStorage.getItem('csp_filter_min_dte'),
      maxDte: localStorage.getItem('csp_filter_max_dte'),
      baseInvest: localStorage.getItem('csp_filter_base_invest'),
      minPutPrice: localStorage.getItem('csp_filter_min_put_price'),
      maxPutPrice: localStorage.getItem('csp_filter_max_put_price')
    }};
    Object.keys(saved).forEach(function(id) {{
      if (saved[id]) {{
        document.getElementById(id).value = saved[id];
      }} else {{
        var cfgVal = DEFAULT_FILTERS[fieldToCfgKey[id]];
        if (cfgVal !== null && cfgVal !== undefined) document.getElementById(id).value = cfgVal;
      }}
    }});
  }} catch (e) {{}}
  applyFilter();
}})();
</script>
</body>
</html>
"""
    SUMMARY_HTML.write_text(html, encoding="utf-8")
    return SUMMARY_HTML


def build_summary(positions, today, filter_cfg=None):
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

    png_path = plot_realized_pnl(closed_rows)

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
        "settled_count": len(settled),
        "png_path": png_path,
    }
    html_path = generate_html_summary(open_rows, closed_rows, totals, today, filter_cfg)
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

    print("-- Scraping Barchart top naked puts --------------------------------------")
    barchart_rows = scrape_barchart_top20()
    if not barchart_rows:
        print("  No rows scraped - aborting.")
        return
    print(f"  Scraped {len(barchart_rows)} candidates (ranked by annualized potential return desc)")

    positions = load_positions()
    filter_cfg = load_filter_config()

    if ensure_pe_at_entry(positions):
        save_positions(positions)

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

    candidates = pick_new_candidates(barchart_rows, positions, today)
    if not candidates:
        print("\n  All of Barchart's top candidates are already open positions - nothing new to add.")
    else:
        print(f"\n  Adding {len(candidates)} new candidate(s) (run {run_label}):")
        for candidate in candidates:
            print(f"    {candidate['symbol']} ${candidate['strike']}P exp {candidate['expiration']} "
                  f"(barchart bid {candidate['barchart_bid']:.2f}, annualized return "
                  f"{candidate.get('potential_return_annual_pct') or 0:.1f}%)")
            # Was this symbol ALREADY good enough to notify on, via any
            # earlier position (same run or a prior day)? If so this new
            # contract isn't a fresh signal - same philosophy as the
            # dashboard's own "first instance to qualify per symbol" filter,
            # just applied to the notification trigger instead of display.
            symbol_already_qualified = any(
                p["symbol"] == candidate["symbol"] and position_passes_filter_config(p, filter_cfg)
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
                notify_discord(
                    f"**[{run_label}] New CSP candidate: {position['symbol']} ${position['strike']:g}P exp {position['expiration']}**\n"
                    f"Barchart ann. return: {ann_return:.1f}% "
                    f"· PE: {pe_text} · Entry stock px {position['entry_stock_px']:.2f}\n"
                    f"Bid {position['bid']:.2f} ({bid_source})\n"
                    f"```diff\n+ Ask {position['ask']:.2f} ({ask_source})  (mid, buy: {mid_entry:.2f})\n```\n"
                    f"<{SUMMARY_HTML_URL}>"
                )

    if settle_expired_positions(positions, today, same_day_ok=same_day_settle_ok):
        save_positions(positions)

    print("\n-- Rebuilding summary for all open positions -----------------------------")
    open_rows, closed_rows, totals = build_summary(positions, today, filter_cfg)
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
