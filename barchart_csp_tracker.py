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

# Only ping Discord for new candidates at or above this Barchart annualized
# return at selection - every new candidate still gets tracked regardless,
# this only gates the notification.
DISCORD_NOTIFY_MIN_ANN_RETURN_PCT = 150.0

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


def notify_expiration_reminders(positions, open_rows, today):
    """One-day-ahead heads-up for open positions, sent once per position
    (flagged on the stored record so it never repeats on a later run that
    same day, or any day after). The user's actual strategy is going long
    (buying the put), so the message leads with the LONG-side decision:
    sell now at the current bid, or exercise if that's already better -
    reusing the same exercise-vs-mid figure already computed for the card.
    Returns True if any position was flagged (caller should save_positions())."""
    changed = False
    by_key = {(p["symbol"], p["strike"], p["expiration"]): p for p in positions}
    for r in open_rows:
        if r["DAYS LEFT"] != 1:
            continue
        p = by_key.get((r["SYMBOL"], r["STRIKE"], r["EXPIRATION"]))
        if p is None or p.get("expiration_reminder_sent"):
            continue

        stock_px = r.get("CURRENT STOCK PRICE")
        stock_line = f"Current stock px: {stock_px:.2f}" if stock_px is not None else "Current stock px: no live quote"
        current_bid = r.get("CURRENT OPTION BID")
        bid_line = (f"+ Current bid (sell to close): {current_bid:.2f}" if current_bid is not None
                    else "+ Current bid: no live quote")
        action_label = "exe" if r.get("BUYER MID IS EXERCISE") else "mid"
        action_value = r.get("UNREALIZED P/L (MID) IF BOUGHT (long put)")
        action_line = f"Long P/L ({action_label}): {_fmt_money(action_value)}"

        notify_discord(
            f"**Expiring tomorrow: {r['SYMBOL']} ${r['STRIKE']:g}P exp {r['EXPIRATION']}**\n"
            f"{stock_line}\n"
            f"```diff\n{bid_line}\n```\n"
            f"{action_line}\n"
            f"<{SUMMARY_HTML_URL}>"
        )
        p["expiration_reminder_sent"] = True
        changed = True
    return changed


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


def get_trailing_pe(symbol):
    """Trailing P/E at this moment - used both to capture a new position's
    entry-time PE and, once, to backfill a stand-in for positions tracked
    before the PE filter existed. None if yfinance has nothing (no/negative
    earnings, delisted, etc.) - a real, not uncommon case, not an error."""
    _yf_rate_limiter.wait()
    try:
        pe = yf.Ticker(symbol).info.get("trailingPE")
        return float(pe) if pe is not None else None
    except Exception:
        return None


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
    """One-time backfill: positions tracked before the PE filter existed
    have no captured entry-time trailing P/E. Fetch today's P/E as an
    approximate stand-in (flagged), fetched once here and then frozen
    permanently in the stored record - never re-fetched on later runs, same
    pattern as the "bid" backward-compat migration. Returns True if any
    position changed (caller should save_positions() in that case)."""
    changed = False
    for p in positions:
        if "pe_at_entry" not in p:
            p["pe_at_entry"] = get_trailing_pe(p["symbol"])
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
    contract) - callers should show that as unavailable, not fall back
    silently, since mixing an approximation into the "actual" column would
    defeat the point of distinguishing it from "fictional"."""
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


def settle_expired_positions(positions, today):
    """Once a tracked position's expiration has passed, lock in its final
    P&L using the stock price at expiration instead of continuing to mark it
    to market - settled positions are kept permanently (not dropped) so a
    realized P&L total means something."""
    changed = False
    for p in positions:
        if p.get("settled"):
            continue
        exp_date = datetime.strptime(p["expiration"], "%Y-%m-%d").date()
        if exp_date >= today:
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
    pe_at_entry = get_trailing_pe(symbol)

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
    """PNG of cumulative realized P&L over time (by expiration date), one
    line for the CSP-seller (short) side and one for the long-put-buyer
    side - both already normalized to NORMALIZED_RISK_USD risk/position so
    the running totals are comparable across differently-priced names."""
    if not closed_rows:
        return None
    ensure_plot_deps()

    dates = [datetime.strptime(r["EXPIRATION"], "%Y-%m-%d").date() for r in closed_rows]
    cum_short = [r["CUMULATIVE P/L IF SOLD"] for r in closed_rows]
    cum_long = [r["CUMULATIVE P/L IF BOUGHT"] for r in closed_rows]

    fig, ax = plt.subplots(figsize=(9, 5))
    ax.plot(dates, cum_short, marker="o", label="Short (CSP seller)")
    ax.plot(dates, cum_long, marker="o", label="Long (put buyer)")
    ax.axhline(0, color="gray", linewidth=0.8)
    ax.set_xlabel("Expiration date")
    ax.set_ylabel(f"Cumulative realized P/L (normalized to ${NORMALIZED_RISK_USD:.0f} risk/position)")
    ax.set_title("Realized CSP P&L over time")
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


def generate_html_summary(open_rows, closed_rows, totals, today):
    """Single self-contained HTML file - a card per position (readable on a
    phone, unlike the 20+ column CSV) plus the totals and the realized P&L
    chart if one exists. No build step, no external assets - just open it in
    a browser (or serve it as-is via GitHub Pages)."""

    def pnl_row(label, seller_pnl, buyer_pnl, seller_roi, buyer_roi, ann_seller_roi, ann_buyer_roi, norm_seller, norm_buyer,
                seller_quote=None, seller_quote_label="", buyer_quote=None, buyer_quote_label="",
                seller_mid=None, buyer_mid=None, norm_seller_mid=None, norm_buyer_mid=None,
                seller_mid_label="mid", buyer_mid_label="mid"):
        # seller_mid/buyer_mid are on the SAME (raw, per-position) basis as
        # seller_pnl/buyer_pnl; norm_seller_mid/norm_buyer_mid are on the same
        # normalized basis as norm_seller/norm_buyer - each parenthetical
        # must sit next to the number it's actually comparable to.
        # buyer_mid_label switches to "exe" when buyer_mid is actually a
        # guaranteed exercise value (buy shares + exercise), not a market
        # mid-price estimate.
        seller_quote_html = (f'<div class="sub2">{seller_quote_label}: {_fmt_money(seller_quote)}</div>'
                              if seller_quote is not None else '')
        buyer_quote_html = (f'<div class="sub2">{buyer_quote_label}: {_fmt_money(buyer_quote)}</div>'
                             if buyer_quote is not None else '')
        return f"""
          <div class="rowlabel">{label}</div>
          <div class="grid2">
            <div class="box">
              <div class="label">SHORT (sold CSP)</div>
              <div class="val {_pnl_class(seller_pnl)}">{_fmt_money(seller_pnl)}<span class="{_pnl_class(seller_mid)}">{_fmt_money_paren(seller_mid, seller_mid_label)}</span></div>
              <div class="sub2">ROI {_fmt_pct(seller_roi)} &middot; ann {_fmt_pct(ann_seller_roi)}</div>
              <div class="sub2">norm ({NORMALIZED_RISK_USD:.0f} risk): {_fmt_money(norm_seller)}<span class="{_pnl_class(norm_seller_mid)}">{_fmt_money_paren(norm_seller_mid, seller_mid_label)}</span></div>
              {seller_quote_html}
            </div>
            <div class="box">
              <div class="label">LONG (bought put)</div>
              <div class="val {_pnl_class(buyer_pnl)}">{_fmt_money(buyer_pnl)}<span class="{_pnl_class(buyer_mid)}">{_fmt_money_paren(buyer_mid, buyer_mid_label)}</span></div>
              <div class="sub2">ROI {_fmt_pct(buyer_roi)} &middot; ann {_fmt_pct(ann_buyer_roi)}</div>
              <div class="sub2">norm ({NORMALIZED_RISK_USD:.0f} risk): {_fmt_money(norm_buyer)}<span class="{_pnl_class(norm_buyer_mid)}">{_fmt_money_paren(norm_buyer_mid, buyer_mid_label)}</span></div>
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
        days_line = f"Settled {r['SETTLED AT']}" if closed else f"{r['DAYS LEFT']}d left"

        if closed:
            rows_html = pnl_row("REALIZED", r["REALIZED P/L IF SOLD (CSP)"], r["REALIZED P/L IF BOUGHT (long put)"],
                                 r["ROI % IF SOLD (CSP)"], r["ROI % IF BOUGHT (long put)"],
                                 r["ANNUALIZED ROI % IF SOLD (CSP)"], r["ANNUALIZED ROI % IF BOUGHT (long put)"],
                                 r[realized_norm_seller_key], r[realized_norm_buyer_key])
            data_attrs = (
                f'data-kind="closed" '
                f'data-norm-rs="{attr(r[realized_norm_seller_key])}" data-norm-rb="{attr(r[realized_norm_buyer_key])}" '
                f'data-roi-rs="{attr(r["ROI % IF SOLD (CSP)"])}" data-roi-rb="{attr(r["ROI % IF BOUGHT (long put)"])}" '
                f'data-ann-rs="{attr(r["ANNUALIZED ROI % IF SOLD (CSP)"])}" data-ann-rb="{attr(r["ANNUALIZED ROI % IF BOUGHT (long put)"])}"'
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
                                 seller_quote=r["CURRENT OPTION ASK"], seller_quote_label="current ask (pay to close)",
                                 buyer_quote=r["CURRENT OPTION BID"], buyer_quote_label="current bid (receive to close)",
                                 seller_mid=r["UNREALIZED P/L (MID) IF SOLD (CSP)"],
                                 buyer_mid=r["UNREALIZED P/L (MID) IF BOUGHT (long put)"],
                                 norm_seller_mid=r[mid_norm_seller_key], norm_buyer_mid=r[mid_norm_buyer_key],
                                 buyer_mid_label=buyer_mid_label)
            if buyer_mid_is_exercise:
                rows_html += ('<div class="sub2">Long "exe" = buy shares + exercise the put '
                               '(guaranteed, independent of the option\'s own market quotes)</div>')
            data_attrs = (
                f'data-kind="open" '
                f'data-norm-as="{attr(r[actual_norm_seller_key])}" data-norm-ab="{attr(r[actual_norm_buyer_key])}" '
                f'data-roi-as="{attr(r["ROI % (ACTUAL) IF SOLD (CSP)"])}" data-roi-ab="{attr(r["ROI % (ACTUAL) IF BOUGHT (long put)"])}" '
                f'data-ann-as="{attr(r["ANNUALIZED ROI % (ACTUAL) IF SOLD (CSP)"])}" data-ann-ab="{attr(r["ANNUALIZED ROI % (ACTUAL) IF BOUGHT (long put)"])}" '
                f'data-norm-ms="{attr(r[mid_norm_seller_key])}" data-norm-mb="{attr(r[mid_norm_buyer_key])}"'
            )

        ann_return = r.get('BARCHART ANNUALIZED RETURN % (at selection)')
        pe = r.get('PE AT ENTRY')
        pe_text = f"{pe:.1f}" if pe is not None else "--"
        return f"""
        <div class="card" data-ann-return="{attr(ann_return)}" data-pe="{attr(pe)}" data-symbol="{_html_escape(r['SYMBOL'])}" data-added="{attr(r['ADDED'])}" {data_attrs}>
          <div class="card-head">
            <span class="sym">{_html_escape(r['SYMBOL'])}</span>
            <span class="strike">${r['STRIKE']:g}P</span>
            <span class="exp">{r['EXPIRATION']}</span>
          </div>
          <div class="sub">{days_line} &middot; Entry {r['ENTRY STOCK PRICE']:.2f} &middot; {price_line}
            &middot; bid {r['BID']:.2f}/{r['BID SOURCE']} &middot; ask {r['ASK']:.2f}/{r['ASK SOURCE']}</div>
          <div class="sub">Barchart ann. return at selection: {_fmt_pct(ann_return)} &middot; PE at entry: {pe_text} ({r.get('PE SOURCE', '')})</div>
          {rows_html}
        </div>"""

    open_rows_newest_first = sorted(open_rows, key=lambda r: r["ADDED"], reverse=True)
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
    <button id="applyFilter" type="button">Filter</button>
    <span class="count" id="filterCount"></span>
  </div>
  <div class="updated" style="margin-top:-6px;">ROI filters on Barchart's annualized return at selection; PE filters on trailing P/E at entry (both frozen at entry, always available)</div>

  <div class="totals">
    <div class="box">
      <div class="label">UNREALIZED - ACTUAL, worst case (<span id="openCount">{len(open_rows)}</span> open, normalized ${NORMALIZED_RISK_USD:.0f}/position)</div>
      <div class="val {_pnl_class(totals['unrealized_actual_seller_total'])}" id="totalActualSeller">Short <span id="totalActualSellerAmt">{_fmt_money(totals['unrealized_actual_seller_total'])}</span><span id="totalActualSellerMid" class="{_pnl_class(totals['unrealized_mid_seller_total'])}">{_fmt_money_paren(totals['unrealized_mid_seller_total'])}</span></div>
      <div class="val {_pnl_class(totals['unrealized_actual_buyer_total'])}" id="totalActualBuyer">Long <span id="totalActualBuyerAmt">{_fmt_money(totals['unrealized_actual_buyer_total'])}</span><span id="totalActualBuyerMid" class="{_pnl_class(totals['unrealized_mid_buyer_total'])}">{_fmt_money_paren(totals['unrealized_mid_buyer_total'])}</span></div>
      <div class="sub2">avg ROI: short <span id="avgActualSellerRoi">{_fmt_pct(totals['avg_unrealized_actual_seller_roi'])}</span> / long <span id="avgActualBuyerRoi">{_fmt_pct(totals['avg_unrealized_actual_buyer_roi'])}</span></div>
      <div class="sub2">avg ann. ROI: short <span id="avgActualSellerAnn">{_fmt_pct(totals['avg_unrealized_actual_seller_ann_roi'])}</span> / long <span id="avgActualBuyerAnn">{_fmt_pct(totals['avg_unrealized_actual_buyer_ann_roi'])}</span></div>
      <div class="sub2">(mid) = less pessimistic reference using the mid price instead of crossing the spread</div>
    </div>
    <div class="box">
      <div class="label">REALIZED (<span id="realizedCount">{totals['settled_count']}</span> settled, normalized ${NORMALIZED_RISK_USD:.0f}/position)</div>
      <div class="val {_pnl_class(totals['realized_seller_total'])}" id="totalRealizedSeller">Short <span id="totalRealizedSellerAmt">{_fmt_money(totals['realized_seller_total'])}</span></div>
      <div class="val {_pnl_class(totals['realized_buyer_total'])}" id="totalRealizedBuyer">Long <span id="totalRealizedBuyerAmt">{_fmt_money(totals['realized_buyer_total'])}</span></div>
      <div class="sub2">avg ROI: short <span id="avgRealizedSellerRoi">{_fmt_pct(totals['avg_realized_seller_roi'])}</span> / long <span id="avgRealizedBuyerRoi">{_fmt_pct(totals['avg_realized_buyer_roi'])}</span></div>
      <div class="sub2">avg ann. ROI: short <span id="avgRealizedSellerAnn">{_fmt_pct(totals['avg_realized_seller_ann_roi'])}</span> / long <span id="avgRealizedBuyerAnn">{_fmt_pct(totals['avg_realized_buyer_ann_roi'])}</span></div>
    </div>
  </div>
  <div class="updated" id="filterNote" style="display:none;">Totals above reflect only the positions currently passing the filter.</div>

  {chart_html}

  <h2>Open positions ({len(open_rows)})</h2>
  <div class="cards">
  {open_cards}
  </div>

  <h2>Closed positions ({len(closed_rows)})</h2>
  <div class="cards">
  {closed_cards}
  </div>

<script>
(function() {{
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
    var noFilter = minRoiRaw === '' && maxRoiRaw === '' && minPeRaw === '' && maxPeRaw === '';
    var minRoi = minRoiRaw === '' ? -Infinity : parseFloat(minRoiRaw);
    var maxRoi = maxRoiRaw === '' ? Infinity : parseFloat(maxRoiRaw);
    var minPe = minPeRaw === '' ? -Infinity : parseFloat(minPeRaw);
    var maxPe = maxPeRaw === '' ? Infinity : parseFloat(maxPeRaw);
    var cards = document.querySelectorAll('.card[data-ann-return]');

    // Pass 1: which cards individually clear BOTH the ROI range and the PE
    // range? (A range with both bounds blank is treated as "not filtering
    // on this dimension," so e.g. setting only PE still lets every ROI
    // value through.)
    var passing = [];
    cards.forEach(function(card) {{
      var roiRaw = card.getAttribute('data-ann-return');
      var roiVal = roiRaw === '' ? null : parseFloat(roiRaw);
      var roiOk = (minRoiRaw === '' && maxRoiRaw === '')
        || (roiVal !== null && !isNaN(roiVal) && roiVal >= minRoi && roiVal <= maxRoi);

      var peRaw = card.getAttribute('data-pe');
      var peVal = peRaw === '' ? null : parseFloat(peRaw);
      var peOk = (minPeRaw === '' && maxPeRaw === '')
        || (peVal !== null && !isNaN(peVal) && peVal >= minPe && peVal <= maxPe);

      if (noFilter || (roiOk && peOk)) {{
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

    var shown = 0;
    var openVisible = [];
    var closedVisible = [];
    cards.forEach(function(card) {{
      var visible = selectedSet.has(card);
      card.style.display = visible ? '' : 'none';
      if (visible) {{
        shown++;
        (card.getAttribute('data-kind') === 'open' ? openVisible : closedVisible).push(card);
      }}
    }});
    var countEl = document.getElementById('filterCount');
    if (countEl) countEl.textContent = shown + ' of ' + cards.length + ' shown';

    // Recompute every total/average from only the currently-visible cards -
    // same sum/average math the Python side uses, just run over a subset.
    setMoney('totalActualSeller', 'totalActualSellerAmt', sumAttr(openVisible, 'data-norm-as'));
    setMoney('totalActualBuyer', 'totalActualBuyerAmt', sumAttr(openVisible, 'data-norm-ab'));
    var midSellerVal = sumAttr(openVisible, 'data-norm-ms');
    var midBuyerVal = sumAttr(openVisible, 'data-norm-mb');
    var midSellerEl = document.getElementById('totalActualSellerMid');
    var midBuyerEl = document.getElementById('totalActualBuyerMid');
    if (midSellerEl) {{ midSellerEl.textContent = fmtMoneyParen(midSellerVal); midSellerEl.className = pnlClass(midSellerVal); }}
    if (midBuyerEl) {{ midBuyerEl.textContent = fmtMoneyParen(midBuyerVal); midBuyerEl.className = pnlClass(midBuyerVal); }}
    setPct('avgActualSellerRoi', avgAttr(openVisible, 'data-roi-as'));
    setPct('avgActualBuyerRoi', avgAttr(openVisible, 'data-roi-ab'));
    setPct('avgActualSellerAnn', avgAttr(openVisible, 'data-ann-as'));
    setPct('avgActualBuyerAnn', avgAttr(openVisible, 'data-ann-ab'));

    setMoney('totalRealizedSeller', 'totalRealizedSellerAmt', sumAttr(closedVisible, 'data-norm-rs'));
    setMoney('totalRealizedBuyer', 'totalRealizedBuyerAmt', sumAttr(closedVisible, 'data-norm-rb'));
    setPct('avgRealizedSellerRoi', avgAttr(closedVisible, 'data-roi-rs'));
    setPct('avgRealizedBuyerRoi', avgAttr(closedVisible, 'data-roi-rb'));
    setPct('avgRealizedSellerAnn', avgAttr(closedVisible, 'data-ann-rs'));
    setPct('avgRealizedBuyerAnn', avgAttr(closedVisible, 'data-ann-rb'));

    var openCountEl = document.getElementById('openCount');
    if (openCountEl) openCountEl.textContent = openVisible.length;
    var realizedCountEl = document.getElementById('realizedCount');
    if (realizedCountEl) realizedCountEl.textContent = closedVisible.length;

    var noteEl = document.getElementById('filterNote');
    if (noteEl) noteEl.style.display = noFilter ? 'none' : '';

    try {{
      localStorage.setItem('csp_filter_min_roi', minRoiRaw);
      localStorage.setItem('csp_filter_max_roi', maxRoiRaw);
      localStorage.setItem('csp_filter_min_pe', minPeRaw);
      localStorage.setItem('csp_filter_max_pe', maxPeRaw);
    }} catch (e) {{}}
  }}

  var btn = document.getElementById('applyFilter');
  if (btn) btn.addEventListener('click', applyFilter);
  ['minRoi', 'maxRoi', 'minPe', 'maxPe'].forEach(function(id) {{
    var el = document.getElementById(id);
    if (el) el.addEventListener('keydown', function(e) {{ if (e.key === 'Enter') applyFilter(); }});
  }});

  try {{
    var saved = {{
      minRoi: localStorage.getItem('csp_filter_min_roi'),
      maxRoi: localStorage.getItem('csp_filter_max_roi'),
      minPe: localStorage.getItem('csp_filter_min_pe'),
      maxPe: localStorage.getItem('csp_filter_max_pe')
    }};
    Object.keys(saved).forEach(function(id) {{
      if (saved[id]) document.getElementById(id).value = saved[id];
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


def build_summary(positions, today):
    open_rows = []
    open_roi_fict = []    # (seller_roi, buyer_roi, ann_seller_roi, ann_buyer_roi) per open position
    open_roi_actual = []  # same, for the "actual" (live requote) side
    open_norm_mid = []    # (norm_seller_mid, norm_buyer_mid) per open position
    for p in positions:
        exp_date = datetime.strptime(p["expiration"], "%Y-%m-%d").date()
        if exp_date < today:
            continue  # expired - handled by settle_expired_positions() instead
        days_held = (today - datetime.strptime(p["added_date"], "%Y-%m-%d").date()).days
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
        # the stock price. None on either leg if no live quote exists (an
        # illiquid contract) - no silent fallback, so as not to blur the two.
        current_bid, current_ask = get_yahoo_quote(p["symbol"], p["expiration"], p["strike"])
        actual_seller_pnl, actual_buyer_pnl = calc_actual_close_pnl(p["bid"], p["ask"], current_bid, current_ask)
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
        # put is already profitable on pure intrinsic value alone, that
        # guaranteed value is more relevant than a market mid-price guess -
        # substitute it in here (the aggregate total stays labeled "mid" for
        # simplicity even though some positions' contribution is really an
        # exercise value; per-card display relabels those specifically to
        # "exe" so it's clear what they actually represent).
        mid_seller_pnl, mid_buyer_pnl = calc_mid_close_pnl(p["bid"], p["ask"], current_bid, current_ask)
        mid_norm_seller, mid_norm_buyer = normalize_pnl(mid_seller_pnl, mid_buyer_pnl, p["strike"], p["ask"])
        buyer_mid_is_exercise = fict_buyer_pnl is not None and fict_buyer_pnl > 0
        if buyer_mid_is_exercise:
            mid_buyer_pnl = fict_buyer_pnl
            mid_norm_buyer = fict_norm_buyer
        open_norm_mid.append((mid_norm_seller, mid_norm_buyer))

        open_rows.append({
            "SYMBOL": p["symbol"],
            "STRIKE": p["strike"],
            "EXPIRATION": p["expiration"],
            "DAYS LEFT": (exp_date - today).days,
            "ENTRY STOCK PRICE": p["entry_stock_px"],
            "CURRENT STOCK PRICE": current_px,
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
        closed_rows.append({
            "SYMBOL": p["symbol"],
            "STRIKE": p["strike"],
            "EXPIRATION": p["expiration"],
            "ENTRY STOCK PRICE": p["entry_stock_px"],
            "FINAL STOCK PRICE": p["final_stock_px"],
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
        "settled_count": len(settled),
        "png_path": png_path,
    }
    html_path = generate_html_summary(open_rows, closed_rows, totals, today)
    totals["html_path"] = html_path

    return open_rows, closed_rows, totals


def main():
    ensure_deps()
    today = date.today()

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

    if ensure_pe_at_entry(positions):
        save_positions(positions)

    candidates = pick_new_candidates(barchart_rows, positions, today)
    if not candidates:
        print("\n  All of Barchart's top candidates are already open positions - nothing new to add.")
    else:
        print(f"\n  Adding {len(candidates)} new candidate(s):")
        for candidate in candidates:
            print(f"    {candidate['symbol']} ${candidate['strike']}P exp {candidate['expiration']} "
                  f"(barchart bid {candidate['barchart_bid']:.2f}, annualized return "
                  f"{candidate.get('potential_return_annual_pct') or 0:.1f}%)")
            position = add_new_position(candidate, today)
            bid_source = "approx (barchart)" if position["bid_is_approx"] else "yahoo"
            ask_source = "approx (bid x 1.2)" if position["ask_is_approx"] else "yahoo"
            print(f"      bid: {position['bid']:.2f} ({bid_source})   ask: {position['ask']:.2f} ({ask_source})")
            positions.append(position)
            save_positions(positions)
            ann_return = candidate.get("potential_return_annual_pct") or 0
            if ann_return >= DISCORD_NOTIFY_MIN_ANN_RETURN_PCT:
                pe_text = f"{position['pe_at_entry']:.1f}" if position.get("pe_at_entry") is not None else "n/a"
                mid_entry = round((position["bid"] + position["ask"]) / 2, 2)
                notify_discord(
                    f"**New CSP candidate: {position['symbol']} ${position['strike']:g}P exp {position['expiration']}**\n"
                    f"Barchart ann. return: {ann_return:.1f}% "
                    f"· PE: {pe_text} · Entry stock px {position['entry_stock_px']:.2f}\n"
                    f"Bid {position['bid']:.2f} ({bid_source})\n"
                    f"```diff\n+ Ask {position['ask']:.2f} ({ask_source})  (mid, buy: {mid_entry:.2f})\n```\n"
                    f"<{SUMMARY_HTML_URL}>"
                )

    if settle_expired_positions(positions, today):
        save_positions(positions)

    print("\n-- Rebuilding summary for all open positions -----------------------------")
    open_rows, closed_rows, totals = build_summary(positions, today)
    if not open_rows and not totals["settled_count"]:
        print("  No positions to summarize.")
        return

    if notify_expiration_reminders(positions, open_rows, today):
        save_positions(positions)

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
