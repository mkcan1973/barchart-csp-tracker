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
     ones - with entry vs. current stock price and unrealized P&L for both
     the CSP-seller and long-put-buyer side, computed off intrinsic value at
     the CURRENT stock price (a mark-to-market approximation, not a real
     option repricing - there's no live premium source here to do better
     without IBKR, which this script deliberately avoids).

Usage:
  python barchart_csp_tracker.py
"""

import subprocess
import sys
import time
import json
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
    try:
        return float(yf.Ticker(symbol).fast_info["last_price"])
    except Exception:
        return None


def get_price_at(symbol, target_date_str):
    """First available close on/after target_date - used to settle a
    position once its expiration has passed."""
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


def is_already_open(positions, symbol, today):
    """True if this SYMBOL has any unexpired tracked position, regardless of
    strike/expiration - one open name at a time, not one per contract."""
    for p in positions:
        if (p["symbol"] == symbol
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


def normalize_pnl(seller_pnl, buyer_pnl, strike, ask):
    """Scale a position's actual-dollar PnL to what it would've been sized at
    NORMALIZED_RISK_USD capital at risk, so positions on different-priced
    stocks (and therefore wildly different position sizes) are comparable."""
    seller_risk = strike * 100
    buyer_risk = ask * 100
    norm_seller = round(seller_pnl * (NORMALIZED_RISK_USD / seller_risk), 2) if seller_risk > 0 else None
    norm_buyer = round(buyer_pnl * (NORMALIZED_RISK_USD / buyer_risk), 2) if buyer_risk > 0 else None
    return norm_seller, norm_buyer


def calc_roi_pct(pnl, risk):
    return round(pnl / risk * 100, 2) if risk > 0 else None


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
    """Every ranked candidate whose symbol isn't already an open position -
    no daily cap. If two rows share a symbol in the same ranked list, only
    the higher-ranked one is picked (still one open position per symbol)."""
    picked = []
    staged_symbols = set()
    for row in barchart_rows:
        if is_already_open(positions, row["symbol"], today) or row["symbol"] in staged_symbols:
            continue
        picked.append(row)
        staged_symbols.add(row["symbol"])
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


def generate_html_summary(open_rows, closed_rows, totals, today):
    """Single self-contained HTML file - a card per position (readable on a
    phone, unlike the 20+ column CSV) plus the totals and the realized P&L
    chart if one exists. No build step, no external assets - just open it in
    a browser (or serve it as-is via GitHub Pages)."""

    def position_card(r, closed):
        norm_seller_key = f"NORM P/L IF SOLD (${NORMALIZED_RISK_USD:.0f} risk)"
        norm_buyer_key = f"NORM P/L IF BOUGHT (${NORMALIZED_RISK_USD:.0f} risk)"
        seller_pnl = r["REALIZED P/L IF SOLD (CSP)"] if closed else r["UNREALIZED P/L IF SOLD (CSP)"]
        buyer_pnl = r["REALIZED P/L IF BOUGHT (long put)"] if closed else r["UNREALIZED P/L IF BOUGHT (long put)"]
        price_line = (f"Final {r['FINAL STOCK PRICE']:.2f}" if closed
                      else f"Now {r['CURRENT STOCK PRICE']:.2f}" if r["CURRENT STOCK PRICE"] is not None else "Now --")
        days_line = f"Settled {r['SETTLED AT']}" if closed else f"{r['DAYS LEFT']}d left"
        return f"""
        <div class="card">
          <div class="card-head">
            <span class="sym">{_html_escape(r['SYMBOL'])}</span>
            <span class="strike">${r['STRIKE']:g}P</span>
            <span class="exp">{r['EXPIRATION']}</span>
          </div>
          <div class="sub">{days_line} &middot; Entry {r['ENTRY STOCK PRICE']:.2f} &middot; {price_line}
            &middot; bid {r['BID']:.2f}/{r['BID SOURCE']} &middot; ask {r['ASK']:.2f}/{r['ASK SOURCE']}</div>
          <div class="sub">Barchart ann. return at selection: {_fmt_pct(r.get('BARCHART ANNUALIZED RETURN % (at selection)'))}</div>
          <div class="grid2">
            <div class="box">
              <div class="label">SHORT (sold CSP)</div>
              <div class="val {_pnl_class(seller_pnl)}">{_fmt_money(seller_pnl)}</div>
              <div class="sub2">ROI {_fmt_pct(r['ROI % IF SOLD (CSP)'])} &middot; ann {_fmt_pct(r['ANNUALIZED ROI % IF SOLD (CSP)'])}</div>
              <div class="sub2">norm ({NORMALIZED_RISK_USD:.0f} risk): {_fmt_money(r[norm_seller_key])}</div>
            </div>
            <div class="box">
              <div class="label">LONG (bought put)</div>
              <div class="val {_pnl_class(buyer_pnl)}">{_fmt_money(buyer_pnl)}</div>
              <div class="sub2">ROI {_fmt_pct(r['ROI % IF BOUGHT (long put)'])} &middot; ann {_fmt_pct(r['ANNUALIZED ROI % IF BOUGHT (long put)'])}</div>
              <div class="sub2">norm ({NORMALIZED_RISK_USD:.0f} risk): {_fmt_money(r[norm_buyer_key])}</div>
            </div>
          </div>
        </div>"""

    open_cards = "\n".join(position_card(r, closed=False) for r in open_rows) or '<p class="empty">No open positions.</p>'
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
  .grid2 {{ display: grid; grid-template-columns: 1fr 1fr; gap: 10px; margin-top: 10px; }}
  .box {{ background: #0f131b; border-radius: 8px; padding: 8px 10px; }}
  .label {{ font-size: 0.72rem; letter-spacing: 0.04em; color: #9aa4b2; }}
  .val {{ font-size: 1.15rem; font-weight: 700; }}
  .pos {{ color: #3ddc84; }}
  .neg {{ color: #ff6b6b; }}
  .empty {{ color: #9aa4b2; font-style: italic; }}
  .chart {{ width: 100%; height: auto; border-radius: 10px; margin-top: 10px; background: white; }}
  @media (prefers-color-scheme: light) {{
    body {{ background: #f5f6f8; color: #1a1d23; }}
    .totals .box, .card, .box {{ background: #ffffff; box-shadow: 0 1px 3px rgba(0,0,0,0.08); }}
    .label, .sub, .sub2, .updated, .card-head .exp, .card-head .strike {{ color: #6b7280; }}
  }}
</style>
</head>
<body>
  <h1>Barchart CSP Tracker</h1>
  <div class="updated">Last updated {today.isoformat()} &middot; {len(open_rows)} open &middot; {len(closed_rows)} closed</div>

  <div class="totals">
    <div class="box">
      <div class="label">UNREALIZED (open, normalized ${NORMALIZED_RISK_USD:.0f}/position)</div>
      <div class="val {_pnl_class(totals['unrealized_seller_total'])}">Short {_fmt_money(totals['unrealized_seller_total'])}</div>
      <div class="val {_pnl_class(totals['unrealized_buyer_total'])}">Long {_fmt_money(totals['unrealized_buyer_total'])}</div>
      <div class="sub2">avg ROI: short {_fmt_pct(totals['avg_unrealized_seller_roi'])} / long {_fmt_pct(totals['avg_unrealized_buyer_roi'])}</div>
      <div class="sub2">avg ann. ROI: short {_fmt_pct(totals['avg_unrealized_seller_ann_roi'])} / long {_fmt_pct(totals['avg_unrealized_buyer_ann_roi'])}</div>
    </div>
    <div class="box">
      <div class="label">REALIZED ({totals['settled_count']} settled, normalized ${NORMALIZED_RISK_USD:.0f}/position)</div>
      <div class="val {_pnl_class(totals['realized_seller_total'])}">Short {_fmt_money(totals['realized_seller_total'])}</div>
      <div class="val {_pnl_class(totals['realized_buyer_total'])}">Long {_fmt_money(totals['realized_buyer_total'])}</div>
      <div class="sub2">avg ROI: short {_fmt_pct(totals['avg_realized_seller_roi'])} / long {_fmt_pct(totals['avg_realized_buyer_roi'])}</div>
      <div class="sub2">avg ann. ROI: short {_fmt_pct(totals['avg_realized_seller_ann_roi'])} / long {_fmt_pct(totals['avg_realized_buyer_ann_roi'])}</div>
    </div>
  </div>

  {chart_html}

  <h2>Open positions ({len(open_rows)})</h2>
  <div class="cards">
  {open_cards}
  </div>

  <h2>Closed positions ({len(closed_rows)})</h2>
  <div class="cards">
  {closed_cards}
  </div>
</body>
</html>
"""
    SUMMARY_HTML.write_text(html, encoding="utf-8")
    return SUMMARY_HTML


def build_summary(positions, today):
    open_rows = []
    open_roi = []  # (seller_roi, buyer_roi, ann_seller_roi, ann_buyer_roi) per open position
    for p in positions:
        exp_date = datetime.strptime(p["expiration"], "%Y-%m-%d").date()
        if exp_date < today:
            continue  # expired - handled by settle_expired_positions() instead
        current_px = get_current_stock_price(p["symbol"])
        seller_pnl, buyer_pnl = (None, None)
        norm_seller, norm_buyer = (None, None)
        seller_roi = buyer_roi = ann_seller_roi = ann_buyer_roi = None
        if current_px is not None:
            seller_pnl, buyer_pnl = calc_pnl_at_price(p["strike"], p["bid"], p["ask"], current_px)
            norm_seller, norm_buyer = normalize_pnl(seller_pnl, buyer_pnl, p["strike"], p["ask"])
            seller_roi = calc_roi_pct(seller_pnl, p["strike"] * 100)
            buyer_roi = calc_roi_pct(buyer_pnl, p["ask"] * 100)
            days_held = (today - datetime.strptime(p["added_date"], "%Y-%m-%d").date()).days
            ann_seller_roi = annualize_roi_pct(seller_roi, days_held)
            ann_buyer_roi = annualize_roi_pct(buyer_roi, days_held)
        open_roi.append((seller_roi, buyer_roi, ann_seller_roi, ann_buyer_roi))
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
            "BID": p["bid"],
            "BID SOURCE": "approx (barchart)" if p["bid_is_approx"] else "yahoo",
            "ASK": p["ask"],
            "ASK SOURCE": "approx (bid x 1.2)" if p["ask_is_approx"] else "yahoo",
            "UNREALIZED P/L IF SOLD (CSP)": seller_pnl,
            "UNREALIZED P/L IF BOUGHT (long put)": buyer_pnl,
            f"NORM P/L IF SOLD (${NORMALIZED_RISK_USD:.0f} risk)": norm_seller,
            f"NORM P/L IF BOUGHT (${NORMALIZED_RISK_USD:.0f} risk)": norm_buyer,
            "ROI % IF SOLD (CSP)": seller_roi,
            "ROI % IF BOUGHT (long put)": buyer_roi,
            "ANNUALIZED ROI % IF SOLD (CSP)": ann_seller_roi,
            "ANNUALIZED ROI % IF BOUGHT (long put)": ann_buyer_roi,
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

    norm_seller_col = f"NORM P/L IF SOLD (${NORMALIZED_RISK_USD:.0f} risk)"
    norm_buyer_col = f"NORM P/L IF BOUGHT (${NORMALIZED_RISK_USD:.0f} risk)"

    unrealized_seller_total = round(sum(r[norm_seller_col] or 0 for r in open_rows), 2)
    unrealized_buyer_total = round(sum(r[norm_buyer_col] or 0 for r in open_rows), 2)
    realized_seller_total = cum_seller  # last row's cumulative == grand total
    realized_buyer_total = cum_buyer

    avg_unrealized_seller_roi = avg(r[0] for r in open_roi)
    avg_unrealized_buyer_roi = avg(r[1] for r in open_roi)
    avg_unrealized_seller_ann_roi = avg(r[2] for r in open_roi)
    avg_unrealized_buyer_ann_roi = avg(r[3] for r in open_roi)
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
            "SYMBOL": f"OPEN P/L - UNREALIZED (normalized to ${NORMALIZED_RISK_USD:.0f} risk each)",
            norm_seller_col: unrealized_seller_total,
            norm_buyer_col: unrealized_buyer_total,
            "ROI % IF SOLD (CSP)": avg_unrealized_seller_roi,
            "ROI % IF BOUGHT (long put)": avg_unrealized_buyer_roi,
            "ANNUALIZED ROI % IF SOLD (CSP)": avg_unrealized_seller_ann_roi,
            "ANNUALIZED ROI % IF BOUGHT (long put)": avg_unrealized_buyer_ann_roi,
        }]))
        sections.append(blank)

        sections.append(pd.DataFrame([{
            "SYMBOL": f"CLOSED P/L - REALIZED, {len(closed_rows)} settled (normalized to ${NORMALIZED_RISK_USD:.0f} risk each)",
            norm_seller_col: realized_seller_total,
            norm_buyer_col: realized_buyer_total,
            "ROI % IF SOLD (CSP)": avg_realized_seller_roi,
            "ROI % IF BOUGHT (long put)": avg_realized_buyer_roi,
            "ANNUALIZED ROI % IF SOLD (CSP)": avg_realized_seller_ann_roi,
            "ANNUALIZED ROI % IF BOUGHT (long put)": avg_realized_buyer_ann_roi,
        }]))

        combined = pd.concat(sections, ignore_index=True)
        combined.to_csv(SUMMARY_CSV, index=False)

    png_path = plot_realized_pnl(closed_rows)

    totals = {
        "unrealized_seller_total": unrealized_seller_total,
        "unrealized_buyer_total": unrealized_buyer_total,
        "realized_seller_total": realized_seller_total,
        "realized_buyer_total": realized_buyer_total,
        "avg_unrealized_seller_roi": avg_unrealized_seller_roi,
        "avg_unrealized_buyer_roi": avg_unrealized_buyer_roi,
        "avg_unrealized_seller_ann_roi": avg_unrealized_seller_ann_roi,
        "avg_unrealized_buyer_ann_roi": avg_unrealized_buyer_ann_roi,
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

    if settle_expired_positions(positions, today):
        save_positions(positions)

    print("\n-- Rebuilding summary for all open positions -----------------------------")
    open_rows, closed_rows, totals = build_summary(positions, today)
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

    print(f"\n  TOTAL UNREALIZED (open, normalized to ${NORMALIZED_RISK_USD:.0f} risk each): "
          f"sold {totals['unrealized_seller_total']:+.2f}  bought {totals['unrealized_buyer_total']:+.2f}")
    print(f"    avg ROI: sold {pct(totals['avg_unrealized_seller_roi'])}  bought {pct(totals['avg_unrealized_buyer_roi'])}"
          f"   |   avg annualized ROI: sold {pct(totals['avg_unrealized_seller_ann_roi'])}"
          f"  bought {pct(totals['avg_unrealized_buyer_ann_roi'])}")
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
