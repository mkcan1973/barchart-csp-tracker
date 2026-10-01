# Barchart CSP Tracker

Tracks high-annualized-return cash-secured put candidates from Barchart's free
naked-puts screener, priced via Yahoo Finance (yfinance). No brokerage
account or API required.

Runs automatically on weekdays via GitHub Actions (see
`.github/workflows/run.yml`) - the script itself skips US market holidays.
Results are committed back to this repo on every run:

- `index.html` - mobile-friendly summary (served via GitHub Pages)
- `barchart_csp_summary.csv` - full detail for spreadsheets
- `barchart_csp_realized_pnl.png` - cumulative realized P&L chart
- `barchart_csp_positions.json` - the underlying tracked position data

To run manually: `python barchart_csp_tracker.py` (installs its own
dependencies on first run).
