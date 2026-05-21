#!/usr/bin/env python3
"""Print live quotes for one or more symbols.

Usage:
    FINSKILLS_API_KEY=... python scripts/quote.py AAPL TSLA NVDA
"""
import sys
from finskills_client import FinskillsClient


def main(symbols: list[str]) -> int:
    if not symbols:
        print("usage: quote.py SYM [SYM ...]", file=sys.stderr)
        return 2
    fs = FinskillsClient()
    if len(symbols) == 1:
        rows = [fs.stock_quote(symbols[0])]
    else:
        data = fs.stock_quotes(symbols)
        rows = data if isinstance(data, list) else data.get("quotes", [])

    print(f"{'Symbol':<8}{'Price':>12}{'Chg':>10}{'Chg%':>9}  {'Volume':>14}  {'Mkt Cap':>16}")
    print("-" * 72)
    for q in rows:
        sym = q.get("symbol", "")
        price = q.get("price") or q.get("regularMarketPrice") or 0
        chg = q.get("change") or q.get("regularMarketChange") or 0
        chgp = q.get("changePercent") or q.get("regularMarketChangePercent") or 0
        vol = q.get("volume") or q.get("regularMarketVolume") or 0
        mc = q.get("marketCap") or 0
        print(f"{sym:<8}{price:>12,.2f}{chg:>10,.2f}{chgp:>8.2f}%  {vol:>14,}  {mc:>16,.0f}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
