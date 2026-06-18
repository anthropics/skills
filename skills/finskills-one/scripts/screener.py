#!/usr/bin/env python3
"""Market screener / mover dashboard.

Usage:
    FINSKILLS_API_KEY=... python scripts/screener.py --top-gainers 25
    FINSKILLS_API_KEY=... python scripts/screener.py --top-losers 25
    FINSKILLS_API_KEY=... python scripts/screener.py --most-active 25
    FINSKILLS_API_KEY=... python scripts/screener.py --briefing
"""
import argparse
import sys
from concurrent.futures import ThreadPoolExecutor
from finskills_client import FinskillsClient


def fmt_rows(rows, label):
    print(f"\n## {label}")
    print(f"{'Symbol':<8}{'Price':>10}{'Chg%':>10}{'Volume':>14}")
    for r in rows[:25]:
        sym = r.get("symbol", "")
        p = r.get("price") or r.get("regularMarketPrice") or 0
        cp = r.get("changePercent") or r.get("regularMarketChangePercent") or 0
        v = r.get("volume") or r.get("regularMarketVolume") or 0
        print(f"{sym:<8}{p:>10,.2f}{cp:>9.2f}%{v:>14,}")


def briefing(fs: FinskillsClient):
    with ThreadPoolExecutor(max_workers=8) as ex:
        futs = {
            "summary":     ex.submit(fs.market_summary),
            "sectors":     ex.submit(fs.market_sectors, True),
            "fear_greed":  ex.submit(fs.market_fear_greed, True),
            "vix":         ex.submit(fs.market_vix),
            "gainers":     ex.submit(fs.market_top_gainers, 5),
            "losers":      ex.submit(fs.market_top_losers, 5),
            "treasury":    ex.submit(fs.macro_treasury_rates),
            "news":        ex.submit(fs.market_news, 5, True),
        }
        out = {k: f.result() for k, f in futs.items()}

    print("# Daily Market Briefing\n")

    s = out["summary"]
    if isinstance(s, dict):
        print("## Major Indices")
        for idx in s.get("indices", []) or []:
            print(f"- {idx.get('symbol')}: {idx.get('price'):,.2f} ({idx.get('changePercent', 0):+.2f}%)")

    print("\n## Sentiment")
    fg = out["fear_greed"]
    vix = out["vix"]
    if isinstance(fg, dict):
        print(f"- Fear & Greed: **{fg.get('value','?')}** ({fg.get('classification','?')})")
    if isinstance(vix, dict):
        print(f"- VIX: {vix.get('price', vix.get('value','?'))}")

    print("\n## Sectors")
    for sec in out["sectors"] if isinstance(out["sectors"], list) else []:
        print(f"- {sec.get('name','?'):<25} {sec.get('changePercent', 0):+.2f}%")

    print("\n## Treasury Yield Curve")
    tr = out["treasury"]
    if isinstance(tr, list) and tr:
        latest = tr[0]
        keys = ["1M","3M","6M","1Y","2Y","5Y","10Y","30Y"]
        print(" | ".join(f"{k}: {latest.get(k,'?')}" for k in keys if k in latest))

    fmt_rows(out["gainers"] if isinstance(out["gainers"], list) else [], "Top Gainers (5)")
    fmt_rows(out["losers"] if isinstance(out["losers"], list) else [], "Top Losers (5)")

    print("\n## Headlines")
    for n in (out["news"] if isinstance(out["news"], list) else [])[:5]:
        print(f"- [{n.get('source','?')}] {n.get('title','')}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--top-gainers", type=int, dest="gainers")
    ap.add_argument("--top-losers", type=int, dest="losers")
    ap.add_argument("--most-active", type=int, dest="active")
    ap.add_argument("--briefing", action="store_true")
    args = ap.parse_args()

    fs = FinskillsClient()

    if args.briefing:
        briefing(fs)
        return 0
    if args.gainers:
        fmt_rows(fs.market_top_gainers(args.gainers), f"Top {args.gainers} Gainers")
    if args.losers:
        fmt_rows(fs.market_top_losers(args.losers), f"Top {args.losers} Losers")
    if args.active:
        fmt_rows(fs.market_most_active(args.active), f"Top {args.active} Most Active")
    if not (args.gainers or args.losers or args.active or args.briefing):
        ap.print_help()
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
