#!/usr/bin/env python3
"""Single-ticker deep-dive report.

Usage:
    FINSKILLS_API_KEY=... python scripts/snapshot.py AAPL
"""
import sys
from concurrent.futures import ThreadPoolExecutor
from finskills_client import FinskillsClient, FinskillsError


def safe(fn, *a, **kw):
    try:
        return fn(*a, **kw)
    except FinskillsError as e:
        return {"_error": str(e)}


def main(symbol: str) -> int:
    fs = FinskillsClient()
    with ThreadPoolExecutor(max_workers=8) as ex:
        f_quote   = ex.submit(safe, fs.stock_quote, symbol)
        f_profile = ex.submit(safe, fs.stock_profile, symbol)
        f_consen  = ex.submit(safe, fs.analyst_rating_summary, symbol)
        f_insider = ex.submit(safe, fs.sec_insider_summary, symbol)
        f_congress= ex.submit(safe, fs.congress_trades, symbol=symbol, limit=10)
        f_news    = ex.submit(safe, fs.news_by_symbol, symbol, 5)
        f_earn    = ex.submit(safe, fs.stock_earnings, symbol)

    quote   = f_quote.result()
    profile = f_profile.result()
    consen  = f_consen.result()
    insider = f_insider.result()
    congress= f_congress.result()
    news    = f_news.result()
    earnings= f_earn.result()

    print(f"# {symbol} — {profile.get('name', symbol) if isinstance(profile, dict) else symbol}\n")
    if isinstance(quote, dict) and "_error" not in quote:
        price = quote.get("price") or quote.get("regularMarketPrice")
        chg = quote.get("changePercent") or quote.get("regularMarketChangePercent") or 0
        mc = quote.get("marketCap")
        print(f"**Price**: ${price:,.2f}  ({chg:+.2f}%)   |   **Market Cap**: ${mc:,.0f}" if mc else f"**Price**: ${price:,.2f}  ({chg:+.2f}%)")
    if isinstance(profile, dict) and "_error" not in profile:
        print(f"**Sector**: {profile.get('sector', '-')}   |   **Industry**: {profile.get('industry', '-')}")
        if profile.get("description"):
            print(f"\n> {profile['description'][:280]}…")

    print("\n## Analyst Consensus")
    if isinstance(consen, dict) and "_error" not in consen:
        r = consen.get("ratings", {})
        print(f"- Total: {sum(r.values()) if r else 'n/a'}  (SB {r.get('strongBuy', 0)} / B {r.get('buy', 0)} / H {r.get('hold', 0)} / S {r.get('sell', 0)} / SS {r.get('strongSell', 0)})")
        print(f"- Consensus: **{consen.get('consensus', 'n/a')}**, avg target ${consen.get('averageTarget', 0):,.2f}")
    else:
        print(consen)

    print("\n## Insider 90d Net")
    print(insider if not isinstance(insider, dict) or "_error" in insider else insider)

    print("\n## Congress Trades (last 10)")
    if isinstance(congress, list):
        for t in congress[:10]:
            print(f"- {t.get('transactionDate','?')}  {t.get('politician','?')} ({t.get('chamber','?')}): {t.get('transactionType','?')} {t.get('amount','?')}")
    else:
        print(congress)

    print("\n## Earnings (recent)")
    if isinstance(earnings, dict) and "history" in earnings:
        for e in earnings["history"][:4]:
            print(f"- {e.get('date','?')}: EPS {e.get('epsActual','?')} vs est {e.get('epsEstimate','?')}")
    else:
        print(earnings)

    print("\n## Latest News")
    if isinstance(news, list):
        for n in news[:5]:
            print(f"- [{n.get('source','?')}] {n.get('title','')}  ({n.get('publishedAt','')})")
    else:
        print(news)

    print("\n_Data: finskills.net. Not investment advice._")
    return 0


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("usage: snapshot.py SYMBOL", file=sys.stderr)
        sys.exit(2)
    sys.exit(main(sys.argv[1].upper()))
