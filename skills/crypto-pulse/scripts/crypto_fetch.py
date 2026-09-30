#!/usr/bin/env python3
"""Crypto market data fetcher. CoinGecko + DexScreener + Fear & Greed."""

import sys
import json
import urllib.request
import urllib.parse
import argparse
import threading
import time
from datetime import datetime

CG_BASE = "https://api.coingecko.com/api/v3"
DEX_BASE = "https://api.dexscreener.com/latest/dex"
FNG_URL = "https://api.alternative.me/fng/?limit=7"

HEADERS = {"User-Agent": "crypto-pulse/1.0", "Accept": "application/json"}

SYMBOL_TO_ID = {
    "BTC": "bitcoin", "ETH": "ethereum", "SOL": "solana", "BNB": "binancecoin",
    "XRP": "ripple", "USDC": "usd-coin", "USDT": "tether", "DOGE": "dogecoin",
    "ADA": "cardano", "AVAX": "avalanche-2", "DOT": "polkadot", "MATIC": "matic-network",
    "LINK": "chainlink", "UNI": "uniswap", "ATOM": "cosmos", "LTC": "litecoin",
    "BCH": "bitcoin-cash", "NEAR": "near", "APT": "aptos", "ARB": "arbitrum",
    "OP": "optimism", "SUI": "sui", "TRX": "tron", "SHIB": "shiba-inu",
    "TON": "the-open-network", "PEPE": "pepe"
}


def fetch_json(url, retries=2, delay=10):
    for attempt in range(retries):
        try:
            req = urllib.request.Request(url, headers=HEADERS)
            with urllib.request.urlopen(req, timeout=15) as resp:
                return json.loads(resp.read().decode('utf-8'))
        except urllib.error.HTTPError as e:
            if e.code == 429 and attempt < retries - 1:
                time.sleep(delay)
                continue
            return {"_error": f"HTTP {e.code}: {e.reason}"}
        except Exception as e:
            return {"_error": str(e)}
    return {"_error": "max retries exceeded"}


def resolve_coin_id(symbol_or_name):
    """Resolve ticker symbol to CoinGecko ID."""
    upper = symbol_or_name.upper()
    if upper in SYMBOL_TO_ID:
        return SYMBOL_TO_ID[upper]

    # Try search API
    encoded = urllib.parse.quote(symbol_or_name)
    data = fetch_json(f"{CG_BASE}/search?query={encoded}")
    coins = data.get("coins", [])
    if coins:
        return coins[0]["id"]
    return symbol_or_name.lower()


def fetch_markets(ids=None, top_n=20, vs_currency="usd"):
    if ids:
        ids_str = ",".join(ids)
        url = f"{CG_BASE}/coins/markets?vs_currency={vs_currency}&ids={ids_str}&order=market_cap_desc&sparkline=false&price_change_percentage=1h,24h,7d,30d"
    else:
        url = f"{CG_BASE}/coins/markets?vs_currency={vs_currency}&order=market_cap_desc&per_page={top_n}&page=1&sparkline=false&price_change_percentage=1h,24h,7d"
    return fetch_json(url)


def fetch_trending():
    return fetch_json(f"{CG_BASE}/search/trending")


def fetch_global():
    return fetch_json(f"{CG_BASE}/global")


def fetch_coin_detail(coin_id):
    url = f"{CG_BASE}/coins/{coin_id}?localization=false&tickers=false&market_data=true&community_data=false&developer_data=false"
    return fetch_json(url)


def fetch_fear_greed():
    return fetch_json(FNG_URL)


def fetch_dex_pairs(query):
    encoded = urllib.parse.quote(query)
    return fetch_json(f"{DEX_BASE}/search?q={encoded}")


def fmt(v, prefix="$", decimals=2, suffix=""):
    if v is None:
        return "N/A"
    if isinstance(v, str):
        return v
    if abs(v) >= 1e12:
        return f"{prefix}{v/1e12:.2f}T{suffix}"
    if abs(v) >= 1e9:
        return f"{prefix}{v/1e9:.1f}B{suffix}"
    if abs(v) >= 1e6:
        return f"{prefix}{v/1e6:.1f}M{suffix}"
    if abs(v) >= 1000:
        return f"{prefix}{v:,.{decimals}f}{suffix}"
    return f"{prefix}{v:.{decimals}f}{suffix}"


def pct(v):
    if v is None:
        return "N/A"
    arrow = "▲" if v > 0 else "▼"
    return f"{arrow}{abs(v):.2f}%"


def print_market_overview(markets_data, global_data, fng_data, trending_data):
    now = datetime.utcnow().strftime("%Y-%m-%d %H:%M UTC")
    print(f"# Crypto Pulse")
    print(f"*{now}*\n")

    # Fear & Greed
    fng_entries = fng_data.get("data", [])
    if fng_entries:
        curr = fng_entries[0]
        print(f"**Fear & Greed:** {curr.get('value')}/100 — {curr.get('value_classification', '')}\n")

    # Global stats
    gdata = global_data.get("data", {})
    if gdata:
        mcap = gdata.get("total_market_cap", {}).get("usd")
        vol = gdata.get("total_volume", {}).get("usd")
        btc_dom = gdata.get("market_cap_percentage", {}).get("btc")
        eth_dom = gdata.get("market_cap_percentage", {}).get("eth")
        print("## Global")
        print(f"- Market Cap: {fmt(mcap)}")
        print(f"- 24h Volume: {fmt(vol)}")
        print(f"- BTC Dominance: {btc_dom:.1f}%" if btc_dom else "")
        print(f"- ETH Dominance: {eth_dom:.1f}%" if eth_dom else "")
        print()

    # Markets table
    if isinstance(markets_data, list) and markets_data:
        print("## Top Coins by Market Cap")
        print("| # | Coin | Price | 1h | 24h | 7d | Mkt Cap |")
        print("|---|------|-------|----|----|-----|---------|")
        for c in markets_data:
            rank = c.get("market_cap_rank", "?")
            name = c.get("name", "")
            sym = c.get("symbol", "").upper()
            price = fmt(c.get("current_price"))
            ch1h = pct(c.get("price_change_percentage_1h_in_currency"))
            ch24 = pct(c.get("price_change_percentage_24h"))
            ch7d = pct(c.get("price_change_percentage_7d_in_currency"))
            mcap = fmt(c.get("market_cap"))
            print(f"| {rank} | {name} ({sym}) | {price} | {ch1h} | {ch24} | {ch7d} | {mcap} |")
        print()

    # Trending
    trend_coins = trending_data.get("coins", [])
    if trend_coins:
        print("## Trending Now (CoinGecko)")
        for i, item in enumerate(trend_coins[:7], 1):
            coin = item.get("item", {})
            print(f"{i}. **{coin.get('name', '')}** ({coin.get('symbol', '').upper()}) — Rank #{coin.get('market_cap_rank', 'N/A')}")
        print()


def print_coin_detail(coin_id, data, dex_data=None):
    if "_error" in data:
        print(f"Error fetching {coin_id}: {data['_error']}")
        return

    md = data.get("market_data", {})
    name = data.get("name", coin_id)
    sym = data.get("symbol", "").upper()

    print(f"# {name} ({sym})")
    print(f"*Rank: #{md.get('market_cap_rank', 'N/A')} | {datetime.utcnow().strftime('%Y-%m-%d %H:%M UTC')}*\n")

    usd_price = md.get("current_price", {}).get("usd")
    print(f"**Price:** {fmt(usd_price)}")
    print(f"**Market Cap:** {fmt(md.get('market_cap', {}).get('usd'))} (#{md.get('market_cap_rank', 'N/A')})")
    print(f"**24h Volume:** {fmt(md.get('total_volume', {}).get('usd'))}")

    circ = md.get("circulating_supply")
    total = md.get("total_supply")
    if circ and total:
        print(f"**Supply:** {circ:,.0f} / {total:,.0f} ({circ/total*100:.1f}% issued)")
    print()

    print("## Price Changes")
    for period in ["1h", "24h", "7d", "14d", "30d", "1y"]:
        key = f"price_change_percentage_{period}_in_currency"
        alt_key = f"price_change_percentage_{period}"
        val = md.get(key, {}).get("usd") if isinstance(md.get(key, {}), dict) else md.get(alt_key)
        if val is not None:
            print(f"- {period}: {pct(val)}")
    print()

    ath = md.get("ath", {}).get("usd")
    ath_date = md.get("ath_date", {}).get("usd", "")[:10]
    ath_change = md.get("ath_change_percentage", {}).get("usd")
    if ath:
        print(f"**ATH:** {fmt(ath)} ({ath_date}) | {pct(ath_change)} from ATH\n")

    # Categories
    categories = data.get("categories", [])
    if categories:
        print(f"**Categories:** {', '.join(categories[:5])}\n")

    # Description
    desc = data.get("description", {}).get("en", "")
    if desc:
        clean = desc.replace("<a href=", "").replace("</a>", "").replace("<br>", " ")[:400]
        print(f"**About:** {clean}...\n")


def main():
    parser = argparse.ArgumentParser(description="Crypto market data fetcher")
    parser.add_argument("--mode", default="overview", choices=["overview", "coin", "trending", "dex"])
    parser.add_argument("--coins", help="Comma-separated coin symbols or IDs")
    parser.add_argument("--top", type=int, default=20)
    parser.add_argument("--query", help="Search query for DEX or coin search")
    parser.add_argument("--format", default="markdown", choices=["markdown", "json"])
    args = parser.parse_args()

    if args.mode == "overview":
        results = {}
        threads = [
            threading.Thread(target=lambda: results.update({"markets": fetch_markets(top_n=args.top)})),
            threading.Thread(target=lambda: results.update({"global": fetch_global()})),
            threading.Thread(target=lambda: results.update({"fng": fetch_fear_greed()})),
            threading.Thread(target=lambda: results.update({"trending": fetch_trending()})),
        ]
        for t in threads:
            t.start()
        for t in threads:
            t.join(timeout=20)

        if args.format == "json":
            print(json.dumps(results, indent=2))
        else:
            print_market_overview(
                results.get("markets", []),
                results.get("global", {}),
                results.get("fng", {}),
                results.get("trending", {})
            )

    elif args.mode == "coin":
        if not args.coins:
            print("Error: --coins required for coin mode", file=sys.stderr)
            sys.exit(1)

        symbols = [s.strip() for s in args.coins.split(",")]
        for sym in symbols:
            coin_id = resolve_coin_id(sym)
            data = fetch_coin_detail(coin_id)
            dex = fetch_dex_pairs(sym) if args.format == "markdown" else None
            if args.format == "json":
                print(json.dumps(data, indent=2))
            else:
                print_coin_detail(coin_id, data, dex)

    elif args.mode == "trending":
        data = fetch_trending()
        if args.format == "json":
            print(json.dumps(data, indent=2))
        else:
            coins = data.get("coins", [])
            print("# Trending on CoinGecko\n")
            for i, item in enumerate(coins, 1):
                c = item.get("item", {})
                print(f"{i}. **{c.get('name')}** ({c.get('symbol', '').upper()}) — Rank #{c.get('market_cap_rank', 'N/A')}")

    elif args.mode == "dex":
        if not args.query:
            print("Error: --query required for dex mode", file=sys.stderr)
            sys.exit(1)
        data = fetch_dex_pairs(args.query)
        pairs = data.get("pairs", [])
        if args.format == "json":
            print(json.dumps(pairs[:10], indent=2))
        else:
            print(f"# DEX Pairs: {args.query}\n")
            for p in pairs[:10]:
                print(f"**{p.get('baseToken', {}).get('symbol','?')}/{p.get('quoteToken', {}).get('symbol','?')}** on {p.get('dexId','?')}")
                print(f"  Price: ${p.get('priceUsd', 'N/A')} | Liquidity: {fmt(p.get('liquidity', {}).get('usd'))} | 24h: {pct(p.get('priceChange', {}).get('h24'))}")
                print()


if __name__ == "__main__":
    main()
