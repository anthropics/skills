#!/usr/bin/env python3
"""Multi-signal market data fetcher. Cross-source financial intelligence."""

import sys
import json
import urllib.request
import urllib.parse
import csv
import io
import argparse
import threading
from datetime import datetime


def fetch_json(url, headers=None, timeout=12):
    try:
        req = urllib.request.Request(url, headers=headers or {
            "User-Agent": "Mozilla/5.0 (market-oracle/1.0)",
            "Accept": "application/json"
        })
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            return json.loads(resp.read().decode('utf-8'))
    except Exception as e:
        return {"_error": str(e)}


def fetch_text(url, timeout=12):
    try:
        req = urllib.request.Request(url, headers={"User-Agent": "market-oracle/1.0"})
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            return resp.read().decode('utf-8')
    except Exception as e:
        return None


# --- CoinGecko ---
def fetch_crypto_markets(top_n=20, extra_ids=None):
    url = f"https://api.coingecko.com/api/v3/coins/markets?vs_currency=usd&order=market_cap_desc&per_page={top_n}&page=1&sparkline=false&price_change_percentage=24h,7d"
    data = fetch_json(url)
    if "_error" in data:
        return {"error": data["_error"], "data": []}

    coins = []
    for c in (data if isinstance(data, list) else []):
        coins.append({
            "id": c.get("id"),
            "symbol": c.get("symbol", "").upper(),
            "name": c.get("name"),
            "price": c.get("current_price"),
            "market_cap": c.get("market_cap"),
            "change_24h": c.get("price_change_percentage_24h"),
            "change_7d": c.get("price_change_percentage_7d_in_currency"),
            "volume_24h": c.get("total_volume"),
            "rank": c.get("market_cap_rank")
        })

    return {"data": coins, "timestamp": datetime.utcnow().isoformat()}


def fetch_fear_greed():
    url = "https://api.alternative.me/fng/?limit=2"
    data = fetch_json(url)
    if "_error" in data:
        return {"error": data["_error"]}

    entries = data.get("data", [])
    result = {}
    if entries:
        result["current"] = {
            "value": int(entries[0].get("value", 0)),
            "classification": entries[0].get("value_classification", ""),
            "timestamp": entries[0].get("timestamp", "")
        }
    if len(entries) > 1:
        result["yesterday"] = {
            "value": int(entries[1].get("value", 0)),
            "classification": entries[1].get("value_classification", "")
        }
    return result


# --- Yahoo Finance (unofficial) ---
EQUITY_TICKERS = {
    "SPY": "S&P 500 ETF",
    "QQQ": "NASDAQ ETF",
    "DIA": "Dow Jones ETF",
    "^VIX": "VIX",
    "GLD": "Gold ETF",
    "TLT": "20Y Treasury ETF",
    "DX-Y.NYB": "US Dollar Index"
}


def fetch_yahoo_quote(ticker):
    encoded = urllib.parse.quote(ticker)
    url = f"https://query1.finance.yahoo.com/v8/finance/chart/{encoded}?interval=1d&range=5d"
    data = fetch_json(url, headers={
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
        "Accept": "application/json",
        "Referer": "https://finance.yahoo.com"
    })

    if "_error" in data:
        return {"ticker": ticker, "error": data["_error"]}

    try:
        result = data["chart"]["result"][0]
        meta = result["meta"]
        closes = result.get("indicators", {}).get("quote", [{}])[0].get("close", [])
        valid_closes = [c for c in closes if c is not None]

        prev_close = meta.get("previousClose") or meta.get("chartPreviousClose")
        current = meta.get("regularMarketPrice")
        change_pct = ((current - prev_close) / prev_close * 100) if prev_close and current else None

        return {
            "ticker": ticker,
            "name": EQUITY_TICKERS.get(ticker, ticker),
            "price": current,
            "prev_close": prev_close,
            "change_pct": round(change_pct, 2) if change_pct is not None else None,
            "currency": meta.get("currency", "USD"),
            "exchange": meta.get("exchangeName", "")
        }
    except (KeyError, IndexError, TypeError) as e:
        return {"ticker": ticker, "error": str(e)}


def fetch_equities(tickers=None):
    if tickers is None:
        tickers = list(EQUITY_TICKERS.keys())

    results = {}
    threads = []

    def fetch_one(t):
        results[t] = fetch_yahoo_quote(t)

    for t in tickers:
        th = threading.Thread(target=fetch_one, args=(t,))
        threads.append(th)
        th.start()

    for th in threads:
        th.join(timeout=15)

    return results


# --- FRED macro data ---
FRED_SERIES = {
    "DFF": "Fed Funds Rate",
    "DGS10": "10Y Treasury Yield",
    "CPIAUCSL": "CPI (All Urban)",
    "UNRATE": "Unemployment Rate",
    "M2SL": "M2 Money Supply"
}


def fetch_fred_series(series_id, latest_only=True):
    url = f"https://fred.stlouisfed.org/graph/fredgraph.csv?id={series_id}"
    text = fetch_text(url)
    if not text:
        return {"series": series_id, "error": "fetch failed"}

    reader = csv.DictReader(io.StringIO(text))
    rows = [r for r in reader if r.get("VALUE") and r["VALUE"] != "."]

    if not rows:
        return {"series": series_id, "error": "no data"}

    if latest_only:
        latest = rows[-1]
        return {
            "series": series_id,
            "name": FRED_SERIES.get(series_id, series_id),
            "value": float(latest["VALUE"]),
            "date": latest["DATE"]
        }

    return {
        "series": series_id,
        "name": FRED_SERIES.get(series_id, series_id),
        "data": [{"date": r["DATE"], "value": float(r["VALUE"])} for r in rows[-12:]]
    }


def fetch_macro():
    results = {}
    threads = []

    def fetch_one(sid):
        results[sid] = fetch_fred_series(sid)

    for sid in ["DFF", "DGS10", "CPIAUCSL", "UNRATE"]:
        th = threading.Thread(target=fetch_one, args=(sid,))
        threads.append(th)
        th.start()

    for th in threads:
        th.join(timeout=15)

    return results


def classify_risk(equities, crypto, fear_greed, macro):
    """Simple risk-on/risk-off classifier."""
    signals = []

    vix = equities.get("^VIX", {}).get("price")
    if vix:
        if vix < 18:
            signals.append(("risk-on", "VIX low", vix))
        elif vix > 25:
            signals.append(("risk-off", "VIX elevated", vix))

    spy = equities.get("SPY", {}).get("change_pct")
    if spy:
        if spy > 0.5:
            signals.append(("risk-on", "SPY up", spy))
        elif spy < -1.0:
            signals.append(("risk-off", "SPY down", spy))

    fg = fear_greed.get("current", {}).get("value")
    if fg:
        if fg > 65:
            signals.append(("risk-on", "Fear&Greed greedy", fg))
        elif fg < 35:
            signals.append(("risk-off", "Fear&Greed fearful", fg))

    btc_change = next((c["change_24h"] for c in crypto.get("data", []) if c["symbol"] == "BTC"), None)
    if btc_change:
        if btc_change > 3:
            signals.append(("risk-on", "BTC 24h strong", btc_change))
        elif btc_change < -4:
            signals.append(("risk-off", "BTC 24h weak", btc_change))

    risk_on = sum(1 for s in signals if s[0] == "risk-on")
    risk_off = sum(1 for s in signals if s[0] == "risk-off")

    if risk_on > risk_off + 1:
        posture = "RISK-ON"
    elif risk_off > risk_on + 1:
        posture = "RISK-OFF"
    else:
        posture = "NEUTRAL"

    return {"posture": posture, "signals": signals, "risk_on": risk_on, "risk_off": risk_off}


def fmt_pct(v):
    if v is None:
        return "N/A"
    arrow = "▲" if v > 0 else "▼"
    return f"{arrow}{abs(v):.2f}%"


def fmt_price(v, decimals=2):
    if v is None:
        return "N/A"
    if v >= 1000:
        return f"${v:,.0f}"
    return f"${v:.{decimals}f}"


def fmt_mcap(v):
    if v is None:
        return "N/A"
    if v >= 1e12:
        return f"${v/1e12:.2f}T"
    if v >= 1e9:
        return f"${v/1e9:.1f}B"
    return f"${v/1e6:.0f}M"


def print_markdown(equities, crypto, fear_greed, macro, risk):
    now = datetime.utcnow().strftime("%Y-%m-%d %H:%M UTC")
    print(f"# Market Oracle Report")
    print(f"*{now}*\n")

    posture_emoji = {"RISK-ON": "🟢", "RISK-OFF": "🔴", "NEUTRAL": "🟡"}
    print(f"## Signal: {posture_emoji.get(risk['posture'], '⚪')} **{risk['posture']}**\n")

    # Equities
    eq_data = [(t, d) for t, d in equities.items() if "error" not in d and d.get("price")]
    if eq_data:
        print("## Equity Markets")
        print("| Asset | Price | 24h |")
        print("|-------|-------|-----|")
        for ticker, d in eq_data:
            name = d.get("name", ticker)
            print(f"| {name} | {fmt_price(d.get('price'))} | {fmt_pct(d.get('change_pct'))} |")
        print()

    # Crypto
    coins = crypto.get("data", [])[:10]
    if coins:
        print("## Crypto Markets")
        print("| Asset | Price | 24h | 7d | Mkt Cap |")
        print("|-------|-------|-----|----|---------|")
        for c in coins:
            print(f"| {c['symbol']} | {fmt_price(c['price'])} | {fmt_pct(c.get('change_24h'))} | {fmt_pct(c.get('change_7d'))} | {fmt_mcap(c.get('market_cap'))} |")
        print()

    # Sentiment
    fg_curr = fear_greed.get("current", {})
    fg_prev = fear_greed.get("yesterday", {})
    if fg_curr:
        print("## Sentiment")
        print(f"**Fear & Greed:** {fg_curr.get('value', 'N/A')}/100 — {fg_curr.get('classification', '')}")
        if fg_prev:
            print(f"**Yesterday:** {fg_prev.get('value', 'N/A')}/100 — {fg_prev.get('classification', '')}")
        print()

    # Macro
    macro_data = [(k, v) for k, v in macro.items() if "error" not in v and v.get("value")]
    if macro_data:
        print("## Macro (FRED)")
        print("| Indicator | Value | Date |")
        print("|-----------|-------|------|")
        for _, d in macro_data:
            print(f"| {d['name']} | {d['value']:.2f}{'%' if 'Rate' in d['name'] or 'Yield' in d['name'] else ''} | {d['date']} |")
        print()

    # Risk signals
    print("## Risk Signals")
    for sig in risk["signals"]:
        direction, reason, val = sig
        icon = "🟢" if direction == "risk-on" else "🔴"
        print(f"- {icon} {reason}: {val:.2f}")
    print()


def main():
    parser = argparse.ArgumentParser(description="Multi-signal market data fetcher")
    parser.add_argument("--mode", default="all", choices=["all", "crypto", "equities", "macro"])
    parser.add_argument("--format", default="markdown", choices=["markdown", "json"])
    parser.add_argument("--tickers", help="Comma-separated ticker list for equities")
    args = parser.parse_args()

    equities, crypto, fear_greed, macro = {}, {"data": []}, {}, {}

    threads = []

    if args.mode in ("all", "crypto"):
        threads.append(threading.Thread(target=lambda: crypto.update(fetch_crypto_markets())))
        threads.append(threading.Thread(target=lambda: fear_greed.update(fetch_fear_greed())))

    if args.mode in ("all", "equities"):
        tickers = args.tickers.split(",") if args.tickers else None
        threads.append(threading.Thread(target=lambda: equities.update(fetch_equities(tickers))))

    if args.mode in ("all", "macro"):
        threads.append(threading.Thread(target=lambda: macro.update(fetch_macro())))

    for t in threads:
        t.start()
    for t in threads:
        t.join(timeout=25)

    risk = classify_risk(equities, crypto, fear_greed, macro)

    if args.format == "json":
        print(json.dumps({
            "equities": equities,
            "crypto": crypto,
            "fear_greed": fear_greed,
            "macro": macro,
            "risk": risk,
            "timestamp": datetime.utcnow().isoformat()
        }, indent=2))
    else:
        print_markdown(equities, crypto, fear_greed, macro, risk)


if __name__ == "__main__":
    main()
