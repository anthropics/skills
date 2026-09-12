#!/usr/bin/env python3
"""Multi-source company intelligence gatherer."""

import sys
import json
import os
import urllib.request
import urllib.parse
import argparse
import threading
from datetime import datetime, timedelta

NEWSAPI_KEY = os.getenv("NEWSAPI_KEY", "")
GITHUB_TOKEN = os.getenv("GITHUB_TOKEN", "")

HEADERS = {"User-Agent": "company-investigator/1.0", "Accept": "application/json"}
EDGAR_HEADERS = {"User-Agent": "company-investigator contact@moneybrain.local", "Accept": "application/json"}


def fetch_json(url, headers=None, timeout=15):
    try:
        req = urllib.request.Request(url, headers=headers or HEADERS)
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            return json.loads(resp.read().decode('utf-8'))
    except urllib.error.HTTPError as e:
        return {"_error": f"HTTP {e.code}", "_status": e.code}
    except Exception as e:
        return {"_error": str(e)}


# --- Yahoo Finance ---
def fetch_stock_data(ticker, range_days=90):
    encoded = urllib.parse.quote(ticker)
    url = f"https://query1.finance.yahoo.com/v8/finance/chart/{encoded}?interval=1d&range={range_days}d"
    data = fetch_json(url, headers={
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
        "Accept": "application/json",
        "Referer": "https://finance.yahoo.com"
    })
    if "_error" in data:
        return data
    try:
        result = data["chart"]["result"][0]
        meta = result["meta"]
        closes = result.get("indicators", {}).get("quote", [{}])[0].get("close", [])
        valid_closes = [c for c in closes if c is not None]

        start_price = valid_closes[0] if valid_closes else None
        current_price = meta.get("regularMarketPrice")
        change_90d = ((current_price - start_price) / start_price * 100) if start_price and current_price else None

        return {
            "ticker": ticker,
            "price": current_price,
            "market_cap": meta.get("marketCap"),
            "52w_high": meta.get("fiftyTwoWeekHigh"),
            "52w_low": meta.get("fiftyTwoWeekLow"),
            "change_90d_pct": round(change_90d, 2) if change_90d is not None else None,
            "currency": meta.get("currency", "USD"),
            "exchange": meta.get("fullExchangeName", "")
        }
    except (KeyError, IndexError, TypeError) as e:
        return {"_error": str(e)}


# --- SEC EDGAR ---
def fetch_edgar_company(company_name):
    encoded = urllib.parse.quote(company_name)
    url = f"https://efts.sec.gov/LATEST/search-index?q=%22{encoded}%22&forms=10-K&dateRange=custom&startdt=2020-01-01"
    data = fetch_json(url, headers={**EDGAR_HEADERS, "Host": "efts.sec.gov"})
    hits = data.get("hits", {}).get("hits", [])
    if not hits:
        return None
    src = hits[0].get("_source", {})
    return {
        "cik": src.get("entity_id", ""),
        "name": src.get("display_names", [""])[0] if src.get("display_names") else "",
        "form": src.get("form_type", ""),
        "filed": src.get("file_date", "")
    }


def fetch_edgar_submissions(cik):
    cik_padded = str(cik).lstrip("0").zfill(10)
    url = f"https://data.sec.gov/submissions/CIK{cik_padded}.json"
    return fetch_json(url, headers={**EDGAR_HEADERS, "Host": "data.sec.gov"})


def fetch_insider_activity(cik, days=90):
    subs = fetch_edgar_submissions(cik)
    if "_error" in subs:
        return []
    filings = subs.get("filings", {}).get("recent", {})
    forms = filings.get("form", [])
    dates = filings.get("filingDate", [])
    cutoff = (datetime.now() - timedelta(days=days)).strftime("%Y-%m-%d")
    insider = [(f, d) for f, d in zip(forms, dates) if f == "4" and d >= cutoff]
    return insider[:20]


# --- News ---
def fetch_news(company, use_key=True):
    if use_key and NEWSAPI_KEY:
        encoded = urllib.parse.quote(company)
        url = f"https://newsapi.org/v2/everything?q={encoded}&sortBy=publishedAt&pageSize=10&language=en"
        data = fetch_json(url, headers={"X-Api-Key": NEWSAPI_KEY, **HEADERS})
        if "_error" not in data:
            return [{"title": a.get("title"), "source": a.get("source", {}).get("name"), "date": a.get("publishedAt", "")[:10], "url": a.get("url")} for a in data.get("articles", [])]

    # Fallback: Hacker News
    encoded = urllib.parse.quote(company)
    url = f"https://hn.algolia.com/api/v1/search?query={encoded}&tags=story&hitsPerPage=10"
    data = fetch_json(url)
    return [{"title": h.get("title"), "source": "Hacker News", "date": h.get("created_at", "")[:10], "url": h.get("url") or f"https://news.ycombinator.com/item?id={h.get('objectID','')}",
             "points": h.get("points", 0)} for h in data.get("hits", [])]


# --- GitHub ---
def fetch_github_org(org_name):
    gh_headers = {**HEADERS}
    if GITHUB_TOKEN:
        gh_headers["Authorization"] = f"Bearer {GITHUB_TOKEN}"

    url = f"https://api.github.com/orgs/{urllib.parse.quote(org_name)}"
    org_data = fetch_json(url, headers=gh_headers)

    repos_url = f"https://api.github.com/orgs/{urllib.parse.quote(org_name)}/repos?sort=stars&per_page=5&type=public"
    repos_data = fetch_json(repos_url, headers=gh_headers)

    if "_error" in org_data:
        # Try searching repos
        search_url = f"https://api.github.com/search/repositories?q={urllib.parse.quote(org_name)}+in:name&sort=stars&per_page=5"
        repos_data = fetch_json(search_url, headers=gh_headers)
        repos_list = repos_data.get("items", [])
        if repos_list:
            return {
                "org": org_name,
                "repos": [{"name": r["full_name"], "stars": r["stargazers_count"], "language": r.get("language")} for r in repos_list[:5]],
                "note": "searched (no exact org match)"
            }
        return {"_error": "org not found"}

    repos_list = repos_data if isinstance(repos_data, list) else repos_data.get("items", [])
    return {
        "org": org_name,
        "public_repos": org_data.get("public_repos", 0),
        "followers": org_data.get("followers", 0),
        "created": org_data.get("created_at", "")[:10],
        "repos": [{"name": r["name"], "stars": r.get("stargazers_count", 0), "language": r.get("language"), "updated": r.get("updated_at", "")[:10]} for r in repos_list[:5]]
    }


# --- Formatting helpers ---
def fmt_money(v):
    if v is None:
        return "N/A"
    if abs(v) >= 1e12:
        return f"${v/1e12:.2f}T"
    if abs(v) >= 1e9:
        return f"${v/1e9:.1f}B"
    if abs(v) >= 1e6:
        return f"${v/1e6:.1f}M"
    return f"${v:,.0f}"


def print_report(company, ticker, stock, edgar, submissions, insider, news, github):
    today = datetime.utcnow().strftime("%Y-%m-%d")
    is_public = ticker and stock and "_error" not in stock

    print(f"# Company Intelligence: {company}")
    print(f"*{today} | Sources: EDGAR, Yahoo Finance, News, GitHub, HN*\n")

    company_type = "Public" if is_public else "Private"
    ticker_str = f" | Ticker: {ticker}" if ticker else ""
    print(f"**Type:** {company_type}{ticker_str}\n")

    # Financial snapshot
    if is_public:
        print("## Financial Snapshot")
        print(f"| Metric | Value |")
        print(f"|--------|-------|")
        print(f"| Price | {fmt_money(stock.get('price'))} |")
        print(f"| Market Cap | {fmt_money(stock.get('market_cap'))} |")
        print(f"| 52W High | {fmt_money(stock.get('52w_high'))} |")
        print(f"| 52W Low | {fmt_money(stock.get('52w_low'))} |")
        ch = stock.get("change_90d_pct")
        arrow = "▲" if ch and ch > 0 else "▼"
        print(f"| 90d Change | {arrow}{abs(ch):.2f}% |" if ch is not None else "| 90d Change | N/A |")
        print()

    # EDGAR
    if submissions and "_error" not in submissions:
        sic = submissions.get("sicDescription", "N/A")
        state = submissions.get("stateOfIncorporation", "N/A")
        fiscal_end = submissions.get("fiscalYearEnd", "N/A")
        print("## SEC/Regulatory Profile")
        print(f"- Industry (SIC): {sic}")
        print(f"- Incorporated: {state}")
        print(f"- Fiscal Year End: {fiscal_end}")
        if insider:
            print(f"- Insider Form 4 filings (90d): {len(insider)}")
        print()

    # News
    if news:
        print("## Recent News")
        for item in news[:7]:
            source = item.get('source', 'N/A')
            date = item.get('date', 'N/A')
            title = item.get('title', 'N/A')
            url = item.get('url', '')
            points = f" | {item.get('points', '')} pts" if item.get('points') else ""
            print(f"- **{title}** — {source}, {date}{points}")
        print()

    # GitHub
    if github and "_error" not in github:
        print("## GitHub Activity")
        print(f"- Public repos: {github.get('public_repos', '?')}")
        print(f"- Followers: {github.get('followers', '?')}")
        repos = github.get("repos", [])
        if repos:
            print("- Top repos:")
            for r in repos[:3]:
                lang = r.get("language") or "N/A"
                print(f"  - {r.get('name')} ({lang}) ⭐ {r.get('stars', 0)}")
        print()


def main():
    parser = argparse.ArgumentParser(description="Multi-source company intelligence")
    parser.add_argument("--company", required=True, help="Company name")
    parser.add_argument("--ticker", help="Stock ticker (for public companies)")
    parser.add_argument("--github-org", help="GitHub org name")
    parser.add_argument("--cik", help="SEC EDGAR CIK (skip auto-lookup)")
    parser.add_argument("--format", default="markdown", choices=["markdown", "json"])
    args = parser.parse_args()

    results = {}
    threads = []

    # News
    threads.append(threading.Thread(target=lambda: results.update({"news": fetch_news(args.company)})))

    # GitHub
    github_org = args.github_org or args.company.lower().replace(" ", "")
    threads.append(threading.Thread(target=lambda: results.update({"github": fetch_github_org(github_org)})))

    # Stock
    if args.ticker:
        threads.append(threading.Thread(target=lambda: results.update({"stock": fetch_stock_data(args.ticker)})))

    # EDGAR
    cik = args.cik
    if not cik:
        edgar_res = fetch_edgar_company(args.company)
        if edgar_res:
            cik = edgar_res.get("cik", "").lstrip("0")
    if cik:
        threads.append(threading.Thread(target=lambda c=cik: results.update({"submissions": fetch_edgar_submissions(c)})))
        threads.append(threading.Thread(target=lambda c=cik: results.update({"insider": fetch_insider_activity(c)})))

    for t in threads:
        t.start()
    for t in threads:
        t.join(timeout=25)

    if args.format == "json":
        print(json.dumps(results, indent=2))
    else:
        print_report(
            args.company, args.ticker,
            results.get("stock", {}),
            results.get("edgar"),
            results.get("submissions", {}),
            results.get("insider", []),
            results.get("news", []),
            results.get("github", {})
        )


if __name__ == "__main__":
    main()
