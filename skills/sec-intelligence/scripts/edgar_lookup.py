#!/usr/bin/env python3
"""SEC EDGAR lookup tool. No auth required. Polite crawling per EDGAR guidelines."""

import sys
import json
import urllib.request
import urllib.parse
import argparse
import time
import re

EDGAR_BASE = "https://data.sec.gov"
EDGAR_SEARCH = "https://efts.sec.gov/LATEST/search-index"
EDGAR_COMPANY_SEARCH = "https://www.sec.gov/cgi-bin/browse-edgar"

# EDGAR requires User-Agent with contact info
HEADERS = {
    "User-Agent": "money-brain research tool contact@moneybrain.local",
    "Accept-Encoding": "gzip, deflate",
    "Host": "data.sec.gov"
}


def fetch(url, headers=None):
    req = urllib.request.Request(url, headers=headers or HEADERS)
    with urllib.request.urlopen(req, timeout=15) as resp:
        return json.loads(resp.read().decode('utf-8'))


def search_company_cik(company_name):
    """Search EDGAR for company CIK by name."""
    url = f"https://efts.sec.gov/LATEST/search-index?q=%22{urllib.parse.quote(company_name)}%22&dateRange=custom&startdt=2020-01-01&forms=10-K"
    headers = {**HEADERS, "Host": "efts.sec.gov"}
    try:
        data = fetch(url, headers)
        hits = data.get("hits", {}).get("hits", [])
        if hits:
            src = hits[0].get("_source", {})
            return {
                "cik": src.get("entity_id", ""),
                "name": src.get("display_names", [""])[0] if src.get("display_names") else src.get("entity_name", ""),
                "ticker": src.get("file_date", "")
            }
    except Exception as e:
        print(f"Search error: {e}", file=sys.stderr)
    return None


def get_submissions(cik):
    """Get company submissions (all filings) from EDGAR."""
    cik_padded = str(cik).zfill(10)
    url = f"{EDGAR_BASE}/submissions/CIK{cik_padded}.json"
    headers = {**HEADERS, "Host": "data.sec.gov"}
    return fetch(url, headers)


def get_company_facts(cik):
    """Get XBRL financial facts for a company."""
    cik_padded = str(cik).zfill(10)
    url = f"{EDGAR_BASE}/api/xbrl/companyfacts/CIK{cik_padded}.json"
    headers = {**HEADERS, "Host": "data.sec.gov"}
    return fetch(url, headers)


def list_filings(cik, form_type=None, limit=20):
    """List filings for a company, optionally filtered by form type."""
    data = get_submissions(cik)
    filings = data.get("filings", {}).get("recent", {})

    if not filings:
        return []

    forms = filings.get("form", [])
    dates = filings.get("filingDate", [])
    accessions = filings.get("accessionNumber", [])
    descriptions = filings.get("primaryDocument", [])

    results = []
    for i, (form, date, accession, doc) in enumerate(zip(forms, dates, accessions, descriptions)):
        if form_type and form != form_type:
            continue
        results.append({
            "form": form,
            "date": date,
            "accession": accession,
            "document": doc,
            "url": f"https://www.sec.gov/Archives/edgar/data/{cik}/{accession.replace('-', '')}/{doc}"
        })
        if len(results) >= limit:
            break

    return results


def get_insider_transactions(cik, days=90):
    """Fetch Form 4 insider transactions."""
    filings = list_filings(cik, form_type="4", limit=50)
    # Filter to recent
    from datetime import datetime, timedelta
    cutoff = (datetime.now() - timedelta(days=days)).strftime("%Y-%m-%d")
    recent = [f for f in filings if f["date"] >= cutoff]
    return recent


def extract_financial_highlights(cik):
    """Extract key financial metrics from XBRL data."""
    try:
        facts = get_company_facts(cik)
        us_gaap = facts.get("facts", {}).get("us-gaap", {})

        metrics = {}

        # Revenue
        for key in ["Revenues", "RevenueFromContractWithCustomerExcludingAssessedTax", "SalesRevenueNet"]:
            if key in us_gaap:
                entries = us_gaap[key].get("units", {}).get("USD", [])
                annual = [e for e in entries if e.get("form") == "10-K"]
                if annual:
                    latest = sorted(annual, key=lambda x: x.get("end", ""))[-1]
                    metrics["revenue"] = {"value": latest["val"], "period": latest.get("end", "")}
                    break

        # Net Income
        for key in ["NetIncomeLoss", "ProfitLoss"]:
            if key in us_gaap:
                entries = us_gaap[key].get("units", {}).get("USD", [])
                annual = [e for e in entries if e.get("form") == "10-K"]
                if annual:
                    latest = sorted(annual, key=lambda x: x.get("end", ""))[-1]
                    metrics["net_income"] = {"value": latest["val"], "period": latest.get("end", "")}
                    break

        return metrics
    except Exception as e:
        return {"error": str(e)}


def format_number(n):
    if n is None:
        return "N/A"
    if abs(n) >= 1e9:
        return f"${n/1e9:.1f}B"
    if abs(n) >= 1e6:
        return f"${n/1e6:.1f}M"
    return f"${n:,.0f}"


def main():
    parser = argparse.ArgumentParser(description="SEC EDGAR lookup")
    parser.add_argument("--cik", help="Company CIK number")
    parser.add_argument("--company", help="Company name to search")
    parser.add_argument("--resolve-cik", action="store_true", help="Find CIK from company name")
    parser.add_argument("--list-filings", action="store_true", help="List recent filings")
    parser.add_argument("--form", help="Filter by form type (10-K, 10-Q, 8-K, 4)")
    parser.add_argument("--latest", action="store_true", help="Show only most recent filing")
    parser.add_argument("--insiders", action="store_true", help="Show insider transactions (Form 4)")
    parser.add_argument("--financials", action="store_true", help="Show financial highlights via XBRL")
    parser.add_argument("--limit", type=int, default=20)
    args = parser.parse_args()

    if args.company and args.resolve_cik:
        result = search_company_cik(args.company)
        if result:
            print(json.dumps(result, indent=2))
        else:
            print(f"Company not found: {args.company}", file=sys.stderr)
            sys.exit(1)
        return

    if not args.cik:
        print("Error: --cik required (or use --company --resolve-cik to find it)", file=sys.stderr)
        sys.exit(1)

    cik = args.cik.lstrip("0")

    if args.list_filings:
        filings = list_filings(cik, form_type=args.form, limit=args.limit)
        if args.latest and filings:
            filings = filings[:1]
        print(json.dumps(filings, indent=2))

    elif args.insiders:
        txns = get_insider_transactions(cik)
        print(json.dumps(txns, indent=2))

    elif args.financials:
        metrics = extract_financial_highlights(cik)
        for k, v in metrics.items():
            if isinstance(v, dict) and "value" in v:
                print(f"{k}: {format_number(v['value'])} (period ending {v.get('period', 'N/A')})")
            else:
                print(f"{k}: {v}")

    else:
        # Default: company overview
        data = get_submissions(cik)
        info = {
            "name": data.get("name", ""),
            "cik": data.get("cik", ""),
            "sic": data.get("sic", ""),
            "sic_description": data.get("sicDescription", ""),
            "tickers": data.get("tickers", []),
            "exchanges": data.get("exchanges", []),
            "state": data.get("stateOfIncorporation", ""),
            "fiscal_year_end": data.get("fiscalYearEnd", ""),
            "recent_filing_count": len(data.get("filings", {}).get("recent", {}).get("form", []))
        }
        print(json.dumps(info, indent=2))


if __name__ == "__main__":
    main()
