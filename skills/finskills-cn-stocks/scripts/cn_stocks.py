#!/usr/bin/env python3
"""Small dependency-free CLI for the Finskills China A-share endpoints."""

from __future__ import annotations

import argparse
import json
import os
import sys
import urllib.error
import urllib.parse
import urllib.request


DEFAULT_BASE_URL = "https://finskills.net"
DATASETS = {"financials", "dividends", "options", "holders", "recommendations", "earnings"}


def make_url(base_url: str, command: str, values: list[str], args: argparse.Namespace) -> str:
    base = base_url.rstrip("/")
    query: dict[str, str | int] = {}

    if command == "quotes":
        path = "/v1/stocks/quotes"
        query["symbols"] = ",".join(values)
    elif command == "search":
        path = "/v1/stocks/search"
        query.update(q=values[0], limit=args.limit)
    else:
        path = f"/v1/stocks/{command}/{urllib.parse.quote(values[0], safe='')}"
        if command == "history":
            query.update(interval=args.interval, adjustment=args.adjustment, limit=args.limit, offset=args.offset)
            if args.date_from:
                query["from"] = args.date_from
            if args.date_to:
                query["to"] = args.date_to
        elif command == "financials":
            query.update(freq=args.freq, limit=args.limit)
        elif command in DATASETS:
            query["limit"] = args.limit

    return f"{base}{path}" + (f"?{urllib.parse.urlencode(query)}" if query else "")


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description="Query Finskills China A-share data")
    result.add_argument("command", choices=["quote", "quotes", "history", "search", "profile", *sorted(DATASETS)])
    result.add_argument("values", nargs="+", help="Security code(s), or a search query")
    result.add_argument("--base-url", default=DEFAULT_BASE_URL)
    result.add_argument("--interval", choices=["1d", "30m", "60m"], default="1d")
    result.add_argument("--adjustment", choices=["none", "qfq", "hfq"], default="qfq")
    result.add_argument("--from", dest="date_from", help="Start date in YYYY-MM-DD format")
    result.add_argument("--to", dest="date_to", help="End date in YYYY-MM-DD format")
    result.add_argument("--freq", choices=["yearly", "quarterly"], default="yearly")
    result.add_argument("--limit", type=int, default=100)
    result.add_argument("--offset", type=int, default=0)
    result.add_argument("--dry-run", action="store_true", help="Print the URL without sending a request")
    return result


def main() -> int:
    args = parser().parse_args()
    if args.command != "quotes" and len(args.values) != 1:
        parser().error(f"{args.command} accepts exactly one value")

    url = make_url(args.base_url, args.command, args.values, args)
    if args.dry_run:
        print(url)
        return 0

    api_key = os.environ.get("FINSKILLS_API_KEY")
    if not api_key:
        print("FINSKILLS_API_KEY is required", file=sys.stderr)
        return 2

    request = urllib.request.Request(url, headers={"X-API-Key": api_key, "Accept": "application/json"})
    try:
        with urllib.request.urlopen(request, timeout=30) as response:
            payload = json.load(response)
    except urllib.error.HTTPError as error:
        body = error.read().decode("utf-8", errors="replace")
        print(f"HTTP {error.code}: {body}", file=sys.stderr)
        return 1
    except urllib.error.URLError as error:
        print(f"Request failed: {error.reason}", file=sys.stderr)
        return 1

    print(json.dumps(payload, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
