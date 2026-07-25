#!/usr/bin/env python3
"""Standalone materials citation search — no MCP dependency.

Queries CrossRef directly via stdlib (urllib) and produces a citation matrix CSV.
Use this script when the MCP server is not installed or unavailable.
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
import time
from pathlib import Path
from urllib.error import URLError
from urllib.parse import urlencode
from urllib.request import Request, urlopen

from _citation_common import (
    CSV_FIELDS,
    build_claim_row,
    classify_evidence_layers,
    default_layer_for_evidence_type,
    evidence_type_for_claim,
    expand_journal_terms,
    read_claims,
    split_items,
)

CROSSREF_API = "https://api.crossref.org/works"
USER_AGENT = "materials-citation-fallback/1.0 (mailto:unknown@example.com)"


def crossref_search(query: str, rows: int = 5) -> list[dict]:
    params = {
        "query": query,
        "rows": str(rows),
        "select": "DOI,title,author,container-title,published-print,published-online,"
                  "volume,issue,page,ISSN,abstract,type",
    }
    url = f"{CROSSREF_API}?{urlencode(params)}"
    req = Request(url, headers={"User-Agent": USER_AGENT})
    try:
        with urlopen(req, timeout=30) as resp:
            data = json.loads(resp.read().decode("utf-8"))
        items = data.get("message", {}).get("items", [])
        return items
    except (URLError, json.JSONDecodeError, OSError) as exc:
        print(f"  CrossRef query failed: {exc}", file=sys.stderr)
        return []


def extract_year(item: dict) -> str:
    for key in ("published-print", "published-online"):
        parts = item.get(key, {}).get("date-parts", [[]])
        if parts and parts[0] and parts[0][0]:
            return str(parts[0][0])
    return ""


def extract_authors(item: dict) -> str:
    authors = item.get("author", [])
    if not authors:
        return "Unknown"
    names = []
    for a in authors[:3]:
        family = a.get("family", "")
        given = a.get("given", "")
        names.append(f"{family} {given}".strip())
    if len(authors) > 3:
        names.append("et al.")
    return "; ".join(names)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--topic", required=True, help="Research topic or material system.")
    parser.add_argument("--journals", default="CBM,JBE,RMPD,IJPE", help="Comma-separated journal aliases.")
    parser.add_argument("--claims-file", help="Optional text file with one claim per line.")
    parser.add_argument("--output", default="materials-citation-matrix.csv")
    parser.add_argument("--max-per-claim", type=int, default=3, help="Max CrossRef results per claim.")
    parser.add_argument("--delay", type=float, default=1.0, help="Delay between CrossRef queries (seconds).")
    args = parser.parse_args()

    topic = args.topic.strip()
    if not topic:
        raise ValueError("--topic must not be empty")

    journals = split_items(args.journals)
    journal_terms = expand_journal_terms(journals)
    claims = read_claims(args.claims_file)
    rows = []

    for idx, claim in enumerate(claims, 1):
        evidence_type = evidence_type_for_claim(claim)
        layer = (classify_evidence_layers(claim) or [default_layer_for_evidence_type(evidence_type)])[0]

        journal_query = " OR ".join(f'"{j}"' for j in journal_terms)
        claim_query = claim.replace("Research gap and novelty", "review OR recent progress")
        query = f'("{topic}") AND ({claim_query}) AND ({journal_query})'

        print(f"[{idx}/{len(claims)}] Searching: {claim[:60]}...")
        items = crossref_search(query, rows=args.max_per_claim)

        if items:
            for item in items:
                title = (item.get("title") or [""])[0]
                journal = (item.get("container-title") or [""])[0]
                doi = item.get("DOI", "")
                year = extract_year(item)
                authors = extract_authors(item)

                rows.append(build_claim_row(
                    idx, claim, evidence_type, layer, query, journal_terms,
                    candidate_source=f"{authors}. {title}. {journal}, {year}.",
                    candidate_doi=doi,
                    candidate_year=year,
                    status="candidate found",
                    risk_note="Inspect abstract/publisher page before citing.",
                ))
        else:
            rows.append(build_claim_row(
                idx, claim, evidence_type, layer, query, journal_terms,
            ))

        if idx < len(claims):
            time.sleep(args.delay)

    with Path(args.output).open("w", encoding="utf-8-sig", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=CSV_FIELDS)
        writer.writeheader()
        writer.writerows(rows)

    print(f"\nOutput: {args.output} ({len(rows)} rows)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
