#!/usr/bin/env python3
"""Create a materials literature search and citation matrix CSV."""

from __future__ import annotations

import argparse
import csv
import sys
from pathlib import Path

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parent))

from _citation_common import (
    CSV_FIELDS,
    DEFAULT_CLAIMS,
    build_claim_row,
    build_query,
    classify_evidence_layers,
    default_layer_for_evidence_type,
    evidence_type_for_claim,
    expand_journal_terms,
    read_claims,
    split_items,
)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--topic", required=True, help="Research topic or material system.")
    parser.add_argument("--journals", default="CBM,JBE,RMPD,IJPE", help="Comma-separated journal aliases.")
    parser.add_argument("--claims-file", help="Optional text file with one claim/evidence need per line.")
    parser.add_argument("--output", default="materials-citation-matrix.csv")
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
        evidence_layer = (classify_evidence_layers(claim) or [default_layer_for_evidence_type(evidence_type)])[0]
        rows.append(build_claim_row(
            idx, claim, evidence_type, evidence_layer,
            build_query(topic, claim, journals),
            journal_terms,
        ))

    with Path(args.output).open("w", encoding="utf-8-sig", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=CSV_FIELDS)
        writer.writeheader()
        writer.writerows(rows)
    print(args.output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
