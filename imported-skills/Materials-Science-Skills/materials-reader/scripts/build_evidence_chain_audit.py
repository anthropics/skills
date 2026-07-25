#!/usr/bin/env python3
"""Create a claim-evidence-mechanism audit table for materials reading."""

from __future__ import annotations

import argparse
import csv
from pathlib import Path


DEFAULT_CLAIMS = [
    "Main material performance claim",
    "Mechanism explanation",
    "Durability or service-condition claim",
    "Engineering application claim",
]


def read_items(path: str | None) -> list[str]:
    if not path:
        return DEFAULT_CLAIMS
    text = Path(path).read_text(encoding="utf-8-sig")
    items = [line.strip(" -\t") for line in text.splitlines() if line.strip()]
    return items or DEFAULT_CLAIMS


def infer_risk(claim: str) -> str:
    lower = claim.lower()
    if any(word in lower for word in ["mechanism", "机理", "interaction", "compatibility"]):
        return "Reviewer may ask whether the mechanism is directly measured."
    if any(word in lower for word in ["durability", "aging", "moisture", "water", "耐久", "水损害"]):
        return "Reviewer may ask for service-condition or retained-performance evidence."
    if any(word in lower for word in ["application", "engineering", "field", "工程"]):
        return "Reviewer may ask about constructability, scale, or field relevance."
    return "Reviewer may ask whether the evidence directly supports the claim."


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--claims-file", help="Optional text file with one claim per line.")
    parser.add_argument("--output", default="materials-evidence-chain-audit.csv")
    args = parser.parse_args()

    rows = []
    for claim in read_items(args.claims_file):
        rows.append(
            {
                "claim": claim,
                "direct_evidence": "[figure/table/test needed]",
                "mechanism_inference": "direct / inferred / unsupported",
                "boundary_or_limitation": "[dosage/material/condition/scale boundary]",
                "borrowable_use": "[background/method/benchmark/mechanism/discussion]",
                "reviewer_risk": infer_risk(claim),
                "citation_role": "[background/method/benchmark/mechanism]",
            }
        )

    fields = [
        "claim",
        "direct_evidence",
        "mechanism_inference",
        "boundary_or_limitation",
        "borrowable_use",
        "reviewer_risk",
        "citation_role",
    ]
    with Path(args.output).open("w", encoding="utf-8-sig", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)
    print(args.output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
