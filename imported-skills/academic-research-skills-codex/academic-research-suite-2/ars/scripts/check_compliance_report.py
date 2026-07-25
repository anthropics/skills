#!/usr/bin/env python3
"""Validate an ARS compliance report against compliance_report.schema.json.

Usage: python scripts/check_compliance_report.py path/to/report.json

Exit 0 on pass (warnings may still be printed to stderr).
Exit 1 on validation failure.
"""
from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path

import jsonschema

SCHEMA_PATH = Path(__file__).resolve().parent.parent / "shared" / "compliance_report.schema.json"


def load_schema() -> dict:
    return json.loads(SCHEMA_PATH.read_text(encoding="utf-8"))


def validate(report: dict) -> list[str]:
    schema = load_schema()
    validator = jsonschema.Draft202012Validator(
        schema,
        format_checker=jsonschema.Draft202012Validator.FORMAT_CHECKER,
    )
    return [f"{list(e.absolute_path)}: {e.message}" for e in validator.iter_errors(report)]


def warn_suspicious(report: dict) -> list[str]:
    """Non-blocking soft warnings for semantic red flags."""
    warnings = []

    # CA-3: sycophancy risk — all 17 items pass with no evidence citations.
    pt = report.get("prisma_trAIce")
    if isinstance(pt, dict):
        by_tier = pt.get("by_tier", {})
        all_pass = all(
            isinstance(t, dict) and t.get("total") == t.get("pass")
            for t in by_tier.values()
        )
        if all_pass and by_tier and not report.get("evidence"):
            warnings.append(
                "WARNING: all 17 PRISMA-trAIce items pass but evidence[] is empty. "
                "CA-3 self-check should trigger in the agent. Consider re-running."
            )

    # CA-4: RAISE pass with empty evidence array for that principle.
    raise_obj = report.get("raise", {})
    for name, status in raise_obj.get("principles", {}).items():
        if status == "pass" and not raise_obj.get("principle_evidence", {}).get(name):
            warnings.append(
                f"WARNING: RAISE principle '{name}' marked 'pass' but principle_evidence is empty. "
                "CA-4 should have downgraded this to 'warn [weak evidence]'."
            )

    # #95 maturity disclosure: when prisma_trAIce subtree is present but
    # protocol_maturity is missing, suggest the agent populate it.
    # Opt-in (ARS_WARN_MISSING_MATURITY=1) to preserve the zero-touch
    # promise for entries authored before Schema 12's protocol_maturity
    # field landed.
    if os.environ.get("ARS_WARN_MISSING_MATURITY") == "1":
        if isinstance(pt, dict) and "protocol_maturity" not in pt:
            warnings.append(
                "WARNING: prisma_trAIce subtree is present but protocol_maturity is missing. "
                "Per issue #95, compliance_agent should populate protocol_maturity from "
                "shared/prisma_trAIce_protocol.md. This warning is opt-in "
                "(ARS_WARN_MISSING_MATURITY=1) and does not fail validation."
            )
    return warnings


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path, help="Path to the compliance report JSON")
    args = parser.parse_args()

    try:
        report = json.loads(args.report.read_text(encoding="utf-8"))
    except (FileNotFoundError, json.JSONDecodeError) as exc:
        print(f"ERROR: failed to load {args.report}: {exc}")
        return 1

    errors = validate(report)
    if errors:
        for e in errors:
            print(f"ERROR: {e}")
        print(
            f"\n{len(errors)} schema violation(s). "
            "See shared/compliance_report.schema.json for field definitions.",
            file=sys.stderr,
        )
        return 1

    for w in warn_suspicious(report):
        print(w, file=sys.stderr)

    print(f"OK: {args.report} is a valid compliance_report (Schema 12)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
