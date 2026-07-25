#!/usr/bin/env python3
"""Validate an ARS benchmark report against benchmark_report.schema.json.

Usage: python scripts/check_benchmark_report.py path/to/report.json

Exit 0 on pass (warnings may still be printed to stderr).
Exit 1 on validation failure.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import jsonschema

SCHEMA_PATH = Path(__file__).resolve().parent.parent / "shared" / "benchmark_report.schema.json"


def load_schema() -> dict:
    return json.loads(SCHEMA_PATH.read_text(encoding="utf-8"))


def validate(report: dict) -> list[str]:
    schema = load_schema()
    validator = jsonschema.Draft202012Validator(schema)
    return [f"{list(e.absolute_path)}: {e.message}" for e in validator.iter_errors(report)]


def warn_self_scored(report: dict) -> list[str]:
    warnings = []
    scoring = report.get("metrics", {}).get("scoring_independence")
    if scoring == "self-scored":
        warnings.append(
            "WARNING: metrics.scoring_independence = 'self-scored'. "
            "Self-scoring is permitted but a known reward-hacking risk. "
            "Consider blind-scored or third-party-scored instead."
        )
    sample = report.get("human_baseline", {}).get("sample_size", 0)
    if isinstance(sample, int) and 1 <= sample <= 2:
        warnings.append(
            f"WARNING: human_baseline.sample_size = {sample}. "
            "n<=2 is dramatic, not statistical. Consider n>=5 or explicit disclosure in caveats."
        )
    return warnings


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path, help="Path to the benchmark report JSON")
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
            f"See shared/benchmark_report_pattern.md for field rationale.",
            file=sys.stderr,
        )
        return 1

    for w in warn_self_scored(report):
        print(w, file=sys.stderr)

    print("OK: benchmark report validates.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
