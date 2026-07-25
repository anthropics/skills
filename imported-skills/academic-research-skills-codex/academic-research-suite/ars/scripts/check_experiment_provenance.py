#!/usr/bin/env python3
"""Validate a Material Passport YAML's `experiment_provenance[]` entry SHAPE (#260).

Usage: python scripts/check_experiment_provenance.py path/to/passport.yaml

Standalone shape-only validator, mirroring scripts/check_repro_lock.py. It
validates each experiment_provenance[] entry against
shared/contracts/passport/experiment_provenance_entry.schema.json — which
encodes the D6 well-formedness rules including the absent-key rule
(negative_results / known_limitations MUST be present, value MAY be []; an
absent key is malformed).

This script does NOT run the cross-array EP/EA invariants (EP-INV-1..4,
EA-INV-1..2 — experiment_id uniqueness, planned_experiment_ids resolution,
declaration symmetry, alignment reference resolution). Those span multiple
aggregates and live in scripts/check_claim_audit_consistency.py. The two
scripts deliberately do not duplicate invariant logic.

- Missing `experiment_provenance` key: OK, exit 0 (optional aggregate; a
  passport may legitimately carry none). The cross-array consistency lint owns
  the declaration<->provenance symmetry check (EP-INV-4), not this shape gate.
- `experiment_provenance: null` or `[]`: OK, exit 0 (nothing to shape-check).
- Any entry failing the schema: ERROR, exit 1.

Exit codes:
    0   no shape violations
    1   one or more entries fail the entry schema
    2   internal error (file not found / malformed YAML / schema missing)
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import yaml
from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parent.parent
ENTRY_SCHEMA = (
    REPO_ROOT / "shared/contracts/passport/experiment_provenance_entry.schema.json"
)


def _validator() -> Draft202012Validator:
    schema = json.loads(ENTRY_SCHEMA.read_text(encoding="utf-8"))
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(
        schema, format_checker=Draft202012Validator.FORMAT_CHECKER
    )


def validate_provenance(entries: object) -> list[str]:
    """Validate each experiment_provenance[] entry against the entry schema.

    Returns a list of human-readable error strings (empty == clean).
    """
    errors: list[str] = []
    if entries is None:
        return errors  # explicit null opt-out — nothing to shape-check
    if not isinstance(entries, list):
        return [
            f"experiment_provenance must be a list (or absent/null); got {type(entries).__name__}"
        ]

    validator = _validator()
    for i, entry in enumerate(entries):
        if not isinstance(entry, dict):
            errors.append(f"experiment_provenance[{i}]: entry must be a mapping; got {type(entry).__name__}")
            continue
        for err in sorted(validator.iter_errors(entry), key=lambda e: list(e.absolute_path)):
            loc = ".".join(str(p) for p in err.absolute_path) or "<root>"
            errors.append(f"experiment_provenance[{i}] {loc}: {err.message}")

    return errors


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("passport", type=Path)
    args = parser.parse_args(argv)

    try:
        doc = yaml.safe_load(args.passport.read_text(encoding="utf-8"))
    except FileNotFoundError:
        print(f"ERROR: passport not found: {args.passport}", file=sys.stderr)
        return 2
    except Exception as exc:
        print(f"ERROR: failed to load {args.passport}: {exc}", file=sys.stderr)
        return 2

    if not isinstance(doc, dict):
        print(f"ERROR: {args.passport}: top-level must be a mapping", file=sys.stderr)
        return 2

    if "experiment_provenance" not in doc:
        print("OK: no experiment_provenance[] aggregate (optional).")
        return 0

    errors = validate_provenance(doc["experiment_provenance"])
    if errors:
        for e in errors:
            print(f"ERROR: {e}")
        print(
            f"\n{len(errors)} shape violation(s). See "
            f"shared/contracts/passport/experiment_provenance_entry.schema.json.",
            file=sys.stderr,
        )
        return 1

    print("OK: experiment_provenance[] entries are well-formed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
