#!/usr/bin/env python3
"""Validate a Material Passport YAML's `repro_lock` sub-block.

Usage: python scripts/check_repro_lock.py path/to/passport.yaml

- Missing `repro_lock` key (not even null): ERROR, exit 1.
- `repro_lock: null`: WARN, exit 0 (honest opt-out).
- Populated block with all required sub-fields: OK, exit 0.
- Populated block with missing sub-field or unknown schema_version: ERROR, exit 1.
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

import yaml

# Canonical repro_lock field set + shape validator are single-sourced in
# repro_lock_validation.py so the nested copy in
# experiment_provenance_entry.schema.json (#260) cannot silently drift from
# this standalone validator. The drift test asserts the two stay in sync.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from repro_lock_validation import (  # noqa: E402
    REQUIRED_FIELDS,  # re-exported for backward compat / external importers
    SUPPORTED_HASH_TIMINGS,
    SUPPORTED_SCHEMA_VERSIONS,
    validate_block,
)

__all__ = [
    "REQUIRED_FIELDS",
    "SUPPORTED_HASH_TIMINGS",
    "SUPPORTED_SCHEMA_VERSIONS",
    "validate_block",
    "main",
]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("passport", type=Path)
    args = parser.parse_args()

    try:
        doc = yaml.safe_load(args.passport.read_text(encoding="utf-8"))
    except Exception as exc:
        print(f"ERROR: failed to load {args.passport}: {exc}")
        return 1

    if not isinstance(doc, dict):
        print(f"ERROR: {args.passport}: top-level must be a mapping")
        return 1

    if "repro_lock" not in doc:
        print("ERROR: repro_lock key is missing. Set 'repro_lock: null' to opt out explicitly.")
        return 1

    lock = doc["repro_lock"]
    if lock is None:
        print("WARN: repro_lock is null — honest opt-out. Reproducibility reduced.", file=sys.stderr)
        print("OK (with WARN): passport valid; repro_lock explicitly null — see stderr.", flush=True)
        return 0

    if not isinstance(lock, dict):
        print(f"ERROR: repro_lock must be null or a mapping, got {type(lock).__name__}")
        return 1

    errors = validate_block(lock)
    if errors:
        for e in errors:
            print(f"ERROR: {e}")
        print(
            f"\n{len(errors)} violation(s). "
            f"See shared/artifact_reproducibility_pattern.md for required fields.",
            file=sys.stderr,
        )
        return 1

    print("OK: passport repro_lock is valid.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
