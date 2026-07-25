#!/usr/bin/env python3
"""Integrity + provenance validator for the #215 field-norm severity gold set.

This gold set is a first-party REGRESSION FIXTURE, not a detector calibration set.
There is no deterministic predictor for "field-norm severity miscalibration" — it
requires domain judgment — so this validator deliberately does NOT compute FNR/FPR
or pretend to be a detector (that would be fluent-wrongness: a calibration ritual
with no predictor behind it). Instead it enforces that every case is structurally
complete and carries stable first-party provenance back to the source paper, so the
fixture stays traceable and cannot silently drift into fabricated cases.

Usage:
    python -m scripts.check_field_norm_severity [gold_set.json]

Exit 0 = clean, 1 = violations (printed one per line to stderr).
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_GOLD_SET = REPO_ROOT / "evals/gold/field_norm_severity/gold_set.json"

VALID_SUBTYPES = {"field_norm_boundary", "significance_boundary"}
REQUIRED_PROVENANCE_KEYS = ("section", "paper_citation", "verbatim_anchor")
# An id ending in this suffix declares itself a contextual exception case (the SAR
# 11.7T case the paper marks ambiguous). The flag must then actually be set — otherwise
# the case silently reverts to a clean positive, the exact fidelity error this guards.
EXCEPTION_ID_SUFFIX = "-exception"
# The fixture must self-identify as a regression fixture (codex review P2): with n=10
# and no deterministic predictor, it must not claim distributional calibration.
REQUIRED_TASK_TYPE = "regression-fixture"


def validate(data: dict[str, Any]) -> list[str]:
    """Return a list of violation messages. Empty list = clean."""
    errors: list[str] = []

    metadata = data.get("metadata")
    if not isinstance(metadata, dict):
        errors.append("metadata: missing or not an object")
        metadata = {}
    task_type = metadata.get("task_type")
    if task_type != REQUIRED_TASK_TYPE:
        errors.append(
            f"metadata.task_type={task_type!r} must be {REQUIRED_TASK_TYPE!r} "
            f"(this is a regression fixture, not a calibrated threshold set)"
        )

    items = data.get("items")
    if not isinstance(items, list) or not items:
        errors.append("items: missing or empty list")
        return errors

    seen_ids: set[str] = set()
    for idx, item in enumerate(items):
        item_id = item.get("id")
        where = item_id if isinstance(item_id, str) and item_id.strip() else f"<index {idx}>"

        if not isinstance(item_id, str) or not item_id.strip():
            errors.append(f"{where}: missing non-empty id")
        elif item_id in seen_ids:
            errors.append(f"{where}: duplicate id {item_id!r}")
        else:
            seen_ids.add(item_id)

        if item.get("severity_miscalibration") is not True:
            errors.append(
                f"{where}: severity_miscalibration must be true "
                f"(every gold case is a documented miscalibration)"
            )

        subtype = item.get("subtype")
        if subtype not in VALID_SUBTYPES:
            errors.append(
                f"{where}: subtype={subtype!r} not in {sorted(VALID_SUBTYPES)}"
            )

        field_norm = item.get("field_norm")
        if not isinstance(field_norm, str) or not field_norm.strip():
            errors.append(f"{where}: missing non-empty field_norm")

        prov = item.get("provenance")
        if not isinstance(prov, dict):
            errors.append(f"{where}: missing provenance object")
        else:
            for key in REQUIRED_PROVENANCE_KEYS:
                val = prov.get(key)
                if not isinstance(val, str) or not val.strip():
                    errors.append(
                        f"{where}: provenance.{key} missing or empty "
                        f"(first-party provenance is required; no untraceable cases)"
                    )

        # exception flag <-> exception_reason must be paired both ways: a contextual
        # case (SAR) must explain why it is non-clean; a clean case must not carry a
        # stray reason that implies it is contextual.
        is_exception = item.get("exception") is True
        has_reason = bool(str(item.get("exception_reason", "")).strip())
        if is_exception and not has_reason:
            errors.append(
                f"{where}: exception=true but exception_reason missing/empty"
            )
        if not is_exception and has_reason:
            errors.append(
                f"{where}: exception_reason present but exception is not true"
            )

        # An id that declares itself an exception case MUST carry exception=true. Without
        # this an exception item that loses BOTH its flag and reason passes the paired
        # check above (both branches false) and silently reverts to a clean positive —
        # the SAR fidelity error this fixture exists to prevent.
        if isinstance(item_id, str) and item_id.endswith(EXCEPTION_ID_SUFFIX) and not is_exception:
            errors.append(
                f"{where}: id ends in {EXCEPTION_ID_SUFFIX!r} but exception is not true "
                f"(a declared exception case must stay marked contextual)"
            )

    return errors


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("gold_set", nargs="?", type=Path, default=DEFAULT_GOLD_SET)
    args = parser.parse_args(argv)

    data = json.loads(args.gold_set.read_text(encoding="utf-8"))
    errors = validate(data)
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    n = len(data.get("items", []))
    print(f"field_norm_severity: {n} cases, all integrity/provenance invariants pass")
    return 0


if __name__ == "__main__":
    sys.exit(main())
