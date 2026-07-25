#!/usr/bin/env python3
"""#268 nested-object Commitment Ledger lint.

Enforces the structural invariants of the Schema 11 Commitment Ledger after the
parallel-list -> nested-object refactor (#268). Runs alongside the existing Kong
A1 / #269 surfaces; no JSON-schema exists for Schema 11, so this lint operates on
the calibration seed YAML plus a cascade-completeness scan of the two prose
surfaces that previously carried index notation.

Invariants (spec docs/design/2026-05-31-ars-268-schema11-nested-commitment-ledger-spec.md §6):

  N1  every expected_commitments[] entry in the seed is a mapping carrying
      commitment_text + commitment_type + required_evidence_type.
  N2  the seed carries NO top-level expected_fulfillment_status /
      expected_unfulfilled_rationale parallel lists on any case (regression guard
      against the retired A1 parallel-list shape).
  N3  for each expected_commitments entry: fulfillment_status (if present) is in
      the enum; unfulfilled_rationale, WHEN PRESENT, must be non-empty on a
      non-fulfilled status and absent on a fulfilled one (no "" placeholder). A
      non-fulfilled commitment MAY omit unfulfilled_rationale entirely — that is
      the valid COMMITMENT_GAP case (e.g. seed N1/N2), not a violation.
  N3b the case-level expected_commitment_gap oracle agrees with the per-commitment
      shape: gap fires iff some commitment is non-fulfilled with a blank/absent
      rationale.
  N4  the Schema 11 prose (shared/handoff_schemas.md) contains no surviving
      `fulfillment_status[i]` / `unfulfilled_rationale[i]` index notation.
  N5  re_review_mode_protocol Commitment Ledger Verification contains no surviving
      index notation either.

Exit 0 on success, 1 on any violation (CI gate).
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

import yaml

REPO = Path(__file__).resolve().parent.parent
SEED = REPO / "evals/calibration/commitment_ledger_seed.yaml"
SCHEMA = REPO / "shared/handoff_schemas.md"
RE_REVIEW = REPO / "academic-paper-reviewer/references/re_review_mode_protocol.md"

EXTRACTION_FIELDS = ("commitment_text", "commitment_type", "required_evidence_type")
STATUS_ENUM = {"fulfilled", "partial", "not-fulfilled", "explicitly-rejected-with-rationale"}
NONFULFILLED = STATUS_ENUM - {"fulfilled"}  # derived so the two stay in sync

# Index-notation regex: a retired parallel-list field name immediately followed by
# a subscript like [i] or [0]. Catches parallel-list-era prose the refactor must
# remove. Tombstone check for the two fields #268 retired — add any further field
# names here whenever a later schema refactor retires an index-notation field.
INDEX_NOTATION = re.compile(r"\b(?:fulfillment_status|unfulfilled_rationale)\s*\[\s*\w+\s*\]")


def _blank_rationale(com: dict) -> bool:
    """True when a commitment's unfulfilled_rationale is missing, null, or whitespace.

    `com.get(key, "")` returns None (not "") when the key is present with a YAML-null
    value, and `str(None)` is the truthy "None" — so a bare `unfulfilled_rationale:`
    would falsely read as populated. Treat missing / None / blank uniformly here.
    """
    val = com.get("unfulfilled_rationale")
    return val is None or not str(val).strip()


def check_seed(seed: dict) -> list[str]:
    """N1 + N2 + N3 + N3b against a parsed seed mapping."""
    errors: list[str] = []
    cases = seed.get("cases", [])
    if not cases:
        errors.append("seed carries no cases")
        return errors
    for case in cases:
        cid = case.get("case_id", "<no-id>")

        # N2: no retired parallel-list keys on the case.
        for legacy in ("expected_fulfillment_status", "expected_unfulfilled_rationale"):
            if legacy in case:
                errors.append(f"N2 {cid}: retired parallel-list key `{legacy}` present")

        commitments = case.get("expected_commitments", [])
        for idx, com in enumerate(commitments):
            where = f"{cid}[{idx}]"
            if not isinstance(com, dict):
                errors.append(f"N1 {where}: commitment entry is not a mapping")
                continue
            # N1: extraction fields present.
            for field in EXTRACTION_FIELDS:
                if field not in com:
                    errors.append(f"N1 {where}: missing extraction field `{field}`")

            # N3: lifecycle coherence.
            status = com.get("fulfillment_status")
            has_rationale = "unfulfilled_rationale" in com
            if status is not None:
                if status not in STATUS_ENUM:
                    errors.append(f"N3 {where}: fulfillment_status `{status}` not in enum")
                if status == "fulfilled" and has_rationale:
                    errors.append(
                        f"N3 {where}: fulfilled commitment carries unfulfilled_rationale "
                        "(omit it — no \"\" placeholder in nested shape)"
                    )
                if status in NONFULFILLED and has_rationale and _blank_rationale(com):
                    errors.append(
                        f"N3 {where}: non-fulfilled status `{status}` carries empty "
                        "unfulfilled_rationale (must be non-empty, or omit the key to trigger gap)"
                    )
            elif has_rationale:
                errors.append(
                    f"N3 {where}: unfulfilled_rationale present without fulfillment_status"
                )

        # N3b: the case-level expected_commitment_gap oracle must agree with the
        # per-commitment shape. COMMITMENT_GAP fires iff some commitment is
        # non-fulfilled with a missing/empty rationale (re_review_mode_protocol).
        # Validate the oracle so a future seed can't carry an incoherent flag.
        if "expected_commitment_gap" in case:
            expected_gap = case["expected_commitment_gap"]
            if not isinstance(expected_gap, bool):
                # A quoted "false" / "true" would coerce truthy under bool() and
                # silently pass the oracle check — require a real YAML boolean.
                errors.append(
                    f"N3b {cid}: expected_commitment_gap must be a boolean, got "
                    f"{type(expected_gap).__name__} ({expected_gap!r})"
                )
            actual_gap = any(
                isinstance(com, dict)
                and com.get("fulfillment_status") in NONFULFILLED
                and _blank_rationale(com)
                for com in commitments
            )
            if isinstance(expected_gap, bool) and actual_gap != expected_gap:
                errors.append(
                    f"N3b {cid}: expected_commitment_gap={expected_gap} "
                    f"contradicts per-commitment shape (actual gap={actual_gap})"
                )
    return errors


def check_index_notation(label: str, text: str) -> list[str]:
    """N4 / N5: no surviving index-notation in the prose surface."""
    errors: list[str] = []
    for m in INDEX_NOTATION.finditer(text):
        line_no = text.count("\n", 0, m.start()) + 1
        errors.append(f"{label}:{line_no}: surviving index notation `{m.group(0)}`")
    return errors


def main() -> int:
    errors: list[str] = []

    if not SEED.exists():
        errors.append(f"missing seed file: {SEED}")
    else:
        errors += check_seed(yaml.safe_load(SEED.read_text(encoding="utf-8")))

    if not SCHEMA.exists():
        errors.append(f"missing schema file: {SCHEMA}")
    else:
        errors += check_index_notation("N4 shared/handoff_schemas.md", SCHEMA.read_text(encoding="utf-8"))

    if not RE_REVIEW.exists():
        errors.append(f"missing re-review protocol: {RE_REVIEW}")
    else:
        errors += check_index_notation(
            "N5 re_review_mode_protocol.md", RE_REVIEW.read_text(encoding="utf-8")
        )

    if errors:
        print("#268 nested-commitment-ledger lint FAILED:")
        for e in errors:
            print(f"  - {e}")
        return 1
    print("#268 nested-commitment-ledger lint OK (N1-N5)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
