"""Drift guard: the nested repro_lock sub-shape in
experiment_provenance_entry.schema.json MUST stay in sync with the canonical
field set in scripts/repro_lock_validation.py (#260 D1 drift guard).

The repro_lock shape is now declared in TWO places:
  1. scripts/repro_lock_validation.py REQUIRED_* constants (single source of
     truth, also imported by scripts/check_repro_lock.py).
  2. The nested `repro_lock` sub-object inside
     shared/contracts/passport/experiment_provenance_entry.schema.json (each
     experiment_provenance[] entry carries its own lock).

Without this test the two copies silently diverge over time — a field added to
the standalone validator but forgotten in the nested schema (or vice versa)
would pass every other gate. This test asserts the required-key sets are equal
at the top level AND inside each sub-block, so the two declarations cannot drift.

Run:
    python -m unittest scripts.test_repro_lock_validation_drift -v
"""
from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO / "scripts"))

from repro_lock_validation import (  # noqa: E402
    REQUIRED_CROSSMODEL,
    REQUIRED_EXTERNAL,
    REQUIRED_FIELDS,
    REQUIRED_MATERIALS,
    REQUIRED_MODEL,
    REQUIRED_PROMPTS,
)

ENTRY_SCHEMA = REPO / "shared/contracts/passport/experiment_provenance_entry.schema.json"


def _nested_repro_lock() -> dict:
    schema = json.loads(ENTRY_SCHEMA.read_text(encoding="utf-8"))
    return schema["properties"]["repro_lock"]


class ReproLockDriftTest(unittest.TestCase):
    """The nested schema's required keys equal the shared canonical constants."""

    def setUp(self) -> None:
        self.lock = _nested_repro_lock()

    def test_top_level_required_matches_canonical(self) -> None:
        nested = set(self.lock["required"])
        self.assertEqual(
            nested,
            REQUIRED_FIELDS,
            msg="nested repro_lock top-level required drifted from "
            f"repro_lock_validation.REQUIRED_FIELDS: only-in-schema="
            f"{nested - REQUIRED_FIELDS}, only-in-constant={REQUIRED_FIELDS - nested}",
        )

    def test_sub_block_required_match_canonical(self) -> None:
        cases = {
            "model": REQUIRED_MODEL,
            "prompts": REQUIRED_PROMPTS,
            "materials": REQUIRED_MATERIALS,
            "external_protocols": REQUIRED_EXTERNAL,
            "cross_model": REQUIRED_CROSSMODEL,
        }
        for block, expected in cases.items():
            with self.subTest(block=block):
                nested = set(self.lock["properties"][block]["required"])
                self.assertEqual(
                    nested,
                    expected,
                    msg=f"nested repro_lock.{block}.required drifted: "
                    f"only-in-schema={nested - expected}, only-in-constant={expected - nested}",
                )

    def test_check_repro_lock_imports_shared_constant(self) -> None:
        """check_repro_lock.py re-exports the shared constant (no duplicate copy).

        Pins that the standalone validator imports from repro_lock_validation
        rather than re-declaring REQUIRED_FIELDS — the drift guard is only sound
        if BOTH copies trace back to the single source.
        """
        import check_repro_lock

        self.assertIs(
            check_repro_lock.REQUIRED_FIELDS,
            REQUIRED_FIELDS,
            msg="check_repro_lock.REQUIRED_FIELDS is not the shared "
            "repro_lock_validation.REQUIRED_FIELDS object — a duplicate copy "
            "would defeat the drift guard.",
        )


if __name__ == "__main__":
    unittest.main()
