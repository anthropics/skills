"""Unit tests for check_field_norm_severity.py (#215).

The #215 gold set is a first-party REGRESSION FIXTURE, not a detector calibration
set: there is no deterministic predictor for field-norm severity miscalibration.
So the lint validates DATA INTEGRITY + first-party PROVENANCE, not FNR/FPR. These
tests drive the validator against in-memory fixtures and the shipped gold set.
"""
from __future__ import annotations

import copy
import json
import unittest
from pathlib import Path

from scripts import check_field_norm_severity as cfns


def _load_shipped() -> dict:
    return json.loads(
        (
            Path(__file__).resolve().parents[1]
            / "evals/gold/field_norm_severity/gold_set.json"
        ).read_text(encoding="utf-8")
    )


class TestShippedGoldSet(unittest.TestCase):
    """The shipped gold set must pass all integrity/provenance invariants."""

    def test_shipped_gold_set_is_clean(self) -> None:
        errors = cfns.validate(_load_shipped())
        self.assertEqual(errors, [], msg=f"shipped gold set has violations: {errors!r}")

    def test_shipped_has_required_counts(self) -> None:
        data = _load_shipped()
        subtypes = [it["subtype"] for it in data["items"]]
        self.assertGreaterEqual(
            subtypes.count("field_norm_boundary"), 5, "need >=5 W1-shape cases"
        )
        self.assertGreaterEqual(
            subtypes.count("significance_boundary"), 5, "need >=5 F.3.4-shape cases"
        )


class TestValidatorInvariants(unittest.TestCase):
    """Drive the validator against mutated copies of the shipped gold set so every
    assertion is shown to be non-vacuous (it RED-s when the invariant is broken)."""

    def setUp(self) -> None:
        self.data = _load_shipped()

    def _mutate(self, fn) -> list[str]:
        data = copy.deepcopy(self.data)
        fn(data)
        return cfns.validate(data)

    def test_missing_provenance_section_fails(self) -> None:
        errors = self._mutate(lambda d: d["items"][0]["provenance"].pop("section"))
        self.assertTrue(
            any("provenance" in e and "section" in e for e in errors),
            msg=f"expected missing-section provenance error: {errors!r}",
        )

    def test_missing_verbatim_anchor_fails(self) -> None:
        errors = self._mutate(lambda d: d["items"][0]["provenance"].pop("verbatim_anchor"))
        self.assertTrue(
            any("verbatim_anchor" in e for e in errors),
            msg=f"expected missing-anchor error: {errors!r}",
        )

    def test_empty_verbatim_anchor_fails(self) -> None:
        errors = self._mutate(
            lambda d: d["items"][0]["provenance"].__setitem__("verbatim_anchor", "")
        )
        self.assertTrue(
            any("verbatim_anchor" in e for e in errors),
            msg=f"expected empty-anchor error: {errors!r}",
        )

    def test_missing_paper_citation_fails(self) -> None:
        errors = self._mutate(lambda d: d["items"][0]["provenance"].pop("paper_citation"))
        self.assertTrue(
            any("paper_citation" in e for e in errors),
            msg=f"expected missing-citation error: {errors!r}",
        )

    def test_unknown_subtype_fails(self) -> None:
        errors = self._mutate(lambda d: d["items"][0].__setitem__("subtype", "made_up"))
        self.assertTrue(
            any("subtype" in e and "made_up" in e for e in errors),
            msg=f"expected unknown-subtype error: {errors!r}",
        )

    def test_severity_miscalibration_must_be_true(self) -> None:
        errors = self._mutate(
            lambda d: d["items"][0].__setitem__("severity_miscalibration", False)
        )
        self.assertTrue(
            any("severity_miscalibration" in e for e in errors),
            msg=f"expected severity flag error: {errors!r}",
        )

    def test_duplicate_id_fails(self) -> None:
        errors = self._mutate(
            lambda d: d["items"][1].__setitem__("id", d["items"][0]["id"])
        )
        self.assertTrue(
            any("duplicate" in e.lower() and "id" in e.lower() for e in errors),
            msg=f"expected duplicate-id error: {errors!r}",
        )

    def test_exception_item_requires_reason(self) -> None:
        """An item flagged exception=true must carry an exception_reason (the SAR case);
        dropping the reason while keeping the flag must fail."""
        def drop_reason(d: dict) -> None:
            for it in d["items"]:
                if it.get("exception") is True:
                    it.pop("exception_reason")

        errors = self._mutate(drop_reason)
        self.assertTrue(
            any("exception_reason" in e for e in errors),
            msg=f"expected missing exception_reason error: {errors!r}",
        )

    def test_non_exception_item_must_not_carry_reason(self) -> None:
        """exception_reason on a non-exception item is a labeling error (it implies the
        item is contextual when the flag says it is clean)."""
        errors = self._mutate(
            lambda d: d["items"][0].__setitem__("exception_reason", "stray")
        )
        self.assertTrue(
            any("exception_reason" in e for e in errors),
            msg=f"expected stray exception_reason error: {errors!r}",
        )

    def test_exception_id_losing_both_flag_and_reason_fails(self) -> None:
        """codex P1: if the SAR item loses BOTH its exception flag and its reason, the paired
        check is satisfied (both branches false) and the case silently reverts to a clean
        positive. The id-suffix guard must still fail — the declared exception stays contextual."""
        def strip_exception(d: dict) -> None:
            for it in d["items"]:
                if str(it.get("id", "")).endswith("-exception"):
                    it.pop("exception", None)
                    it.pop("exception_reason", None)

        errors = self._mutate(strip_exception)
        self.assertTrue(
            any("-exception" in e and "exception is not true" in e for e in errors),
            msg=f"expected exception-id guard error: {errors!r}",
        )

    def test_missing_field_norm_fails(self) -> None:
        errors = self._mutate(lambda d: d["items"][0].pop("field_norm"))
        self.assertTrue(
            any("field_norm" in e for e in errors),
            msg=f"expected missing field_norm error: {errors!r}",
        )

    def test_metadata_missing_regression_fixture_disclaimer_fails(self) -> None:
        """The metadata MUST state this is a regression fixture, not a calibrated
        threshold set (codex P2: do not claim distributional calibration from n=10)."""
        errors = self._mutate(
            lambda d: d["metadata"].__setitem__("task_type", "advisory-calibration")
        )
        self.assertTrue(
            any("task_type" in e or "regression" in e.lower() for e in errors),
            msg=f"expected task_type-not-regression error: {errors!r}",
        )


if __name__ == "__main__":
    unittest.main()
