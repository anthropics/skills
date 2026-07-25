#!/usr/bin/env python3
"""Mutation tests for check_268_nested_commitment_ledger.

Each invariant is exercised against a deliberately-mutated in-memory fixture to
confirm it FAILs — guarding against a trivial accept-all regression
(feedback_schema_mutation_test_for_constraints). The clean fixture must PASS.
"""
from __future__ import annotations

import copy
import unittest

import scripts.check_268_nested_commitment_ledger as lint


CLEAN_SEED = {
    "cases": [
        {
            "case_id": "F1",
            "expected_commitments": [
                {
                    "commitment_text": "add ablation on CIFAR-100",
                    "commitment_type": "add_experiment",
                    "required_evidence_type": "new_table",
                    "fulfillment_status": "fulfilled",
                }
            ],
            "expected_commitment_gap": False,
        },
        {
            "case_id": "P2",
            "expected_commitments": [
                {
                    "commitment_text": "add ImageNet experiments",
                    "commitment_type": "add_experiment",
                    "required_evidence_type": "new_table",
                    "fulfillment_status": "not-fulfilled",
                    "unfulfilled_rationale": "deferred — compute budget; acknowledged in §6.",
                },
                {
                    "commitment_text": "add CIFAR-100 experiments",
                    "commitment_type": "add_experiment",
                    "required_evidence_type": "new_table",
                    "fulfillment_status": "fulfilled",
                },
            ],
            "expected_commitment_gap": False,
        },
        {
            "case_id": "N1",
            "expected_commitments": [
                {
                    "commitment_text": "add error bars across 5 seeds",
                    "commitment_type": "add_experiment",
                    "required_evidence_type": "new_figure",
                    "fulfillment_status": "not-fulfilled",
                    # unfulfilled_rationale omitted → COMMITMENT_GAP trigger (valid)
                }
            ],
            "expected_commitment_gap": True,
        },
    ]
}

CLEAN_PROSE = "A commitment object with fulfillment_status fulfilled carries no rationale."


class TestCleanPasses(unittest.TestCase):
    def test_clean_seed_passes(self):
        self.assertEqual(lint.check_seed(copy.deepcopy(CLEAN_SEED)), [])

    def test_clean_prose_passes(self):
        self.assertEqual(lint.check_index_notation("x", CLEAN_PROSE), [])


class TestRealFiles(unittest.TestCase):
    def test_real_files_pass(self):
        # The shipped artifacts must satisfy the lint end-to-end (hits disk).
        self.assertEqual(lint.main(), 0)


class TestN1MissingField(unittest.TestCase):
    def test_missing_commitment_type_fails(self):
        seed = copy.deepcopy(CLEAN_SEED)
        del seed["cases"][0]["expected_commitments"][0]["commitment_type"]
        errs = lint.check_seed(seed)
        self.assertTrue(any("N1" in e and "commitment_type" in e for e in errs), errs)

    def test_non_mapping_commitment_fails(self):
        seed = copy.deepcopy(CLEAN_SEED)
        seed["cases"][0]["expected_commitments"][0] = "not a mapping"
        errs = lint.check_seed(seed)
        self.assertTrue(
            any("N1" in e and "commitment entry is not a mapping" in e for e in errs), errs
        )


class TestN2ReintroducedParallelList(unittest.TestCase):
    def test_parallel_status_list_fails(self):
        seed = copy.deepcopy(CLEAN_SEED)
        seed["cases"][0]["expected_fulfillment_status"] = ["fulfilled"]
        errs = lint.check_seed(seed)
        self.assertTrue(any("N2" in e and "expected_fulfillment_status" in e for e in errs), errs)

    def test_parallel_rationale_list_fails(self):
        seed = copy.deepcopy(CLEAN_SEED)
        seed["cases"][0]["expected_unfulfilled_rationale"] = [""]
        errs = lint.check_seed(seed)
        self.assertTrue(any("N2" in e and "expected_unfulfilled_rationale" in e for e in errs), errs)


class TestN3LifecycleCoherence(unittest.TestCase):
    def test_fulfilled_with_rationale_fails(self):
        seed = copy.deepcopy(CLEAN_SEED)
        seed["cases"][0]["expected_commitments"][0]["unfulfilled_rationale"] = "should not be here"
        errs = lint.check_seed(seed)
        self.assertTrue(any("N3" in e and "fulfilled commitment carries" in e for e in errs), errs)

    def test_nonfulfilled_with_empty_rationale_fails(self):
        seed = copy.deepcopy(CLEAN_SEED)
        # P2 first commitment is not-fulfilled with rationale; blank it out.
        seed["cases"][1]["expected_commitments"][0]["unfulfilled_rationale"] = "   "
        errs = lint.check_seed(seed)
        self.assertTrue(any("N3" in e and "empty" in e for e in errs), errs)

    def test_nonfulfilled_with_null_rationale_fails(self):
        # A bare `unfulfilled_rationale:` (YAML null) must not read as populated
        # via the str(None) == "None" trap — it is a present-but-blank key.
        seed = copy.deepcopy(CLEAN_SEED)
        seed["cases"][1]["expected_commitments"][0]["unfulfilled_rationale"] = None
        errs = lint.check_seed(seed)
        self.assertTrue(any("N3" in e and "empty" in e for e in errs), errs)

    def test_bad_status_enum_fails(self):
        seed = copy.deepcopy(CLEAN_SEED)
        seed["cases"][0]["expected_commitments"][0]["fulfillment_status"] = "kinda-done"
        errs = lint.check_seed(seed)
        self.assertTrue(any("N3" in e and "not in enum" in e for e in errs), errs)

    def test_rationale_without_status_fails(self):
        seed = copy.deepcopy(CLEAN_SEED)
        com = seed["cases"][0]["expected_commitments"][0]
        del com["fulfillment_status"]
        com["unfulfilled_rationale"] = "orphan rationale"
        errs = lint.check_seed(seed)
        self.assertTrue(any("N3" in e and "without fulfillment_status" in e for e in errs), errs)


class TestN3bGapOracleCoherence(unittest.TestCase):
    def test_false_gap_on_silent_omission_fails(self):
        # N1 (not-fulfilled, no rationale) genuinely SHOULD gap; flipping its
        # oracle to False must be caught.
        seed = copy.deepcopy(CLEAN_SEED)
        n1 = next(c for c in seed["cases"] if c["case_id"] == "N1")
        n1["expected_commitment_gap"] = False
        errs = lint.check_seed(seed)
        self.assertTrue(any("N3b" in e and "N1" in e for e in errs), errs)

    def test_true_gap_on_fully_fulfilled_fails(self):
        # F1 is fully fulfilled (no gap); claiming a gap must be caught.
        seed = copy.deepcopy(CLEAN_SEED)
        f1 = next(c for c in seed["cases"] if c["case_id"] == "F1")
        f1["expected_commitment_gap"] = True
        errs = lint.check_seed(seed)
        self.assertTrue(any("N3b" in e and "F1" in e for e in errs), errs)

    def test_quoted_boolean_gap_flag_fails(self):
        # A quoted "false" on a genuine-gap case would coerce truthy under bool();
        # the oracle must reject non-boolean expected_commitment_gap outright.
        seed = copy.deepcopy(CLEAN_SEED)
        n1 = next(c for c in seed["cases"] if c["case_id"] == "N1")
        n1["expected_commitment_gap"] = "false"
        errs = lint.check_seed(seed)
        self.assertTrue(any("N3b" in e and "must be a boolean" in e for e in errs), errs)


class TestN4N5IndexNotation(unittest.TestCase):
    def test_fulfillment_status_index_fails(self):
        errs = lint.check_index_notation("x", "where fulfillment_status[i] is empty")
        self.assertTrue(any("index notation" in e for e in errs), errs)

    def test_unfulfilled_rationale_index_fails(self):
        errs = lint.check_index_notation("x", "the unfulfilled_rationale[0] placeholder")
        self.assertTrue(any("index notation" in e for e in errs), errs)

    def test_legacy_array_description_passes(self):
        # The schema's legacy-normalization note references `fulfillment_status: [...]`
        # (array literal, not a subscript) — that must NOT trip the index regex.
        errs = lint.check_index_notation("x", "old top-level `fulfillment_status: [...]` arrays")
        self.assertEqual(errs, [])


if __name__ == "__main__":
    unittest.main()
