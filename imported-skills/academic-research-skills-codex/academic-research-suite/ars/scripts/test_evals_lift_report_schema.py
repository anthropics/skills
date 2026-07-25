"""Schema tests for shared/evals_lift_report.schema.json (#184 Delta 2).

Includes the mandatory TRIVIAL-ACCEPT-ALL mutation: swapping the schema for
``{}`` must make a known-bad report validate, proving the real schema's
constraints are load-bearing.
"""
from __future__ import annotations

import copy
import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[1]
SCHEMA_PATH = REPO_ROOT / "shared" / "evals_lift_report.schema.json"


@pytest.fixture(scope="module")
def schema():
    return json.loads(SCHEMA_PATH.read_text(encoding="utf-8"))


@pytest.fixture(scope="module")
def validator(schema):
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def _valid_report():
    return {
        "harness_version": "1.0.0",
        "run_id": "20260531T000000Z-abcd1234",
        "gold_set_version": "1.0.0",
        "per_task": [
            {
                "task_name": "citation_extraction",
                "manifest_version": "1.0.0",
                "status": "measured",
                "sample_n": 50,
                "aggregate_metric": {
                    "metric": "accuracy", "value": 1.0,
                    "direction": "higher_is_better",
                    "threshold_value": 0.90, "comparison": ">=", "passed": True,
                },
                "per_class": [
                    {"class_name": "true", "metric": "accuracy", "value": 1.0,
                     "direction": "higher_is_better", "support": 30, "passed": True},
                ],
                "expert_concordance": [
                    {"class_name": "true", "agreement_rate": 1.0,
                     "labeled_count": 5, "agreements": 5},
                ],
            }
        ],
        "caveats": ["Synthetic gold set; concordance advisory only."],
    }


def test_valid_report_passes(validator):
    assert sorted(validator.iter_errors(_valid_report()), key=lambda e: str(e.path)) == []


def test_is_valid_draft_2020_12_schema(schema):
    # Must not raise.
    Draft202012Validator.check_schema(schema)
    assert schema["$schema"] == "https://json-schema.org/draft/2020-12/schema"


def test_rejects_missing_required_field(validator):
    bad = _valid_report()
    del bad["run_id"]
    assert validator.iter_errors(bad)
    assert not validator.is_valid(bad)


def test_rejects_empty_caveats(validator):
    bad = _valid_report()
    bad["caveats"] = []  # minItems: 1
    assert not validator.is_valid(bad)


def test_rejects_additional_top_level_property(validator):
    bad = _valid_report()
    bad["unexpected"] = True
    assert not validator.is_valid(bad)


def test_rejects_per_task_missing_aggregate_metric(validator):
    bad = _valid_report()
    del bad["per_task"][0]["aggregate_metric"]
    assert not validator.is_valid(bad)


def test_trivial_accept_all_mutation_proves_constraints_load_bearing():
    # Swap the real schema for {} (accept-all). A known-bad report (empty
    # caveats + missing run_id) THEN validates, proving the real schema's
    # required/minItems constraints are doing the work.
    known_bad = _valid_report()
    known_bad["caveats"] = []
    del known_bad["run_id"]

    real = json.loads(SCHEMA_PATH.read_text(encoding="utf-8"))
    assert not Draft202012Validator(real).is_valid(known_bad)  # real schema rejects

    accept_all = {}
    assert Draft202012Validator(accept_all).is_valid(known_bad)  # mutant accepts
