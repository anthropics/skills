#!/usr/bin/env python3
"""Tests for check_394_submission_policy.py (#394 slice 4, plan D5).

Mutation discipline: every invariant has a passing case against the real
tree artifacts and a failing case proving the check fires when the guarded
property is broken.
"""
from __future__ import annotations

import json
import re

import pytest

from check_394_submission_policy import (
    FORMATTER,
    ORCHESTRATOR,
    REPORT_SCHEMA,
    TP_SCHEMA,
    VERIFIER,
    check_formatter,
    check_orchestrator,
    check_report_schema,
    check_tp_schema,
    check_verifier_single_homed,
    find_terminal_policies_access,
)


@pytest.fixture(scope="module")
def tp_schema():
    return json.loads(TP_SCHEMA.read_text(encoding="utf-8"))


@pytest.fixture(scope="module")
def report_schema():
    return json.loads(REPORT_SCHEMA.read_text(encoding="utf-8"))


@pytest.fixture(scope="module")
def orchestrator_text():
    return ORCHESTRATOR.read_text(encoding="utf-8")


@pytest.fixture(scope="module")
def formatter_text():
    return FORMATTER.read_text(encoding="utf-8")


# --- invariant 1: terminal_policies schema ----------------------------------

def test_tp_schema_real_tree_passes(tp_schema):
    assert check_tp_schema(tp_schema) == []


def test_tp_schema_missing_key_fails(tp_schema):
    mutated = json.loads(json.dumps(tp_schema))
    del mutated["properties"]["submission_package"]
    assert check_tp_schema(mutated)


def test_tp_schema_widened_enum_fails(tp_schema):
    mutated = json.loads(json.dumps(tp_schema))
    mutated["properties"]["submission_package"]["enum"].append(
        "strict_articles_only")
    errs = check_tp_schema(mutated)
    assert errs and "enum" in errs[0]


def test_tp_schema_json_default_fails(tp_schema):
    # The Invariant-3 lesson: a JSON-Schema `default` is non-operational
    # comfort — the absent-key default lives in the evaluator.
    mutated = json.loads(json.dumps(tp_schema))
    mutated["properties"]["submission_package"]["default"] = "advisory"
    errs = check_tp_schema(mutated)
    assert errs and "default" in errs[0]


# --- invariant 2: orchestrator gate section ---------------------------------

def test_orchestrator_real_tree_passes(orchestrator_text):
    assert check_orchestrator(orchestrator_text) == []


def test_orchestrator_missing_section_fails():
    assert check_orchestrator("# something else entirely\n")


@pytest.mark.parametrize("literal", [
    "bounded: 2 fix rounds",
    "VERIFICATION-INCOMPLETE",
    "--check-freshness",
    "SOLE reader of `terminal_policies.submission_package`",
    "Gate on stdout tokens, NEVER on exit codes",
    "Recompute each pass",
])
def test_orchestrator_lost_literal_fails(orchestrator_text, literal):
    mutated = orchestrator_text.replace(literal, "REDACTED")
    errs = check_orchestrator(mutated)
    assert errs, f"dropping {literal!r} must fire invariant 2"


# --- invariant 3: formatter advisories section ------------------------------

def test_formatter_real_tree_passes(formatter_text):
    assert check_formatter(formatter_text) == []


def test_formatter_missing_section_fails():
    assert check_formatter("# no advisories here\n")


@pytest.mark.parametrize("literal", [
    "mandatory and non-empty iff",
    "Invariant 13",
    "`not_applicable` rows",
])
def test_formatter_lost_literal_fails(formatter_text, literal):
    # Scope the mutation to the advisories section so a literal that also
    # appears elsewhere (Invariant 13 does) is removed where it matters.
    section_re = re.compile(
        r"^## Submission Package Advisories.*?(?=^## |\Z)",
        re.MULTILINE | re.DOTALL)
    mutated = section_re.sub(
        lambda m: m.group(0).replace(literal, "REDACTED"), formatter_text)
    errs = check_formatter(mutated)
    assert errs, f"dropping {literal!r} must fire invariant 3"


# --- invariant 4: AST single-homed guard ------------------------------------

def test_verifier_real_tree_is_single_homed():
    assert check_verifier_single_homed(
        VERIFIER.read_text(encoding="utf-8")) == []


def test_docstring_mention_does_not_fire():
    # The whole point of the AST guard (gate-1 P2): the verifier's module
    # docstring legitimately SAYS "terminal_policies"; only runtime access
    # may fire.
    source = '"""The script never reads terminal_policies (§5.3)."""\n'
    assert find_terminal_policies_access(source) == []


def test_comment_and_help_text_do_not_fire():
    source = (
        "# never touch terminal_policies here\n"
        'HELP = "the orchestrator reads terminal_policies, not this script"\n'
    )
    assert find_terminal_policies_access(source) == []


def test_subscript_access_fires():
    assert find_terminal_policies_access(
        'x = passport["terminal_policies"]\n')


def test_dotget_access_fires():
    assert find_terminal_policies_access(
        'x = passport.get("terminal_policies", {})\n')


def test_planted_access_in_real_source_fires():
    # Mutation pair for the real tree: planting a read into the actual
    # verifier source must fire.
    planted = (VERIFIER.read_text(encoding="utf-8")
               + '\n_tp = {}.get("terminal_policies")\n')
    assert check_verifier_single_homed(planted)


# --- invariant 5: report schema policy_slug ---------------------------------

def test_report_schema_real_tree_passes(report_schema):
    assert check_report_schema(report_schema) == []


def test_report_schema_widened_slug_enum_fails(report_schema):
    mutated = json.loads(json.dumps(report_schema))
    mutated["properties"]["header"]["properties"]["policy_slug"][
        "enum"].append("paranoid")
    errs = check_report_schema(mutated)
    assert errs and "enum" in errs[0]


def test_report_schema_dropped_null_semantics_fails(report_schema):
    mutated = json.loads(json.dumps(report_schema))
    mutated["properties"]["header"]["properties"]["policy_slug"][
        "description"] = "a slug"
    errs = check_report_schema(mutated)
    assert errs


def test_report_schema_string_none_is_not_null(report_schema):
    # Final-round review P3: the enum member must be JSON null, not the
    # STRING "None" — a str() mapping in the lint would let them collide.
    mutated = json.loads(json.dumps(report_schema))
    slug = mutated["properties"]["header"]["properties"]["policy_slug"]
    slug["enum"] = ["None", "advisory", "strict"]
    errs = check_report_schema(mutated)
    assert errs and "enum" in errs[0]
