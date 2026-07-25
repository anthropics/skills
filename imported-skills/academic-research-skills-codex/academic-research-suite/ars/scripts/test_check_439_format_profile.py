#!/usr/bin/env python3
"""Tests for check_439_format_profile.py (#439 Slice A).

Mutation discipline: every invariant has a passing case against the real schema
and a failing case proving the check fires when the guarded property is broken.
"""
from __future__ import annotations

import copy
import json

import pytest
from jsonschema import Draft202012Validator

from check_439_format_profile import (
    FORMATTER,
    INTAKE,
    POSITIONING,
    SCHEMA,
    check_cut_fields_stay_cut,
    check_example_fixture,
    check_fixed_pt_conditional,
    check_formatter_wiring,
    check_intake_wiring,
    check_no_provenance,
    check_positioning_boundary,
    check_schema_valid,
)


@pytest.fixture(scope="module")
def schema():
    return json.loads(SCHEMA.read_text(encoding="utf-8"))


# --- invariant 1: valid standalone schema, locked root ----------------------

def test_schema_real_tree_passes(schema):
    assert check_schema_valid(schema) == []


def test_schema_open_root_fails(schema):
    mutated = copy.deepcopy(schema)
    mutated["additionalProperties"] = True
    assert check_schema_valid(mutated), "open root (additionalProperties:true) must fire"


# --- invariant 2: fixed_pt conditional --------------------------------------

def test_fixed_pt_conditional_real_tree_passes(schema):
    assert check_fixed_pt_conditional(schema) == []


def test_fixed_pt_conditional_removed_fails(schema):
    """Drop the allOf conditional → fixed_pt no longer gated → check must fire."""
    mutated = copy.deepcopy(schema)
    mutated["properties"]["line_spacing"].pop("allOf", None)
    assert check_fixed_pt_conditional(mutated), "removing the fixed_pt conditional must fire"


def test_fixed_pt_conditional_mode_not_required_fails(schema):
    """Drop required:[mode] → {fixed_pt:20} with no mode becomes valid → check must fire (codex P2-1)."""
    mutated = copy.deepcopy(schema)
    mutated["properties"]["line_spacing"].pop("required", None)
    assert check_fixed_pt_conditional(mutated), "dropping required:[mode] must fire"


# --- invariant 3: no provenance machinery -----------------------------------

def test_no_provenance_real_tree_passes(schema):
    assert check_no_provenance(schema) == []


def test_provenance_leak_fails(schema):
    mutated = copy.deepcopy(schema)
    mutated["properties"]["declared_by"] = {"const": "scholar"}
    assert check_no_provenance(mutated), "a leaked declared_by must fire"


def test_inferred_marker_leak_fails(schema):
    mutated = copy.deepcopy(schema)
    mutated["properties"]["body_font_provenance"] = {"type": "string"}
    assert check_no_provenance(mutated), "a leaked *_provenance field must fire"


# --- invariant 4: cut fields stay cut ---------------------------------------

def test_cut_fields_real_tree_passes(schema):
    assert check_cut_fields_stay_cut(schema) == []


def test_profile_name_reappears_fails(schema):
    mutated = copy.deepcopy(schema)
    mutated["properties"]["profile_name"] = {"type": "string"}
    assert check_cut_fields_stay_cut(mutated), "reappearing profile_name must fire"


def test_caption_bold_reappears_fails(schema):
    mutated = copy.deepcopy(schema)
    mutated["properties"]["caption"]["properties"]["bold"] = {"type": "boolean"}
    assert check_cut_fields_stay_cut(mutated), "reappearing caption.bold must fire"


# --- invariant 5: synthetic example fixture validates -----------------------

def test_example_fixture_real_tree_passes(schema):
    assert check_example_fixture(schema) == []


def test_example_fixture_violation_fails(schema):
    """A schema that rejects the committed example must make the check fire."""
    mutated = copy.deepcopy(schema)
    # forbid table_border_style 'three_line' (the example declares it) → example invalid
    mutated["properties"]["table_border_style"]["enum"] = ["full_grid", "none"]
    assert check_example_fixture(mutated), "an example that violates the schema must fire"


# --- invariant 6: formatter wiring ------------------------------------------

@pytest.fixture(scope="module")
def formatter_text():
    return FORMATTER.read_text(encoding="utf-8")


@pytest.fixture(scope="module")
def intake_text():
    return INTAKE.read_text(encoding="utf-8")


def test_formatter_wiring_real_tree_passes(formatter_text):
    assert check_formatter_wiring(formatter_text) == []


def test_formatter_wiring_missing_section_fails():
    assert check_formatter_wiring("# no format profile section here"), \
        "a formatter without the Format Profile section must fire"


def test_formatter_wiring_dropped_guard_fails(formatter_text):
    """Remove the byte-equivalence guard literal → check must fire."""
    mutated = formatter_text.replace("skip this entire section", "skip it")
    assert check_formatter_wiring(mutated), "dropping the byte-equivalence guard must fire"


def test_formatter_wiring_dropped_venue_precedence_fails(formatter_text):
    mutated = formatter_text.replace("venue compliance wins", "format profile wins")
    assert check_formatter_wiring(mutated), "dropping venue precedence must fire"


def test_formatter_wiring_dropped_failclosed_fails(formatter_text):
    mutated = formatter_text.replace("fail closed BEFORE formatting", "handle path issues")
    assert check_formatter_wiring(mutated), "dropping the fail-closed rule must fire"


def test_formatter_wiring_dropped_no_inference_fails(formatter_text):
    mutated = formatter_text.replace("Never infer a missing layout field", "Guess layout")
    assert check_formatter_wiring(mutated), "dropping the no-inference rule must fire"


def test_formatter_wiring_dropped_best_effort_fails(formatter_text):
    mutated = formatter_text.replace("best-effort per output target", "always applied")
    assert check_formatter_wiring(mutated), "dropping the best-effort rule must fire"


# --- invariant 7: intake wiring ---------------------------------------------

def test_intake_wiring_real_tree_passes(intake_text):
    assert check_intake_wiring(intake_text) == []


def test_intake_wiring_missing_followup_fails():
    assert check_intake_wiring("# no followup"), "a missing #439 follow-up must fire"


def test_intake_wiring_dropped_byte_equiv_rule_fails(intake_text):
    mutated = intake_text.replace("no PCR `Format Profile` row at all", "an absent row")
    assert check_intake_wiring(mutated), "dropping the write-nothing rule must fire"


def test_intake_wiring_dropped_pcr_row_fails(intake_text):
    """Remove the structural PCR table row → check must fire (not just the prose mention)."""
    mutated = intake_text.replace("| **Format Profile** |", "| Format Profile |")
    assert check_intake_wiring(mutated), "losing the structural PCR Format Profile row must fire"


# --- invariant 8: POSITIONING boundary --------------------------------------

@pytest.fixture(scope="module")
def positioning_text():
    return POSITIONING.read_text(encoding="utf-8")


def test_positioning_boundary_real_tree_passes(positioning_text):
    assert check_positioning_boundary(positioning_text) == []


def test_positioning_boundary_missing_note_fails():
    assert check_positioning_boundary("# positioning without the boundary"), \
        "a POSITIONING without the #439 boundary note must fire"


def test_positioning_boundary_dropped_review_criterion_fails(positioning_text):
    mutated = positioning_text.replace("Review criterion:", "Note:")
    assert check_positioning_boundary(mutated), "dropping the Review criterion must fire"


# --- schema behavior: the contract a real profile must satisfy --------------
# These assert the SCHEMA itself (not the lint) accepts/rejects the right shapes,
# so the example profiles in the design doc stay valid and the cut/conditional
# rules hold at the data layer.

@pytest.fixture(scope="module")
def validator(schema):
    return Draft202012Validator(schema)


def _valid(validator, inst) -> bool:
    return not list(validator.iter_errors(inst))


@pytest.mark.parametrize(
    "inst",
    [
        {},
        {"body_font": {"family": "SimSun", "size_pt": 10.5}},
        {"line_spacing": {"mode": "fixed_pt", "fixed_pt": 20}},
        {"line_spacing": {"mode": "double"}},
        {"caption": {"placement": "below", "alignment": "center", "latin_font_family": "Times New Roman"}},
        {"margins_cm": {"top": 2.5, "bottom": 2.5, "left": 3.0, "right": 2.5}},
        {"table_border_style": "three_line"},
    ],
)
def test_schema_accepts_valid_profiles(validator, inst):
    assert _valid(validator, inst), f"should be VALID: {inst}"


@pytest.mark.parametrize(
    "inst",
    [
        {"line_spacing": {"mode": "double", "fixed_pt": 20}},   # fixed_pt with wrong mode
        {"line_spacing": {"mode": "fixed_pt"}},                  # fixed_pt mode missing value
        {"profile_name": "Guangxi undergrad"},                   # cut field
        {"caption": {"bold": True}},                             # cut field
        {"heading_font": {"family": "x"}},                       # cut field
        {"body_font": {"size_pt": 0}},                           # non-positive size
        {"table_border_style": "dashed"},                        # not in enum
        {"caption": {"placement": "middle"}},                    # not in enum
        {"unknown_top_level": 1},                                # locked root
    ],
)
def test_schema_rejects_invalid_profiles(validator, inst):
    assert not _valid(validator, inst), f"should be INVALID: {inst}"
