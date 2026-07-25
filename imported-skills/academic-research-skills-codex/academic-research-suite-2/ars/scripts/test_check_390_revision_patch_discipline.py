#!/usr/bin/env python3
"""Tests for check_390_revision_patch_discipline.py (#390 Slice B, #424).

Mutation discipline: every invariant has a passing case against the real
tree artifacts and a failing case proving the check fires when the guarded
property is broken. Mutations reproduce the guarded literal EXACTLY
(case-sensitive) — a probe that mutates a re-cased copy of the anchor
exercises nothing (the #383 lesson).
"""
from __future__ import annotations

import json
import re

import pytest

from check_390_revision_patch_discipline import (
    FORMATTER,
    APPLY_SCRIPT,
    ORCHESTRATOR,
    PAPER_SKILL,
    PATCH_SCHEMA,
    PROTOCOL,
    SCHEMAS,
    SPEC,
    WORD_COUNT,
    WRITER,
    check_marker_rules,
    check_orchestrator,
    check_paper_skill,
    check_protocol_doc,
    check_schema8,
    check_spec_example,
    check_threshold_lock,
    check_writer,
    spec_example_patch,
)


@pytest.fixture(scope="module")
def writer_text():
    return WRITER.read_text(encoding="utf-8")


@pytest.fixture(scope="module")
def orchestrator_text():
    return ORCHESTRATOR.read_text(encoding="utf-8")


@pytest.fixture(scope="module")
def skill_text():
    return PAPER_SKILL.read_text(encoding="utf-8")


@pytest.fixture(scope="module")
def schemas_text():
    return SCHEMAS.read_text(encoding="utf-8")


@pytest.fixture(scope="module")
def protocol_text():
    return PROTOCOL.read_text(encoding="utf-8")


@pytest.fixture(scope="module")
def formatter_text():
    return FORMATTER.read_text(encoding="utf-8")


@pytest.fixture(scope="module")
def word_count_text():
    return WORD_COUNT.read_text(encoding="utf-8")


@pytest.fixture(scope="module")
def spec_text():
    return SPEC.read_text(encoding="utf-8")


@pytest.fixture(scope="module")
def patch_schema():
    return json.loads(PATCH_SCHEMA.read_text(encoding="utf-8"))


@pytest.fixture(scope="module")
def apply_src():
    return APPLY_SCRIPT.read_text(encoding="utf-8")


def _mutate(text: str, literal: str) -> str:
    """Remove the exact (case-sensitive) literal; assert it was present so
    a drifted probe fails loudly instead of exercising nothing."""
    assert literal in text, f"probe literal drifted: {literal!r}"
    return text.replace(literal, "REDACTED-BY-MUTATION-TEST")


# --- invariant 1: writer discipline block -----------------------------------

def test_writer_real_tree_passes(writer_text):
    assert check_writer(writer_text) == []

def test_writer_missing_section_fails(writer_text):
    errs = check_writer(_mutate(
        writer_text, "## Patch-Document Revision Emission (#390)"))
    assert errs and "missing" in errs[0]

def test_writer_lost_hash_discipline_fails(writer_text):
    errs = check_writer(_mutate(
        writer_text, "Copy hashes, never compute them."))
    assert errs and "hash copy discipline" in errs[0]

def test_writer_lost_escalation_tag_fails(writer_text):
    errs = check_writer(_mutate(
        writer_text, "[PATCH-ESCALATION-REQUIRED: layer=pre_drafting"))
    assert errs and "escalation tag" in errs[0]

def test_writer_lost_sidecar_path_fails(writer_text):
    errs = check_writer(_mutate(
        writer_text, "phase6_*/revision_patch_round<N>.json"))
    assert errs and "sidecar emission path" in errs[0]


# --- invariant 2: orchestrator sequencing -----------------------------------

def test_orchestrator_real_tree_passes(orchestrator_text):
    assert check_orchestrator(orchestrator_text) == []

def test_orchestrator_lost_no_rewrite_window_fails(orchestrator_text):
    errs = check_orchestrator(_mutate(
        orchestrator_text,
        "nothing may rewrite the draft between steps 1 and 3"))
    assert errs and "no-rewrite window" in errs[0]

def test_orchestrator_lost_auto_fallback_ban_fails(orchestrator_text):
    errs = check_orchestrator(_mutate(
        orchestrator_text, "NEVER auto-fallback to full re-emission"))
    assert errs and "no auto-fallback" in errs[0]

def test_orchestrator_lost_step_fails(orchestrator_text):
    errs = check_orchestrator(_mutate(
        orchestrator_text, "**Finalizer pass:**"))
    assert errs and any("lost step" in e for e in errs)

def test_orchestrator_steps_out_of_order_fails(orchestrator_text):
    # Swap the anchorize and apply step labels: same literals, wrong order.
    swapped = orchestrator_text.replace(
        "**Anchorize (manifest refresh):**", "@@TMP@@").replace(
        "**Apply:**", "**Anchorize (manifest refresh):**").replace(
        "@@TMP@@", "**Apply:**")
    errs = check_orchestrator(swapped)
    assert errs and any("normative order" in e for e in errs)

def test_orchestrator_lost_escalated_provenance_fails(orchestrator_text):
    errs = check_orchestrator(_mutate(
        orchestrator_text, "mode: full_reemission_escalated"))
    assert errs and any("escalated provenance" in e for e in errs)


# --- invariant 3: SKILL.md ---------------------------------------------------

def test_skill_real_tree_passes(skill_text):
    assert check_paper_skill(skill_text) == []

def test_skill_lost_honest_boundary_fails(skill_text):
    errs = check_paper_skill(_mutate(
        skill_text, "does not make the revision itself better"))
    assert errs and "honest boundary" in errs[0]

def test_skill_mode_row_regressed_to_full_draft_fails(skill_text):
    row = next(line for line in skill_text.splitlines()
               if line.lstrip().startswith("| `revision` |"))
    regressed = skill_text.replace(
        row, "| `revision` | \"Revise paper\" | 8->5->6 | "
        "Revised draft with tracked changes |")
    errs = check_paper_skill(regressed)
    assert errs and any("patch document deliverable" in e for e in errs)


# --- invariant 4: Schema 8 ---------------------------------------------------

def test_schema8_real_tree_passes(schemas_text):
    assert check_schema8(schemas_text) == []

def test_schema8_lost_field_fails(schemas_text):
    errs = check_schema8(_mutate(schemas_text, "`change_block_ids`"))
    assert errs and "field row" in errs[0]

def test_schema8_lost_producer_split_fails(schemas_text):
    errs = check_schema8(_mutate(schemas_text, "never by the writer"))
    assert errs and "producer split" in errs[0]


# --- invariant 5: protocol doc -----------------------------------------------

def test_protocol_real_tree_passes(protocol_text):
    assert check_protocol_doc(protocol_text) == []

def test_protocol_missing_file_fails():
    errs = check_protocol_doc(None)
    assert errs and "missing" in errs[0]

def test_protocol_lost_apply_command_fails(protocol_text):
    errs = check_protocol_doc(_mutate(
        protocol_text, "python scripts/ars_apply_revision_patch.py"))
    assert errs and "apply command" in errs[0]

def test_protocol_lost_marker_lifecycle_fails(protocol_text):
    errs = check_protocol_doc(_mutate(protocol_text, "## Marker lifecycle"))
    assert errs and "marker lifecycle" in errs[0]


# --- invariant 6: marker rules -----------------------------------------------

def test_marker_rules_real_tree_pass(formatter_text, word_count_text):
    assert check_marker_rules(formatter_text, word_count_text) == []

def test_formatter_lost_ordering_fails(formatter_text, word_count_text):
    errs = check_marker_rules(
        _mutate(formatter_text, "ONLY AFTER every marker-dependent gate"),
        word_count_text)
    assert errs and "ordering" in errs[0]

def test_word_count_lost_strip_rule_fails(formatter_text, word_count_text):
    errs = check_marker_rules(
        formatter_text,
        _mutate(word_count_text,
                "Strip every `<!--...-->` comment before computing"))
    assert errs and any("strip-before-count" in e for e in errs)


# --- invariant 7: threshold lock ----------------------------------------------

def test_threshold_lock_real_tree_passes(spec_text, apply_src):
    assert check_threshold_lock(spec_text, apply_src) == []

def test_threshold_lock_amendment_lost_decision_fails(spec_text, apply_src):
    errs = check_threshold_lock(
        _mutate(spec_text, "heading-anchor exemption"), apply_src)
    assert errs and any("exemption decision" in e for e in errs)

def test_threshold_constant_is_the_ship_decision():
    from ars_apply_revision_patch import DEFAULT_TOUCHED_RATIO_THRESHOLD
    assert DEFAULT_TOUCHED_RATIO_THRESHOLD == 0.6

def test_cli_default_regressed_to_none_fails(spec_text, apply_src):
    # codex P3: the lint must catch a CLI default regression even while
    # the constant still equals 0.6. Mutate the argparse default to None.
    regressed = apply_src.replace(
        "default=DEFAULT_TOUCHED_RATIO_THRESHOLD,", "default=None,")
    assert regressed != apply_src, "probe literal drifted"
    errs = check_threshold_lock(spec_text, regressed)
    assert errs and any("argparse default" in e for e in errs)


# --- invariant 8: spec example validates --------------------------------------

def test_spec_example_real_tree_passes(spec_text, patch_schema):
    assert check_spec_example(spec_text, patch_schema) == []

def test_spec_example_extracted(spec_text):
    example = spec_example_patch(spec_text)
    assert example is not None
    assert example["patch_format_version"] == "1.0"

def test_spec_example_invalidated_fails(spec_text, patch_schema):
    # Give the example an op shape the schema forbids (hash-less replace),
    # splicing a fresh §3.2 block so the probe is independent of the
    # embedded JSON's exact formatting.
    mutated_example = json.loads(json.dumps(spec_example_patch(spec_text)))
    del mutated_example["ops"][0]["old_hash"]
    head, tail = spec_text.split("### 3.2 Patch document", 1)
    after_block = tail.split("```", 2)[2]
    mutated_spec = (head + "### 3.2 Patch document\n\n```json\n"
                    + json.dumps(mutated_example, indent=2)
                    + "\n```" + after_block)
    errs = check_spec_example(mutated_spec, patch_schema)
    assert errs and "no longer validates" in errs[0]
