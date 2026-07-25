#!/usr/bin/env python3
"""Mutation tests for check_firm_rules_sync.py (v3.10 PR-A).

Confirms the lint is not a trivial accept-all: each mutation that breaks the
sync or reintroduces the ID collision MUST make the lint FAIL, and the clean
repo MUST PASS. Per `feedback_schema_mutation_test_for_constraints`.
"""
from __future__ import annotations

import re
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

from tests.test_helpers import run_script
from scripts.check_firm_rules_sync import CIM_SECTION_HEADER, _extract_section

REPO_ROOT = Path(__file__).resolve().parents[1]
LINT = REPO_ROOT / "scripts" / "check_firm_rules_sync.py"

SYNTHESIS = "deep-research/agents/synthesis_agent.md"
COMPILER = "deep-research/agents/report_compiler_agent.md"
WRITER = "academic-paper/agents/draft_writer_agent.md"
SCHEMA = "shared/contracts/passport/claim_intent_manifest.schema.json"
FORMATTER = "academic-paper/agents/formatter_agent.md"
FIRM_RULES = "shared/references/firm_rules.md"


def _run(root: Path) -> subprocess.CompletedProcess[str]:
    return run_script(LINT, "--root", str(root))


@pytest.fixture()
def tree(tmp_path: Path) -> Path:
    """A copy of just the files the lint reads, under a temp root."""
    rels = [
        SYNTHESIS, COMPILER, WRITER, SCHEMA, FORMATTER, FIRM_RULES,
        "deep-research/references/crossref_api_protocol.md",
        "deep-research/references/openalex_api_protocol.md",
        "academic-pipeline/agents/pipeline_orchestrator_agent.md",
        "deep-research/agents/bibliography_agent.md",
    ]
    for rel in rels:
        src = REPO_ROOT / rel
        dst = tmp_path / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy(src, dst)
    return tmp_path


def _mutate(root: Path, rel: str, old: str, new: str) -> None:
    path = root / rel
    text = path.read_text(encoding="utf-8")
    assert old in text, f"anchor not found in {rel}: {old!r}"
    path.write_text(text.replace(old, new, 1), encoding="utf-8")


# --- positive: clean tree passes ---

def test_clean_tree_passes(tree: Path) -> None:
    r = _run(tree)
    assert r.returncode == 0, r.stderr


# --- mutation: sync drift in a mirror ---

def test_mirror_wording_drift_fails(tree: Path) -> None:
    # Alter the canonical operative clause in the synthesis mirror.
    _mutate(
        tree, SYNTHESIS,
        "Emit exactly ONE manifest entry per agent invocation",
        "Emit exactly TWO manifest entries per agent invocation",
    )
    r = _run(tree)
    assert r.returncode == 1
    assert "R-CIM-A mirror drifted" in r.stderr


def test_mirror_wording_drift_in_writer_fails(tree: Path) -> None:
    _mutate(
        tree, WRITER,
        "BEFORE the first prose block",
        "AFTER the first prose block",
    )
    r = _run(tree)
    assert r.returncode == 1
    assert "drifted" in r.stderr


def test_semantic_edit_in_agent_slot_fails(tree: Path) -> None:
    # The <AGENT> wildcard must not be wide enough to swallow a semantic edit
    # smuggled into the self-reference slot. "agent or compiler" is 4 words /
    # contains "or" → must NOT match → flagged as drift.
    _mutate(
        tree, SYNTHESIS,
        "per agent invocation",
        "per agent or compiler invocation",
    )
    r = _run(tree)
    assert r.returncode == 1
    assert "drifted" in r.stderr


# --- mutation: collision regression (contamination ID back in claim-manifest) ---

def test_renaming_cim_back_to_contamination_id_fails(tree: Path) -> None:
    # Reverting the rule heading to the contamination ID breaks BOTH the sync
    # check (canonical clause's ID no longer matches) AND the collision guard.
    # Either failure is acceptable here; this test guards the rename, not the
    # collision guard in isolation (see test_stray_contamination_id_in_section).
    _mutate(tree, SYNTHESIS, "R-CIM-A (one-shot", "R-L3-2-A (one-shot")
    r = _run(tree)
    assert r.returncode == 1
    assert "collision regression" in r.stderr or "drifted" in r.stderr


def test_stray_contamination_id_in_section_fails(tree: Path) -> None:
    # Inject a stray contamination ID into the Claim Intent Manifest section
    # body WITHOUT touching any R-CIM canonical clause. This isolates the
    # collision guard: the sync check still passes, so only the collision guard
    # can catch this. Regression test for the (v3.8)-header bug that silently
    # disabled the guard.
    _mutate(
        tree, SYNTHESIS,
        "Three firm rules:\n\n- **R-CIM-A",
        "Three firm rules: (see R-L3-2-A)\n\n- **R-CIM-A",
    )
    r = _run(tree)
    assert r.returncode == 1
    assert "collision regression" in r.stderr
    assert "drifted" not in r.stderr  # the sync check must NOT be what fires


def test_stray_contamination_id_behind_fenced_fake_heading_fails(tree: Path) -> None:
    # A forbidden contamination ID hidden inside the section after a FENCED fake
    # `## heading` must still be caught. A naive section extractor that stops at
    # any `## ` line would terminate the section early at the fake heading and
    # miss the ID. Regression guard for the fence-aware _extract_section: the
    # fake `## Legacy` is inside a ``` block, so it does NOT end the section.
    # Anchor on the section-internal R-CIM-A bullet (unique to the Claim Intent
    # Manifest section — "Three firm rules:" also appears earlier in the prompt,
    # outside the section, so anchoring there would inject out-of-section).
    _mutate(
        tree, SYNTHESIS,
        "- **R-CIM-A (one-shot pre-commitment):**",
        "```md\n## Legacy copied wording\n- R-L3-2-A here\n```\n- **R-CIM-A (one-shot pre-commitment):**",
    )
    r = _run(tree)
    assert r.returncode == 1
    assert "collision regression" in r.stderr
    assert "drifted" not in r.stderr  # the sync check must NOT be what fires


def test_full_contamination_namespace_guarded_in_section(tree: Path) -> None:
    # The guard seals the whole R-L3-2-A..E namespace, not just the A/B/C that
    # historically collided. A D/E ID appearing in the claim-manifest section is
    # still a leak (claim-manifest surfaces carry no contamination IDs at all).
    _mutate(
        tree, SYNTHESIS,
        "- **R-CIM-A (one-shot pre-commitment):**",
        "(stray R-L3-2-D)\n- **R-CIM-A (one-shot pre-commitment):**",
    )
    r = _run(tree)
    assert r.returncode == 1
    assert "R-L3-2-D" in r.stderr
    assert "collision regression" in r.stderr


def test_contamination_id_in_schema_fails(tree: Path) -> None:
    _mutate(tree, SCHEMA, "per R-CIM-A", "per R-L3-2-A")
    r = _run(tree)
    assert r.returncode == 1
    assert "R-L3-2-A" in r.stderr


# --- mutation: collision regression (R-CIM leaked into contamination context) ---

def test_cim_id_in_formatter_fails(tree: Path) -> None:
    # Inject an R-CIM token into the contamination pass-through paragraph.
    _mutate(
        tree, FORMATTER,
        "v3.7.3 R-L3-2-A",
        "v3.7.3 R-L3-2-A (see also R-CIM-A)",
    )
    r = _run(tree)
    assert r.returncode == 1
    assert "R-CIM-A leaked" in r.stderr


# --- v3.10 PR-B: contradiction guard (R-L3-2-A reword) ---

def test_contradiction_phrase_in_r_l3_2_a_sentence_fails(tree: Path) -> None:
    """Injecting an unqualified non-blocking claim into the R-L3-2-A reference
    sentence must fail — a strict policy can now block."""
    _mutate(
        tree, "deep-research/references/crossref_api_protocol.md",
        "handled per R-L3-2-A (advisory by default",
        "advisory only, handled per R-L3-2-A (",
    )
    r = _run(tree)
    assert r.returncode == 1
    assert "contradiction phrase" in r.stderr
    assert "advisory only" in r.stderr


def test_contradiction_guard_does_not_flag_collaboration_observer(tree: Path) -> None:
    """False-positive guard: the Collaboration Depth Observer's legitimate
    'never blocks' wording (a different subsystem, NOT in an R-L3-2-A sentence)
    must NOT trip the contradiction guard. The orchestrator file carries both
    'Collaboration Depth Observer (advisory, never blocks)' and contamination
    R-L3-2-* references; only the latter are scanned."""
    # The clean tree already contains the collaboration-observer 'never blocks'
    # prose in the orchestrator. A clean run must pass — proving the guard scopes
    # to R-L3-2-A sentences only, not the whole file.
    r = _run(tree)
    assert r.returncode == 0, (
        "contradiction guard false-flagged the collaboration-observer prose: "
        + r.stderr
    )


def test_contradiction_phrase_after_semicolon_still_caught(tree: Path) -> None:
    """codex P2: a contradiction phrase joined to the R-L3-2-A reference by a
    semicolon must still be caught — the guard must NOT split on ';' (which would
    put the phrase in a different chunk and miss it)."""
    _mutate(
        tree, "deep-research/references/crossref_api_protocol.md",
        "handled per R-L3-2-A (advisory by default",
        "handled per R-L3-2-A; contamination signals never block emission (",
    )
    r = _run(tree)
    assert r.returncode == 1
    assert "contradiction phrase" in r.stderr


def test_contradiction_phrase_outside_r_l3_2_a_sentence_passes(tree: Path) -> None:
    """Adding a 'never blocks' clause in a sentence that does NOT name R-L3-2-A
    must pass — the guard scopes to the R-L3-2-A reference, not the file."""
    _mutate(
        tree, "deep-research/references/crossref_api_protocol.md",
        "Mirrors the structure of",
        "This lookup never blocks anything by itself. Mirrors the structure of",
    )
    r = _run(tree)
    assert r.returncode == 0, r.stderr


# --- mutation: canonical block removed → invocation error ---

def test_missing_canonical_block_fails(tree: Path) -> None:
    path = tree / FIRM_RULES
    text = path.read_text(encoding="utf-8")
    # Drop the R-CIM-A canonical block entirely.
    text2 = re.sub(
        r"<!-- canonical:R-CIM-A -->.*?<!-- /canonical:R-CIM-A -->",
        "",
        text,
        flags=re.DOTALL,
    )
    assert text2 != text
    path.write_text(text2, encoding="utf-8")
    r = _run(tree)
    assert r.returncode == 1
    assert "R-CIM-A" in r.stderr


# --- mutation: missing CIM section header / missing guard file → violation ---

def test_missing_cim_section_header_fails(tree: Path) -> None:
    # Rename the section header so it no longer matches. The collision guard
    # must REFUSE (flag the missing section), not pass vacuously.
    _mutate(
        tree, SYNTHESIS,
        "## Claim Intent Manifest Emission",
        "## Manifest Emission Renamed",
    )
    r = _run(tree)
    assert r.returncode == 1
    assert "section header not found" in r.stderr


def test_missing_guard_file_fails(tree: Path) -> None:
    # Delete a contamination-context file. The guard must flag the absence,
    # not silently skip it.
    (tree / FORMATTER).unlink()
    r = _run(tree)
    assert r.returncode == 1
    assert "missing collision-guard file" in r.stderr


# --- unit: _extract_section header/boundary handling ---

def test_extract_section_tolerates_version_suffix() -> None:
    text = "## Claim Intent Manifest Emission (v3.8)\nbody line\n## Next\nafter"
    assert _extract_section(text, CIM_SECTION_HEADER) == "body line\n"


def test_extract_section_at_eof_no_trailing_newline() -> None:
    text = "## Claim Intent Manifest Emission (v3.8)\nlast body line"
    assert _extract_section(text, CIM_SECTION_HEADER) == "last body line"


def test_extract_section_does_not_stop_at_level3_heading() -> None:
    text = "## Claim Intent Manifest Emission\nintro\n### sub\nmore\n## Next\nx"
    body = _extract_section(text, CIM_SECTION_HEADER)
    assert "### sub" in body and "more" in body and "x" not in body


def test_extract_section_stops_at_next_level2() -> None:
    text = "## Claim Intent Manifest Emission\nbody\n## Other Section\nleak R-L3-2-A"
    assert "R-L3-2-A" not in _extract_section(text, CIM_SECTION_HEADER)


def test_extract_section_does_not_stop_at_fenced_heading() -> None:
    # A `## ` line inside a fenced code block is example text, not a real
    # section boundary; the section must continue past it so the collision guard
    # still scans content after the fence.
    text = (
        "## Claim Intent Manifest Emission\n"
        "intro\n"
        "```md\n"
        "## Fake heading\n"
        "hidden R-L3-2-A\n"
        "```\n"
        "tail\n"
        "## Real Next Section\n"
        "after"
    )
    body = _extract_section(text, CIM_SECTION_HEADER)
    assert "R-L3-2-A" in body and "tail" in body
    assert "after" not in body  # real H2 after the closed fence still stops it


def test_extract_section_returns_none_when_header_absent() -> None:
    assert _extract_section("no header here\njust text", CIM_SECTION_HEADER) is None


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
