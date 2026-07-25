"""Render-side regression test for v3.7.1 Step 2 — Section 0 Scope Report.

Codex round-1 review of PR #78 surfaced a P1 architectural finding: the static
Section 0 block was prepended to `shared/templates/codex_audit_multifile_template.md`
and lint-enforced, but `scripts/audit_snapshot.py::render_prompt` extracted only
sections [3, 6, 7] from the template. Section 0 was therefore absent from every
wrapper-dispatched audit prompt, defeating the spec §3.2 contract that the
Scope Report rides verbatim every round.

This test pins the render-side contract: render_prompt MUST emit a Section 0
Scope Report block ahead of the Section 1 Round metadata block so the audit
target sees the scope-disclosure framing before any pass/fail summary.
"""
from __future__ import annotations

from pathlib import Path

import pytest

from scripts.audit_snapshot import render_prompt

REPO_ROOT = Path(__file__).resolve().parent.parent
TEMPLATE_PATH = (
    REPO_ROOT / "shared" / "templates" / "codex_audit_multifile_template.md"
)


def _render_minimal_prompt() -> bytes:
    """Run render_prompt with minimal valid arguments."""
    return render_prompt(
        audit_template=TEMPLATE_PATH.read_bytes(),
        primary_paths=["primary/file.md"],
        primary_contents=[b"primary content"],
        supporting_paths=[],
        supporting_contents=[],
        round_n=1,
        target_rounds=3,
        git_sha="0123456789ab",
        stage=2,
        agent="synthesis_agent",
        prior_findings=None,
    )


def test_render_prompt_emits_section_0_scope_report_header() -> None:
    """The rendered prompt MUST contain the Section 0 H2 anchor."""
    rendered = _render_minimal_prompt()
    assert b"## Section 0 \xe2\x80\x94 Scope Report" in rendered, (
        "render_prompt does not emit Section 0 Scope Report header — "
        "spec §3.2 contract violated (codex round-1 PR #78 P1)."
    )


def test_render_prompt_emits_scope_report_codex_round_header() -> None:
    """The rendered prompt MUST contain the canonical Scope Report header."""
    rendered = _render_minimal_prompt()
    assert b"## Codex Audit Round N \xe2\x80\x94 Scope Report" in rendered, (
        "render_prompt does not emit the canonical Scope Report header "
        "literal (spec line 134)."
    )


def test_render_prompt_section_0_appears_before_section_1() -> None:
    """Spec line 146 firm rule: Scope Report must appear BEFORE any pass/fail summary."""
    rendered = _render_minimal_prompt()
    section_0_pos = rendered.find(b"## Section 0 \xe2\x80\x94 Scope Report")
    section_1_pos = rendered.find(b"## Section 1 \xe2\x80\x94 Round metadata")
    assert section_0_pos != -1 and section_1_pos != -1, (
        "fixture assumption violated: both Section 0 and Section 1 must be present"
    )
    assert section_0_pos < section_1_pos, (
        f"Scope Report (offset {section_0_pos}) does not appear before Section 1 "
        f"(offset {section_1_pos}); spec line 146 firm rule violated."
    )


def test_render_prompt_emits_required_scope_report_fields() -> None:
    """The four required Scope Report content fields must appear (spec lines 136-140)."""
    rendered = _render_minimal_prompt()
    text = rendered.decode("utf-8")
    required_fields = [
        "**Total entries audited:**",
        "**Entries with retrieved original source:**",
        "**Entries description-only (no retrieved source):**",
        "**Audit scope warning:**",
    ]
    missing = [f for f in required_fields if f not in text]
    assert not missing, (
        f"render_prompt output missing required Scope Report fields: {missing}"
    )


def test_render_prompt_emits_aggregate_status_splits() -> None:
    """The three aggregate-status splits must appear (spec lines 147-150)."""
    rendered = _render_minimal_prompt()
    text = rendered.decode("utf-8")
    required_splits = [
        "verified-against-source",
        "description-internally-consistent",
        "unaudited-due-to-missing-source",
    ]
    missing = [s for s in required_splits if s not in text]
    assert not missing, (
        f"render_prompt output missing aggregate-status splits: {missing}"
    )
