"""Mutation tests for ARS v3.7.1 Step 2 — D2 audit Scope Report lint.

Spec: docs/design/2026-04-30-ars-v3.6.8-trust-provenance-and-drift-transparency-spec.md
      §3.2 (D2 — Audit scope coverage non-disclosure)
      §4 Step 2 — Audit report Scope Report block

Tests verify that the lint:

  1. PASSES on the audit template AS SHIPPED (baseline carries the
     Section 0 Scope Report block prepended in Step 2).
  2. PASSES that the Scope Report header appears strictly BEFORE the
     Section 1 heading (the firm rule from spec line 146).
  3. FAILS when the Section 0 H2 anchor is removed.
  4. FAILS when the combined-aggregate "PASSED" verb appears in the audit
     summary scope (spec line 152).
  5. FAILS when the aggregate status is missing one of the three required
     splits per spec lines 147-150.
  6. FAILS when a pass/fail summary is positioned BEFORE Section 0
     (spec line 146 firm rule).
  7. FAILS when the Section 1 heading bytes mutate (regression sentinel
     for the additive-prepend invariant per Q5 amend).
  8. FAILS when any of the four required Scope Report content fields is
     removed.

Baseline assumption: Step 2 commit prepends the Scope Report block to
`shared/templates/codex_audit_multifile_template.md`. Each mutation test
snapshots the template, mutates a single attribute of that baseline,
runs the lint as a subprocess, and restores the file in `finally`
(mirrors test_check_v3_6_8_pattern_protection.py snapshot pattern).
"""
from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
LINT = REPO_ROOT / "scripts" / "check_v3_6_8_audit_scope_block.py"
TEMPLATE = REPO_ROOT / "shared" / "templates" / "codex_audit_multifile_template.md"

# Anchors that MUST appear in the baseline (Step 2 ships these). If any
# is absent, the baseline contract has drifted and tests are vacuous.
SECTION_0_H2_ANCHOR = "## Section 0 — Scope Report"
SCOPE_REPORT_HEADER = "## Codex Audit Round N — Scope Report"
SECTION_1_HEADING = "## Section 1 — Round metadata"
UNAUDITED_SPLIT_LINE = "  - `unaudited-due-to-missing-source: <count>` (always reported, never hidden)\n"

REQUIRED_FIELDS = [
    "**Total entries audited:**",
    "**Entries with retrieved original source:**",
    "**Entries description-only (no retrieved source):**",
    "**Audit scope warning:**",
    "**Affected refcodes (description-only):**",
]


def _run_lint() -> subprocess.CompletedProcess[str]:
    """Run the v3.7.1 audit-scope lint as a subprocess (so sys.exit propagates)."""
    return subprocess.run(
        [sys.executable, str(LINT)],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )


# ---------- Helpers for snapshot + restore ----------


class _Snapshot:
    """Backs up a file's bytes; restores on context exit."""

    def __init__(self, path: Path):
        self.path = path
        self._bytes: bytes | None = None
        self._existed: bool = False

    def __enter__(self) -> "_Snapshot":
        self._existed = self.path.exists()
        if self._existed:
            self._bytes = self.path.read_bytes()
        return self

    def __exit__(self, exc_type, exc, tb) -> None:
        if self._existed and self._bytes is not None:
            self.path.write_bytes(self._bytes)
        elif not self._existed and self.path.exists():
            self.path.unlink()


def _baseline_text() -> str:
    """Return template text and assert baseline anchors are present."""
    text = TEMPLATE.read_text(encoding="utf-8")
    for anchor in (SECTION_0_H2_ANCHOR, SCOPE_REPORT_HEADER, SECTION_1_HEADING):
        assert anchor in text, (
            f"baseline contract drift: {anchor!r} missing from template; "
            "Step 2 prepend may have been reverted."
        )
    return text


# ---------- Tests ----------


def test_t1_baseline_template_passes() -> None:
    """T1: template AS SHIPPED carries a valid Scope Report block → PASS."""
    _baseline_text()  # asserts baseline anchors present
    result = _run_lint()
    assert result.returncode == 0, (
        f"Expected exit 0 on baseline template; got {result.returncode}.\n"
        f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
    )
    assert "PASS" in result.stdout


def test_t2_scope_report_header_strictly_before_section_1() -> None:
    """T2: baseline Scope Report header anchored before Section 1 → PASS + ordering verified."""
    text = _baseline_text()
    result = _run_lint()
    assert result.returncode == 0
    # Sanity check: the lint actually verified ordering, not just header presence.
    assert text.find(SECTION_0_H2_ANCHOR) < text.find(SECTION_1_HEADING)
    assert text.find(SCOPE_REPORT_HEADER) < text.find(SECTION_1_HEADING)


def test_t3_missing_section_0_anchor_fails() -> None:
    """T3: Section 0 H2 anchor removed → FAIL."""
    with _Snapshot(TEMPLATE):
        text = _baseline_text()
        # Mutate the Section 0 H2 heading so the lint cannot anchor it.
        # We change the heading bytes so it no longer matches '^## Section 0'.
        mutated = text.replace(SECTION_0_H2_ANCHOR, "## Sectionless 0 — Scope Report", 1)
        TEMPLATE.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            "Expected lint to reject template after Section 0 anchor mutation.\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )
        assert "Section 0" in result.stdout
        assert "missing" in result.stdout.lower() or "absent" in result.stdout.lower()


def test_t4_combined_aggregate_passed_verb_in_summary_fails() -> None:
    """T4: inject a combined-aggregate 'PASSED' verb in summary context → FAIL (spec line 152)."""
    with _Snapshot(TEMPLATE):
        text = _baseline_text()
        # Inject a forbidden combined-aggregate verdict line just before Section 1.
        injection = "\n## Audit Summary\n\nverdict: PASSED\n\n---\n"
        mutated = text.replace(
            SECTION_1_HEADING,
            injection + SECTION_1_HEADING,
            1,
        )
        TEMPLATE.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            "Expected lint to reject combined-aggregate 'PASSED' verb per spec line 152.\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )
        # The combined-aggregate verb is what's forbidden; the rule code
        # should surface either R4 or the verb itself.
        out = result.stdout
        assert "PASSED" in out or "combined-aggregate" in out.lower()


def test_t5_missing_unaudited_split_fails() -> None:
    """T5: drop the 'unaudited-due-to-missing-source' split row → FAIL (spec line 150)."""
    with _Snapshot(TEMPLATE):
        text = _baseline_text()
        assert UNAUDITED_SPLIT_LINE in text, (
            "fixture assumption violated: unaudited split line not present in baseline"
        )
        mutated = text.replace(UNAUDITED_SPLIT_LINE, "", 1)
        TEMPLATE.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            "Expected lint to reject Scope Report missing the "
            "'unaudited-due-to-missing-source' split per spec line 150.\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )
        assert "unaudited-due-to-missing-source" in result.stdout


def test_t6_pass_fail_summary_before_section_0_fails() -> None:
    """T6: inject a pass/fail summary BEFORE Section 0 → FAIL (spec line 146)."""
    with _Snapshot(TEMPLATE):
        text = _baseline_text()
        # Inject a fake pass/fail summary heading + verdict row BEFORE Section 0.
        injection = (
            "\n## Audit Summary\n\nverified-against-source: PASS\n\n---\n\n"
        )
        mutated = text.replace(
            SECTION_0_H2_ANCHOR,
            injection + SECTION_0_H2_ANCHOR,
            1,
        )
        TEMPLATE.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            "Expected lint to reject pass/fail summary placed before Section 0 "
            "(spec line 146 firm rule).\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )


def test_t7_section_1_heading_byte_mutation_fails() -> None:
    """T7: Section 1 heading bytes change → FAIL (additive-prepend invariant per Q5)."""
    with _Snapshot(TEMPLATE):
        text = _baseline_text()
        # Mutate the Section 1 heading's title (capitalization swap).
        mutated = text.replace(
            SECTION_1_HEADING,
            "## Section 1 — Round Metadata",  # capitalization changed
            1,
        )
        TEMPLATE.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            "Expected lint to enforce Section 1 byte-equivalence per Q5 amend "
            "(spec §3.2 line 131: Sections 1-7 stay byte-equivalent in title, "
            "ordinal label, and order).\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )


@pytest.mark.parametrize("missing_field", REQUIRED_FIELDS)
def test_t8_missing_required_content_field_fails(missing_field: str) -> None:
    """T8: drop one of the four required Scope Report fields → FAIL (spec lines 136-140)."""
    with _Snapshot(TEMPLATE):
        text = _baseline_text()
        assert missing_field in text, (
            f"fixture assumption violated: field {missing_field!r} not present in baseline"
        )
        # Drop the entire line that contains the field marker.
        lines = text.splitlines(keepends=True)
        # Drop only the FIRST line that contains the marker, to avoid
        # accidentally removing a Template-structure summary line that
        # also references the field name.
        new_lines: list[str] = []
        dropped = False
        for line in lines:
            if not dropped and missing_field in line:
                dropped = True
                continue
            new_lines.append(line)
        assert dropped, "fixture assumption violated: no line dropped"
        TEMPLATE.write_text("".join(new_lines), encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            f"Expected lint to reject Scope Report missing field {missing_field!r}.\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )


# ---- Round-2 codex review findings ----


@pytest.mark.parametrize("missing_field", REQUIRED_FIELDS)
def test_t9_required_field_check_scoped_to_section_0(missing_field: str) -> None:
    """T9 (codex round-2 P2-1): required-field scan must be scoped to Section 0,
    not whole-file. If the field is dropped from Section 0 but the same marker
    appears in a later appendix or documentation block, the lint must still FAIL.
    """
    with _Snapshot(TEMPLATE):
        text = _baseline_text()
        # Find the Section 0 block boundaries: from "## Section 0" anchor
        # to the next "## Section 1" anchor.
        section_0_pos = text.find("## Section 0 — Scope Report")
        section_1_pos = text.find("## Section 1 — Round metadata")
        assert section_0_pos != -1 and section_1_pos != -1
        section_0_block = text[section_0_pos:section_1_pos]
        assert missing_field in section_0_block, (
            f"fixture assumption violated: field {missing_field!r} missing from Section 0 baseline"
        )
        # Remove the field from Section 0 only, then inject a decoy line
        # carrying the same marker AFTER Section 7 so a whole-file scan
        # would falsely PASS.
        section_0_mutated = section_0_block.replace(missing_field, "REDACTED-FIELD-MARKER", 1)
        appendix_decoy = (
            f"\n\n## Appendix — documentation reference\n\n"
            f"For historical context, the Scope Report contract requires "
            f"{missing_field} to appear in every audit round.\n"
        )
        mutated = (
            text[:section_0_pos]
            + section_0_mutated
            + text[section_1_pos:]
            + appendix_decoy
        )
        TEMPLATE.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            f"Expected lint to reject when {missing_field!r} is missing from Section 0 "
            f"(even though the marker appears in an appendix after Section 7).\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )


@pytest.mark.parametrize("missing_split", [
    "verified-against-source",
    "description-internally-consistent",
    "unaudited-due-to-missing-source",
])
def test_t10_required_split_check_scoped_to_section_0(missing_split: str) -> None:
    """T10 (codex round-2 P2-1, applies to R3 too): aggregate-status split
    scan must be scoped to Section 0. Decoy in appendix must not falsely PASS.
    """
    with _Snapshot(TEMPLATE):
        text = _baseline_text()
        section_0_pos = text.find("## Section 0 — Scope Report")
        section_1_pos = text.find("## Section 1 — Round metadata")
        section_0_block = text[section_0_pos:section_1_pos]
        assert missing_split in section_0_block
        section_0_mutated = section_0_block.replace(missing_split, "REDACTED-SPLIT-NAME", 1)
        appendix_decoy = (
            f"\n\n## Appendix — split nomenclature\n\n"
            f"Note: the {missing_split} verdict is computed by the orchestrator.\n"
        )
        mutated = (
            text[:section_0_pos]
            + section_0_mutated
            + text[section_1_pos:]
            + appendix_decoy
        )
        TEMPLATE.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            f"Expected lint to reject when {missing_split!r} is missing from Section 0 "
            f"(even though the marker appears in an appendix).\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )


def test_t11_target_relative_path_does_not_crash() -> None:
    """T11 (codex round-2 P2-2): --target with a relative repo path must
    not crash with ValueError. Lint should resolve the path and proceed.
    """
    result = subprocess.run(
        [
            sys.executable,
            str(LINT),
            "--target",
            "shared/templates/codex_audit_multifile_template.md",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    # The lint must produce a deterministic exit code (0 or 1 — both indicate
    # the lint ran), NOT crash with ValueError or ImportError.
    assert result.returncode in (0, 1), (
        f"Expected exit 0 or 1 on relative --target; got {result.returncode}.\n"
        f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
    )
    # Crash signature: ValueError traceback in stderr.
    assert "Traceback" not in result.stderr, (
        f"Expected --target with relative path to be handled gracefully; "
        f"got Python traceback in stderr:\n{result.stderr}"
    )


@pytest.mark.parametrize(
    "passed_line",
    [
        # P2 (round-13): bare PASSED in output instructions (Section 6
        # area or anywhere after Scope Report) without verdict-key or
        # summary-heading framing.
        "If zero findings, output exactly: PASSED",
        "On success: PASSED",  # `success` would not match _VERDICT_TOKEN
        "Mark the run PASSED in the manifest.",
        "Emit a single token: PASSED.",
    ],
)
def test_t27_unquoted_passed_post_section_0_fails(passed_line: str) -> None:
    """T27 (codex round-13 P2 → architectural cap rule): any UNQUOTED
    `PASSED` token appearing after the Scope Report content violates the
    spec line 152 contract. Lexical pattern enumeration (rounds 5-7, 13)
    cannot cover every future combination of verdict keys, summary
    headings, and instruction phrasings. The cap rule denies any bare
    PASSED on the post-Section-0 surface and allows only quoted forms
    (`"PASSED"` or backtick `` `PASSED` ``) used in spec self-explanation.
    """
    with _Snapshot(TEMPLATE):
        text = _baseline_text()
        # Inject after Section 0 / before Section 1.
        injection = "\n\n" + passed_line + "\n\n"
        mutated = text.replace(
            SECTION_1_HEADING,
            injection + SECTION_1_HEADING,
            1,
        )
        TEMPLATE.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            f"Expected lint to reject bare PASSED token ({passed_line!r}) on "
            f"post-Section-0 surface. Spec line 152 forbids the combined-"
            f"aggregate verb regardless of phrasing.\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )


@pytest.mark.parametrize(
    "self_explanation",
    [
        # Quoted forms used in spec self-explanation must NOT trip the cap rule.
        '\n\nThe combined-aggregate "PASSED" verb is forbidden.\n\n',
        "\n\nUse backtick form: `PASSED` is the literal token.\n\n",
        '\n\nNote: "PASSED" appears as documentation only.\n\n',
    ],
)
def test_t28_quoted_passed_self_explanation_allowed(self_explanation: str) -> None:
    """T28 (codex round-13 cap rule, allow side): the cap rule must NOT
    fire on PASSED tokens enclosed in straight quotes or backticks —
    those are the spec self-explanation forms used in the canonical
    template (lines 26 and 49) and must remain valid.
    """
    with _Snapshot(TEMPLATE):
        text = _baseline_text()
        mutated = text.replace(
            SECTION_1_HEADING,
            self_explanation + SECTION_1_HEADING,
            1,
        )
        TEMPLATE.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 0, (
            f"Expected lint to ACCEPT quoted PASSED self-explanation "
            f"({self_explanation!r}). Cap rule must allow `\"PASSED\"` and "
            f"backtick `PASSED` forms used in spec documentation prose.\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )


@pytest.mark.parametrize(
    "suffix",
    [
        " (draft)",
        " v2",
        ": revised",
        " — Updated",
    ],
)
def test_t26_scope_report_header_with_suffix_fails(suffix: str) -> None:
    """T26 (codex round-12 P2): R1 Scope Report header must be a complete
    canonical line, not a prefix. A suffixed form like
    `## Codex Audit Round N — Scope Report (draft)` must FAIL because the
    rendered prompt would carry a non-canonical header. Symmetric to T21
    (round 8) which closed the same gap on Section 1.
    """
    canonical = "## Codex Audit Round N — Scope Report"
    with _Snapshot(TEMPLATE):
        text = _baseline_text()
        # Mutate inside the live fenced Section 0 block.
        mutated = text.replace(canonical + "\n", canonical + suffix + "\n", 1)
        TEMPLATE.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            f"Expected lint to reject Scope Report header with suffix "
            f"{suffix!r}. The canonical bytes appear as a prefix only; the "
            f"actual heading title has changed.\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )


def test_t25_preamble_header_decoy_does_not_short_circuit_ordering() -> None:
    """T25 (codex round-11 P2): if a preamble decoy of the canonical
    `## Codex Audit Round N — Scope Report` line exists ahead of the
    real Section 0 (e.g. inside a documentation block), a verdict line
    placed BETWEEN that decoy and the real Scope Report content must
    still FAIL. Round-10 derived ordering_boundary from the first
    whole-file occurrence; with a preamble decoy that boundary lands too
    early and the verdict escapes the scan. Boundary must instead derive
    from the Section-0-validated header position.
    """
    with _Snapshot(TEMPLATE):
        text = _baseline_text()
        section_0_pos = text.find("## Section 0 — Scope Report")
        assert section_0_pos != -1
        # Inject (a) a preamble decoy header line before Section 0,
        # (b) a verdict line between the decoy and Section 0.
        decoy_block = (
            "## Documentation reference\n\n"
            "## Codex Audit Round N — Scope Report\n\n"
            "(decoy header — purely informational, real block lives below)\n\n"
            "verdict: PASS\n\n"
            "---\n\n"
        )
        mutated = text[:section_0_pos] + decoy_block + text[section_0_pos:]
        TEMPLATE.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            "Expected lint to reject verdict line between preamble decoy "
            "header and the real Scope Report content. Boundary derivation "
            "must use the Section-0-validated header, not first whole-file "
            "occurrence.\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )


@pytest.mark.parametrize(
    "verdict_line",
    [
        "verdict: PASS",
        "result: FAIL",
        "Final status: PASSED",
    ],
)
def test_t24_verdict_inside_fenced_block_before_canonical_header_fails(
    verdict_line: str,
) -> None:
    """T24 (codex round-10 P2): a verdict line inserted INSIDE the fenced
    Scope Report block but BEFORE the canonical
    `## Codex Audit Round N — Scope Report` header still violates spec
    line 146. Round-9 ordering fix used text_no_fences for both anchor
    discovery and prefix scan, which masked the live block entirely
    (canonical header lives in fence, so it could not be found, and any
    verdict line inside the same fence was hidden too).
    """
    with _Snapshot(TEMPLATE):
        text = _baseline_text()
        # Find the opening fence right after the Section 0 H2.
        # In the canonical template this is `\n```\n## Codex Audit Round N — Scope Report`.
        fence_open_match = re.search(r"^```\s*\n", text, re.MULTILINE)
        assert fence_open_match is not None, (
            "fixture assumption violated: opening fence not found"
        )
        fence_open_end = fence_open_match.end()
        # Inject the verdict line right after the opening fence, BEFORE
        # the canonical Scope Report header line.
        mutated = (
            text[:fence_open_end]
            + verdict_line
            + "\n\n"
            + text[fence_open_end:]
        )
        TEMPLATE.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            f"Expected lint to reject verdict line ({verdict_line!r}) inside "
            f"the fenced Scope Report block but before the canonical header. "
            f"Spec line 146 firm rule applies regardless of fence framing — "
            f"the fence IS the prompt content sent to codex.\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )


def test_t22_affected_refcodes_field_required() -> None:
    """T22 (codex round-9 P2a): `**Affected refcodes (description-only):**`
    is part of the spec line 142 contract and must be a required field.
    Removing it from Section 0 must FAIL the lint.
    """
    field = "**Affected refcodes (description-only):**"
    with _Snapshot(TEMPLATE):
        text = _baseline_text()
        section_0_pos = text.find("## Section 0 — Scope Report")
        section_1_pos = text.find("## Section 1 — Round metadata")
        assert section_0_pos != -1 and section_1_pos != -1
        section_0_block = text[section_0_pos:section_1_pos]
        assert field in section_0_block, (
            f"fixture assumption violated: field {field!r} not present in baseline Section 0"
        )
        # Drop the line carrying the field marker (within Section 0).
        section_0_lines = section_0_block.splitlines(keepends=True)
        section_0_mutated = "".join(
            ln for ln in section_0_lines if field not in ln
        )
        mutated = (
            text[:section_0_pos]
            + section_0_mutated
            + text[section_1_pos:]
        )
        TEMPLATE.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            f"Expected lint to reject Scope Report missing field {field!r} "
            f"(spec line 142 — the required affected-refcodes disclosure).\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )


@pytest.mark.parametrize(
    "verdict_line",
    [
        # P2b (round-9): verdict line between Section 0 H2 and canonical header.
        "verdict: PASS\n\n",
        "result: FAIL\n\n",
        "Final status: PASSED\n\n",
    ],
)
def test_t23_verdict_between_section_0_h2_and_canonical_header_fails(
    verdict_line: str,
) -> None:
    """T23 (codex round-9 P2b): a verdict line inserted AFTER `## Section 0`
    but BEFORE the canonical `## Codex Audit Round N — Scope Report`
    header still violates spec line 146 (Scope Report before any pass/fail
    summary). The ordering check previously scoped to text before Section
    0 H2; this layout slips through.
    """
    with _Snapshot(TEMPLATE):
        text = _baseline_text()
        section_0_h2 = "## Section 0 — Scope Report (mandatory; v3.7.1 D2)\n"
        section_0_pos = text.find(section_0_h2)
        assert section_0_pos != -1, "fixture assumption violated"
        # Inject verdict line right after the Section 0 H2, before any
        # other Section-0 content (and before the canonical fenced header).
        insert_at = section_0_pos + len(section_0_h2)
        mutated = (
            text[:insert_at]
            + "\n"
            + verdict_line
            + text[insert_at:]
        )
        TEMPLATE.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            f"Expected lint to reject verdict line ({verdict_line!r}) inserted "
            f"between Section 0 H2 and the canonical Scope Report header. "
            f"Spec line 146 requires Scope Report content to precede any "
            f"pass/fail summary surface.\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )


@pytest.mark.parametrize(
    "appended",
    [
        # P2 (round-8): Section 1 heading mutated by appending text.
        " (renamed)",
        " v2",
        ": revised",
        " — Round Metadata Override",
    ],
)
def test_t21_section_1_heading_with_appended_text_fails(appended: str) -> None:
    """T21 (codex round-8 P2): R5 Section 1 byte-equivalence sentinel must
    reject heading lines mutated by appending text. find() previously
    matched the canonical bytes as a prefix even when the line continued
    with extra title text — that's a real heading change (rendered prompt
    has different Section 1 framing) and must FAIL the byte-equivalence
    invariant.
    """
    with _Snapshot(TEMPLATE):
        text = _baseline_text()
        mutated = text.replace(
            SECTION_1_HEADING + "\n",
            SECTION_1_HEADING + appended + "\n",
            1,
        )
        TEMPLATE.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            f"Expected lint to reject Section 1 heading mutated by appending "
            f"text ({appended!r}). The canonical bytes appear as a prefix only; "
            f"the actual heading title has changed.\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )


@pytest.mark.parametrize(
    "summary_block",
    [
        # P2 (round-7): multi-line audit summary forms.
        "\n## Audit Summary\n\nThis audit PASSED.\n\n",
        "\n## Audit Summary\n\nPASSED\n\n",
        "\n## Final Verdict\n\nThis run PASSED comprehensively.\n\n",
        "\n## Audit Summary\n\nThe audit PASSED for all dimensions.\n\n",
    ],
)
def test_t20_multi_line_audit_summary_with_passed_fails(summary_block: str) -> None:
    """T20 (codex round-7 P2): R4 must catch multi-line audit summaries
    where `## Audit Summary` (or similar heading) is followed on subsequent
    lines by `PASSED` — bare or in prose like `This audit PASSED.`.
    The combined-aggregate verb is the violation regardless of whether it
    sits on the same line as the summary key.
    """
    with _Snapshot(TEMPLATE):
        text = _baseline_text()
        # Inject after Section 0 / before Section 1.
        mutated = text.replace(
            SECTION_1_HEADING,
            summary_block + SECTION_1_HEADING,
            1,
        )
        TEMPLATE.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            f"Expected lint to reject multi-line audit summary with PASSED "
            f"({summary_block!r}). Spec line 152 forbids the combined-aggregate "
            f"verb across all audit-summary surfaces.\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )


def test_t18_scope_report_header_prose_mention_does_not_satisfy_r1() -> None:
    """T18 (codex round-6 P2-8): SCOPE_REPORT_HEADER check must be
    line-anchored, not substring. A prose mention like
    `The required header is "## Codex Audit Round N — Scope Report"`
    inside Section 0 must NOT satisfy R1 if the real header line is
    missing or renamed.
    """
    with _Snapshot(TEMPLATE):
        text = _baseline_text()
        section_0_pos = text.find("## Section 0 — Scope Report")
        section_1_pos = text.find("## Section 1 — Round metadata")
        assert section_0_pos != -1 and section_1_pos != -1
        section_0_block = text[section_0_pos:section_1_pos]
        # Rename the real fenced header so it no longer matches the literal,
        # then add a prose mention carrying the literal text.
        section_0_mutated = section_0_block.replace(
            "## Codex Audit Round N — Scope Report",
            "## Codex Audit Round N — REDACTED",
            1,
        )
        prose_mention = (
            "\n\nNote: the required header line is "
            '`## Codex Audit Round N — Scope Report` (do not literally embed in prose).\n\n'
        )
        section_0_mutated = section_0_mutated.replace(
            "## Section 0 — Scope Report",
            "## Section 0 — Scope Report" + prose_mention,
            1,
        )
        mutated = (
            text[:section_0_pos]
            + section_0_mutated
            + text[section_1_pos:]
        )
        TEMPLATE.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            "Expected lint to require the canonical Scope Report header to "
            "be a real heading line (not a prose mention). Substring match "
            "lets a documentation reference satisfy R1 even when the real "
            "header is missing.\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )


@pytest.mark.parametrize(
    "multi_word_summary",
    [
        # P2-9 (round-6): multi-word verdict keys before single-word PASSED.
        "\n\nFinal verdict: PASSED\n\n",
        "\n\nAudit status: PASSED\n\n",
        "\n\nOverall verdict: PASSED\n\n",
        "\n\nFinal status: PASSED\n\n",
        "\n\nFinal Result: PASSED\n\n",
    ],
)
def test_t19_multi_word_verdict_key_with_passed_fails(multi_word_summary: str) -> None:
    """T19 (codex round-6 P2-9): R4 must catch multi-word verdict keys
    (e.g. 'Final verdict: PASSED', 'Audit status: PASSED'). The combined-
    aggregate verb is the violation regardless of the key word count.
    """
    with _Snapshot(TEMPLATE):
        text = _baseline_text()
        # Inject after Section 0 / before Section 1 (anywhere outside the
        # spec self-explanation prose).
        mutated = text.replace(
            SECTION_1_HEADING,
            multi_word_summary + SECTION_1_HEADING,
            1,
        )
        TEMPLATE.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            f"Expected lint to reject multi-word verdict-key + PASSED line "
            f"({multi_word_summary!r}). Spec line 152 forbids the verb "
            f"regardless of how many words the key has.\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )


@pytest.mark.parametrize(
    "summary_block",
    [
        # P2-5 (round-5): non-`verdict` key followed by combined-aggregate PASSED.
        "\n## Audit Summary\n\nOverall status: PASSED\n\n---\n",
        "\n## Audit Summary\n\nResult: PASSED\n\n---\n",
        "\n## Audit Summary\n\nFinal: PASSED\n\n---\n",
    ],
)
def test_t16_non_verdict_key_with_passed_fails(summary_block: str) -> None:
    """T16 (codex round-5 P2-5): R4 must reject combined-aggregate 'PASSED'
    summaries that use any key, not just `verdict`. The spec line 152
    contract is on the *verb*, not the surrounding key.
    """
    with _Snapshot(TEMPLATE):
        text = _baseline_text()
        # Inject the summary block just before Section 1 (after Section 0).
        mutated = text.replace(
            SECTION_1_HEADING,
            summary_block + SECTION_1_HEADING,
            1,
        )
        TEMPLATE.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            f"Expected lint to reject combined-aggregate 'PASSED' under non-verdict key "
            f"({summary_block!r}). Spec line 152 forbids the verb regardless of the key.\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )


@pytest.mark.parametrize(
    "bare_verdict_line",
    [
        # P2-6 (round-5): bare verdict line before Section 0 with no `## Summary` heading.
        "verdict: PASS\n\n",
        "overall: FAIL\n\n",
        "result: PASSED\n\n",
        "final status: PASS\n\n",
    ],
)
def test_t17_bare_verdict_before_section_0_fails(bare_verdict_line: str) -> None:
    """T17 (codex round-5 P2-6): R1 ordering check must reject ANY pass/fail
    summary line ahead of Section 0, not only ones with a `## ... Summary`
    heading. A bare `verdict: PASS` line still counts as a pass/fail summary
    per spec line 146.
    """
    with _Snapshot(TEMPLATE):
        text = _baseline_text()
        section_0_pos = text.find("## Section 0 — Scope Report")
        assert section_0_pos != -1
        # Inject bare verdict line BEFORE Section 0 (no heading framing).
        mutated = (
            text[:section_0_pos]
            + bare_verdict_line
            + text[section_0_pos:]
        )
        TEMPLATE.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            f"Expected lint to reject bare verdict line before Section 0 "
            f"({bare_verdict_line!r}). Spec line 146 firm rule: Scope Report "
            f"must appear BEFORE any pass/fail summary, regardless of heading framing.\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )


def test_t15_forbidden_passed_verb_inside_fenced_block_fails() -> None:
    """T15 (codex round-4 P2): combined-aggregate 'PASSED' inside a fenced
    code block must FAIL. Fenced blocks are the actual prompt content sent
    to codex (the canonical Scope Report header lives in a fence), so the
    forbidden verb appearing there defeats the spec line 152 contract just
    as much as outside a fence.
    """
    with _Snapshot(TEMPLATE):
        text = _baseline_text()
        # Locate Section 0 fenced block and inject the forbidden verb there.
        fence_start = text.find("```\n## Codex Audit Round N — Scope Report")
        assert fence_start != -1, (
            "fixture assumption violated: canonical fenced Scope Report header missing"
        )
        # Inject "verdict: PASSED" line right after the header. This is
        # inside the fenced block — fence-strip would blank it, but the
        # rendered prompt sent to codex preserves it verbatim.
        injection_target = "## Codex Audit Round N — Scope Report\n\n"
        injection_pos = text.find(injection_target, fence_start)
        assert injection_pos != -1
        insert_at = injection_pos + len(injection_target)
        mutated = (
            text[:insert_at]
            + "verdict: PASSED\n\n"
            + text[insert_at:]
        )
        TEMPLATE.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            "Expected lint to reject combined-aggregate 'PASSED' verb even "
            "inside a fenced code block (the fenced content IS the prompt "
            "codex sees). Spec line 152 forbids the combined-aggregate verb "
            "anywhere in the audit summary surface.\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )


def test_t13_section_1_decoy_inside_fence_does_not_satisfy_invariant() -> None:
    """T13 (codex round-3 P2-3): a fenced-block decoy carrying the exact
    Section 1 heading text must NOT satisfy the byte-equivalence sentinel.
    The real top-level Section 1 heading is removed/renamed; lint must FAIL.
    """
    with _Snapshot(TEMPLATE):
        text = _baseline_text()
        # 1) Rename the real top-level Section 1 heading (capitalization swap).
        # 2) Inject a fenced-code-block carrying the exact original heading
        #    text so a whole-file find() would falsely satisfy R5.
        renamed = text.replace(
            "## Section 1 — Round metadata",
            "## Section 1 — Round Metadata",  # title-case mutation
            1,
        )
        decoy_fence = (
            "\n\n## Appendix — historical example\n\n"
            "```\n"
            "## Section 1 — Round metadata\n"
            "Sample round metadata content (decoy).\n"
            "```\n"
        )
        TEMPLATE.write_text(renamed + decoy_fence, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            "Expected lint to enforce Section 1 byte-equivalence at top level, "
            "rejecting decoy heading inside a fenced block.\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )


def test_t14_scope_report_header_decoy_in_preamble_does_not_satisfy_r1() -> None:
    """T14 (codex round-3 P2-4): a decoy SCOPE_REPORT_HEADER appearing in
    the preamble before Section 0 must NOT satisfy R1 if the real header
    is missing from Section 0. The lint must check the canonical header
    inside Section 0, not whole-file find().
    """
    with _Snapshot(TEMPLATE):
        text = _baseline_text()
        # 1) Inject the canonical Scope Report header into the preamble
        #    (in a fenced block so it doesn't break Section 0 anchor detection).
        # 2) Remove the canonical Scope Report header from Section 0.
        preamble_decoy = (
            "## Preamble historical reference\n\n"
            "```\n"
            "## Codex Audit Round N — Scope Report\n"
            "(decoy: this is documentation, not the live block)\n"
            "```\n\n"
        )
        # Find Section 0 so the decoy is inserted before it.
        section_0_pos = text.find("## Section 0 — Scope Report")
        assert section_0_pos != -1
        # Remove the canonical header inside Section 0 (it lives in a fenced block).
        section_1_pos = text.find("## Section 1 — Round metadata")
        section_0_block = text[section_0_pos:section_1_pos]
        section_0_mutated = section_0_block.replace(
            "## Codex Audit Round N — Scope Report",
            "## Codex Audit Round N — REDACTED",
            1,
        )
        mutated = (
            text[:section_0_pos]
            + section_0_mutated
            + text[section_1_pos:]
        )
        # Insert preamble decoy before Section 0.
        section_0_pos_after = mutated.find("## Section 0 — Scope Report")
        mutated = (
            mutated[:section_0_pos_after]
            + preamble_decoy
            + mutated[section_0_pos_after:]
        )
        TEMPLATE.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            "Expected lint to enforce SCOPE_REPORT_HEADER presence inside "
            "Section 0, rejecting preamble decoy that satisfies whole-file find().\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )


def test_t12_target_outside_repo_does_not_crash(tmp_path) -> None:
    """T12 (codex round-2 P2-2): --target with an absolute path outside
    the repo must not crash. Lint should display the raw path and proceed.
    """
    fixture = tmp_path / "fake_template.md"
    # Minimal valid Scope Report fixture so the lint reports PASS not FAIL.
    fixture.write_text(
        "# Test\n\n"
        "## Section 0 — Scope Report\n\n"
        "```\n"
        "## Codex Audit Round N — Scope Report\n\n"
        "**Total entries audited:** <N>\n"
        "**Entries with retrieved original source:** <N>\n"
        "**Entries description-only (no retrieved source):** <N>\n"
        "**Audit scope warning:** test\n"
        "```\n\n"
        "verified-against-source\n"
        "description-internally-consistent\n"
        "unaudited-due-to-missing-source\n\n"
        "## Section 1 — Round metadata\n\n"
        "body\n",
        encoding="utf-8",
    )
    result = subprocess.run(
        [sys.executable, str(LINT), "--target", str(fixture)],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert "Traceback" not in result.stderr, (
        f"Expected --target outside the repo to be handled gracefully; "
        f"got Python traceback in stderr:\n{result.stderr}"
    )
    assert result.returncode in (0, 1), (
        f"Expected deterministic exit code; got {result.returncode}"
    )
