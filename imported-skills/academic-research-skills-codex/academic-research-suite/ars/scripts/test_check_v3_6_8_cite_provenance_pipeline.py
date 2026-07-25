"""Mutation tests for ARS v3.7.1 Step 3b — Cite-Time Provenance Finalizer.

Spec: docs/design/2026-04-30-ars-v3.6.8-trust-provenance-and-drift-transparency-spec.md
      § Step 3b — Pipeline finalizer (academic-pipeline mode)

Step 3b acceptance (spec lines 454-457):
- Orchestrator subsection present
- Mutation test: removing any of the 4 matrix rows fails lint
- Revision-loop test: a draft passed through finalizer twice produces
  identical resolved markers; new bare `<!--ref:slug-->` comments in the
  revised pass are resolved correctly without invalidating prior `ok`
  markers (round-1 codex P2 finding 11)

The lint runs grep-class checks against the actual repo file. Each
mutation test backs up `pipeline_orchestrator_agent.md`, mutates,
runs the lint as a subprocess, and restores the file in `finally`.
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
LINT = REPO_ROOT / "scripts" / "check_v3_6_8_cite_provenance_pipeline.py"
TARGET = REPO_ROOT / "academic-pipeline" / "agents" / "pipeline_orchestrator_agent.md"

FINALIZER_HEADING = "## Cite-Time Provenance Finalizer (v3.7.1)"


def _run_lint() -> subprocess.CompletedProcess[str]:
    """Run the v3.6.8 cite-provenance pipeline lint."""
    return subprocess.run(
        [sys.executable, str(LINT)],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )


class _Snapshot:
    """Backs up a file's bytes; restores on context exit (exception-safe)."""

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


# =========================================================================
# Happy path
# =========================================================================


def test_happy_path_passes_on_clean_tree() -> None:
    """Untouched pipeline_orchestrator (with finalizer subsection) → lint passes."""
    result = _run_lint()
    assert result.returncode == 0, (
        f"Expected exit 0 on clean tree, got {result.returncode}.\n"
        f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
    )
    assert "PASSED" in result.stdout
    assert "pipeline_orchestrator_agent.md" in result.stdout


# =========================================================================
# Subsection presence (spec acceptance: Orchestrator subsection present)
# =========================================================================


def test_finalizer_subsection_missing_fails() -> None:
    """Removing the entire `## Cite-Time Provenance Finalizer (v3.7.1)`
    subsection from pipeline_orchestrator_agent.md must hard-fail."""
    with _Snapshot(TARGET):
        text = TARGET.read_text(encoding="utf-8")
        assert FINALIZER_HEADING in text, "fixture missing finalizer heading"
        # Replace the canonical heading with a non-marker heading so the
        # extractor returns None.
        mutated = text.replace(
            FINALIZER_HEADING,
            "## (former finalizer heading)",
            1,
        )
        TARGET.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            "Removing the finalizer subsection must hard-fail; "
            f"got rc={result.returncode}\nstdout:\n{result.stdout}"
        )
        assert "Cite-Time Provenance Finalizer" in result.stdout or "finalizer" in result.stdout.lower()


# =========================================================================
# 4-cell matrix rows (spec lines 174-179)
# =========================================================================
#
# Each row is keyed by its WARN level / status:
#   Row 1: HIGH WARN  → `[UNVERIFIED CITATION — NO ORIGINAL]`
#   Row 2: MED WARN   → `[UNVERIFIED CITATION — AI HAS NOT CROSS-CHECKED]`
#   Row 3: LOW WARN   → `<!--ref:slug LOW-WARN-->` + per-section pre-finalization checklist
#   Row 4: ok         → `<!--ref:slug ok-->`


def test_high_warn_row_missing_fails() -> None:
    """Row 1 (HIGH WARN — NO ORIGINAL) must be present.

    Spec line 176: HIGH WARN row maps source_acquired=false to
    `[UNVERIFIED CITATION — NO ORIGINAL]<!--ref:slug-->`.
    """
    with _Snapshot(TARGET):
        text = TARGET.read_text(encoding="utf-8")
        # Replace the row's canonical phrase so the lint can't find it.
        marker = "UNVERIFIED CITATION — NO ORIGINAL"
        assert marker in text, f"fixture missing row-1 marker {marker!r}"
        mutated = text.replace(marker, "REDACTED-ROW-1", 1)
        TARGET.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1
        assert "HIGH" in result.stdout or "row 1" in result.stdout.lower() or "NO ORIGINAL" in result.stdout


def test_med_warn_row_missing_fails() -> None:
    """Row 2 (MED WARN — AI HAS NOT CROSS-CHECKED) must be present.

    Spec line 177: MED WARN row maps (acquired=true, verified=false,
    human=false) to `[UNVERIFIED CITATION — AI HAS NOT CROSS-CHECKED]`.
    """
    with _Snapshot(TARGET):
        text = TARGET.read_text(encoding="utf-8")
        marker = "UNVERIFIED CITATION — AI HAS NOT CROSS-CHECKED"
        assert marker in text, f"fixture missing row-2 marker {marker!r}"
        mutated = text.replace(marker, "REDACTED-ROW-2", 1)
        TARGET.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1
        assert "MED" in result.stdout or "CROSS-CHECKED" in result.stdout or "row 2" in result.stdout.lower()


def test_low_warn_row_missing_fails() -> None:
    """Row 3 (LOW WARN — `<!--ref:slug LOW-WARN-->`) must be present.

    Spec line 178: LOW WARN row maps (acquired=true, verified=true,
    human=false) to `<!--ref:slug LOW-WARN-->`.

    Note: the finalizer subsection mentions LOW-WARN multiple times
    (matrix row, prose discussion, LOW-WARN-promotion paragraph). This
    mutation strips ALL occurrences so the canonical phrase is fully
    absent from the block.
    """
    with _Snapshot(TARGET):
        text = TARGET.read_text(encoding="utf-8")
        marker = "LOW-WARN"
        assert marker in text, f"fixture missing row-3 marker {marker!r}"
        # Strip ALL occurrences to make mutation effective; replace_all=False
        # would leave later mentions standing and the lint would still pass.
        mutated = text.replace(marker, "REDACTED-ROW-3")
        TARGET.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1
        assert "LOW" in result.stdout or "row 3" in result.stdout.lower() or "LOW-WARN" in result.stdout


def test_ok_row_missing_fails() -> None:
    """Row 4 (`<!--ref:slug ok-->`) must be present.

    Spec line 179: OK row maps all-true triple to `<!--ref:slug ok-->`.

    Note: the canonical OK marker `<!--ref:slug ok-->` appears in both
    the matrix row and the idempotency / LOW-WARN-promotion prose. Strip
    ALL occurrences for an effective mutation.
    """
    with _Snapshot(TARGET):
        text = TARGET.read_text(encoding="utf-8")
        marker = "<!--ref:slug ok-->"
        assert marker in text, f"fixture missing row-4 marker {marker!r}"
        mutated = text.replace(marker, "<!--ref:slug-redacted-->")
        TARGET.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1
        assert "ok" in result.stdout.lower() or "row 4" in result.stdout.lower() or "<!--ref:slug ok-->" in result.stdout


# =========================================================================
# Idempotency clause (spec line 181)
# =========================================================================


def test_idempotency_clause_missing_fails() -> None:
    """The subsection must state that the finalizer pass is idempotent on
    its own resolved markers (re-running on `<!--ref:slug ok-->` is a no-op).

    Spec line 181 sentence: 'Each finalizer pass is idempotent on its own
    resolved markers'.
    """
    with _Snapshot(TARGET):
        text = TARGET.read_text(encoding="utf-8")
        marker = "idempotent"
        assert marker in text, "fixture missing idempotency marker"
        # Strip every occurrence — heading "Idempotency" and prose use of
        # "idempotent" both must go for the lint to flag the absence.
        mutated = text.replace(marker, "non-deterministic")
        TARGET.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1
        assert "idempot" in result.stdout.lower()


# =========================================================================
# Revision-loop preservation (spec line 181 + acceptance line 457)
# =========================================================================


def test_revision_loop_preservation_clause_missing_fails() -> None:
    """The subsection must state that on revision loops, resolved markers
    do not invalidate; new bare markers are resolved on the next pass.

    Spec line 181: 'On revision loops ... the finalizer re-runs against
    the current draft and re-resolves any newly-emitted bare
    `<!--ref:slug-->` comments; resolved markers do not invalidate.'
    """
    with _Snapshot(TARGET):
        text = TARGET.read_text(encoding="utf-8")
        # The canonical sentence carries the phrase "do not invalidate"
        # immediately after the revision-loop description.
        marker = "do not invalidate"
        assert marker in text, "fixture missing revision-loop preservation phrase"
        mutated = text.replace(marker, "are reset and re-resolved", 1)
        TARGET.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1
        assert "revision" in result.stdout.lower() or "invalidate" in result.stdout.lower()


# =========================================================================
# Peer-file join (spec line 172)
# =========================================================================


def test_low_warn_matrix_drift_with_promotion_paragraph_intact_fails() -> None:
    """R1 P2-1 closure: matrix-row drift to e.g. `LOW-WARNING` while the
    promotion paragraph still mentions `LOW-WARN` must FAIL.

    Pre-R1 the lint anchored on bare `LOW-WARN` substring, so the
    promotion paragraph alone could satisfy the check while the matrix
    row drifted. R1 anchors on TWO tokens: the resolved marker form
    `<!--ref:slug LOW-WARN-->` AND the `per-section` checklist phrase.
    This test mutates ONLY the matrix-row's `<!--ref:slug LOW-WARN-->`
    marker (not the bare `LOW-WARN` references in surrounding prose) and
    asserts the lint catches the drift.
    """
    with _Snapshot(TARGET):
        text = TARGET.read_text(encoding="utf-8")
        # The matrix-row marker is `<!--ref:slug LOW-WARN-->` exactly.
        matrix_marker = "<!--ref:slug LOW-WARN-->"
        assert matrix_marker in text, "fixture missing matrix-row LOW-WARN marker"
        # Strip ALL occurrences of the resolved marker form. Bare
        # `LOW-WARN` mentions in prose remain.
        mutated = text.replace(matrix_marker, "<!--ref:slug LOW-WARNING-->")
        TARGET.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            "R1 P2-1: matrix-row drift on LOW-WARN marker must fail "
            "the lint even when promotion-paragraph LOW-WARN is intact"
        )


def test_low_warn_per_section_checklist_clause_missing_fails() -> None:
    """R1 P2-1 + R2 P2 closure: removing the matrix-row-unique phrase
    `per-section pre-finalization checklist` must FAIL the lint.

    R2 P2 closure: the bare `per-section` substring appears in BOTH the
    matrix row AND the LOW-WARN-promotion paragraph (`per-section
    checklist artifact`). The R2 anchor uses the fuller canonical phrase
    that is unique to the matrix row, so mutating ONLY the matrix-row
    occurrence (leaving the promotion paragraph intact) is sufficient
    to make the lint fail.
    """
    with _Snapshot(TARGET):
        text = TARGET.read_text(encoding="utf-8")
        marker = "per-section pre-finalization checklist"
        assert marker in text, "fixture missing matrix-row checklist phrase"
        # Mutate the FULL phrase so the matrix row no longer carries the
        # canonical clause; the promotion paragraph's `per-section
        # checklist artifact` (no `pre-finalization`) is left intact, so
        # if the lint anchored on bare `per-section` the test would
        # pre-R2 false-pass.
        mutated = text.replace(marker, "global checklist")
        TARGET.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            "R2 P2: matrix-row-only `per-section pre-finalization "
            "checklist` mutation must fail the lint"
        )


def test_ok_matrix_row_canonical_clause_drift_caught() -> None:
    """R3 P2-1 closure: mutate ONLY the matrix-row's `**OK**: replace with`
    canonical clause (leaving `<!--ref:slug ok-->` in the LOW-WARN-promotion
    paragraph intact). Pre-R3 lint anchored only on bare `<!--ref:slug ok-->`,
    so matrix-row drift was not detected when the promotion paragraph still
    mentioned the marker.
    """
    with _Snapshot(TARGET):
        text = TARGET.read_text(encoding="utf-8")
        marker = "**OK**: replace with"
        assert marker in text, "fixture missing OK matrix-row clause"
        # Mutate ONLY the canonical clause; leave bare `<!--ref:slug ok-->`
        # in the surrounding prose.
        mutated = text.replace(marker, "OK: clear with")
        # Sanity: bare `<!--ref:slug ok-->` must survive elsewhere in the
        # block to prove R3 P2-1 (otherwise the test isn't proving its claim).
        assert "<!--ref:slug ok-->" in mutated, (
            "fixture invariant violated: promotion paragraph lost"
        )
        TARGET.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            "R3 P2-1: matrix-row OK canonical clause drift must fail "
            f"the lint; got rc={result.returncode}"
        )


def test_rescind_affordance_clause_missing_fails() -> None:
    """R3 P2-2 closure: the canonical block must mention `/ars-unmark-read`
    so the bidirectional rescind contract survives prose edits.
    """
    with _Snapshot(TARGET):
        text = TARGET.read_text(encoding="utf-8")
        marker = "/ars-unmark-read"
        assert marker in text, "fixture missing /ars-unmark-read mention"
        mutated = text.replace(marker, "/ars-rescind")
        TARGET.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            "R3 P2-2: removing /ars-unmark-read must fail the lint"
        )


def test_demote_language_clause_missing_fails() -> None:
    """R3 P2-2 closure: the canonical block must explicitly describe
    demotion (e.g. `ok` → `LOW-WARN`). Anchor is the `demot` stem so
    both `demote` and `demotion` count.
    """
    with _Snapshot(TARGET):
        text = TARGET.read_text(encoding="utf-8")
        marker = "demot"
        assert marker in text, "fixture missing demot* language"
        # Strip ALL occurrences (covers `demote`, `demotion`, `demoted`).
        mutated = text.replace(marker, "REDACT")
        TARGET.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            "R3 P2-2: removing demote/demotion language must fail the lint"
        )


def test_med_warn_row_wildcard_human_read_caught() -> None:
    """R3 P1 closure: spec line 177 wrote `(true, false, false)` for MED
    WARN, leaving `(true, false, true)` undefined. R3 changed the prompt
    prose to use `—` (wildcard) for `human_read_source` in row 2 so the
    matrix is total over the 8 input combinations. The MED WARN canonical
    phrase `UNVERIFIED CITATION — AI HAS NOT CROSS-CHECKED` is unchanged;
    this test pins that the MED WARN row's third column carries `—`
    rather than `false` (or any non-wildcard token), so the totality
    contract is enforced at the prose level.
    """
    text = TARGET.read_text(encoding="utf-8")
    # The MED WARN row in the canonical block has the phrase
    # `UNVERIFIED CITATION — AI HAS NOT CROSS-CHECKED`. Locate that
    # phrase, walk back to the start of its table row, and assert the
    # third column is `—` (em-dash) and not any other token.
    import re as _re
    # Find the MED-WARN row by anchor on its unique phrase.
    pos = text.find("UNVERIFIED CITATION — AI HAS NOT CROSS-CHECKED")
    assert pos != -1, "fixture missing MED WARN phrase"
    # Walk back to the line start.
    line_start = text.rfind("\n", 0, pos) + 1
    line_end = text.index("\n", pos)
    row = text[line_start:line_end]
    # Row format: `| true              | false                             | <COL3>               | **MED WARN**: ...`
    # Split by `|` and find columns.
    parts = [p.strip() for p in row.split("|")]
    # parts[0]='', parts[1]='true', parts[2]='false', parts[3]=col3, parts[4]=resolution
    assert len(parts) >= 5, f"expected ≥5 |-delimited parts in MED row, got {parts}"
    col3 = parts[3]
    assert col3 == "—", (
        f"R3 P1: MED WARN row's `human_read_source` column must be `—` "
        f"(wildcard) so the matrix is total over the 8 input combinations; "
        f"got {col3!r}. Spec line 177 wrote `false` but that leaves "
        f"`(true, false, true)` undefined — the wildcard fix is intentional."
    )


def test_low_warn_promotion_paragraph_alone_does_not_satisfy_matrix_row() -> None:
    """R2 P2 closure: prove the matrix-row-only mutation does NOT
    accidentally pass when the promotion paragraph still mentions
    `per-section` (without `pre-finalization`).

    Mutates the matrix row's full anchor phrase but leaves the
    promotion paragraph's bare `per-section` reference intact. This
    pins the canonical phrase as the sole matrix-row anchor.
    """
    with _Snapshot(TARGET):
        text = TARGET.read_text(encoding="utf-8")
        # Confirm both occurrences exist before mutation.
        assert "per-section pre-finalization checklist" in text
        # Strip ONLY the full phrase; bare `per-section` in the
        # promotion paragraph (`per-section checklist artifact`) stays.
        mutated = text.replace(
            "per-section pre-finalization checklist",
            "global checklist",
        )
        # Sanity: the promotion paragraph's `per-section` reference must
        # survive the mutation (otherwise the test isn't proving what
        # it claims).
        assert "per-section checklist" in mutated, (
            "fixture invariant violated: promotion paragraph lost"
        )
        TARGET.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1


def test_peer_file_join_clause_missing_fails() -> None:
    """The subsection must reference the peer-file
    `<session>_human_read_log.yaml` (or the canonical computed form
    `<passport-stem>_human_read_log.yaml` per §3.6 round-5 R5-003 amend)
    as the join source for `human_read_source`.
    """
    with _Snapshot(TARGET):
        text = TARGET.read_text(encoding="utf-8")
        # Canonical token: `human_read_log.yaml` (may appear in both the
        # shorthand `<session>_human_read_log.yaml` form and the §3.6
        # computed form within the same paragraph). Strip ALL occurrences.
        marker = "human_read_log.yaml"
        assert marker in text, f"fixture missing peer-file marker {marker!r}"
        mutated = text.replace(marker, "human_read_data.json")
        TARGET.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1
        assert "human_read" in result.stdout.lower() or "peer" in result.stdout.lower() or "human_read_log" in result.stdout
