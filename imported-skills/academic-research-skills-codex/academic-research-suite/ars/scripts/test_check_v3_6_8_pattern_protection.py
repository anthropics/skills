"""Mutation tests for ARS v3.7.1 byte-equivalence SHA gate.

Spec: docs/design/2026-04-30-ars-v3.6.8-trust-provenance-and-drift-transparency-spec.md
      § Step 0 — Lint manifest separation (round-1 codex F-004 amend)

Tests verify that:
  1. Happy path: untouched v3.6.7 PATTERN PROTECTION blocks pass.
  2. Mutation: any byte change inside a v3.6.7-tagged block fails.
  3. Additive boundary: edits OUTSIDE v3.6.7-tagged blocks (e.g. appending
     a new "Two-Layer Citation Emission" section after the block) do NOT
     trigger SHA mismatch.
  4. v3.6.8 manifest shape validation (scope tag, files list).
  5. PR-1 expected state (v3.6.8 manifest with empty 'files' list) is OK.
  6. Boundary errors (v3.6.7 marker missing at HEAD; manifest absent).

The lint runs git operations against the actual repo, so each mutation
test backs up the file under test, mutates, runs the lint as a subprocess,
and restores the file in `finally` to keep the working tree clean.
"""
from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
LINT = REPO_ROOT / "scripts" / "check_v3_6_8_pattern_protection.py"
V3_6_7_MANIFEST = REPO_ROOT / "scripts" / "v3_6_7_inversion_manifest.json"
V3_6_8_MANIFEST = REPO_ROOT / "scripts" / "v3_6_8_inversion_manifest.json"

# v3.6.7-protected agent files. We pick synthesis_agent.md as the canonical
# mutation target throughout; the lint hashes all three so mutating any one
# proves the gate works against the full manifest.
TARGET_AGENT = REPO_ROOT / "deep-research" / "agents" / "synthesis_agent.md"
PROTECTION_MARKER = "## PATTERN PROTECTION (v3.6.7)"


def _run_lint() -> subprocess.CompletedProcess[str]:
    """Run the v3.6.8 lint as a subprocess (so its sys.exit propagates)."""
    return subprocess.run(
        [sys.executable, str(LINT)],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )


# ---------- Helpers for mutation + restore (file-level snapshot) ----------


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


# ---------- Tests ----------


def test_happy_path_passes_on_clean_tree() -> None:
    """Untouched v3.6.7 blocks → SHA gate passes."""
    result = _run_lint()
    assert result.returncode == 0, (
        f"Expected exit 0 on clean tree, got {result.returncode}.\n"
        f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
    )
    assert "PASSED" in result.stdout
    # All three v3.6.7-protected files reported.
    assert "synthesis_agent.md" in result.stdout
    assert "research_architect_agent.md" in result.stdout
    assert "report_compiler_agent.md" in result.stdout


def test_mutation_inside_v3_6_7_block_fails() -> None:
    """Inject 1 byte inside the v3.6.7 PATTERN PROTECTION block → exit 1 + FAIL diagnostic."""
    with _Snapshot(TARGET_AGENT):
        text = TARGET_AGENT.read_text(encoding="utf-8")
        pos = text.find(PROTECTION_MARKER)
        assert pos != -1, "marker missing in test fixture (test would be vacuous)"
        # Inject a stray space at end of the marker line (still inside block).
        nl = text.index("\n", pos)
        mutated = text[:nl] + " " + text[nl:]
        TARGET_AGENT.write_text(mutated, encoding="utf-8")

        result = _run_lint()
        assert result.returncode == 1
        assert "BYTE-EQUIVALENCE FAIL" in result.stdout
        assert "synthesis_agent.md" in result.stdout
        assert "v3.7.1 boundary rule violated" in result.stdout


def test_appending_new_h2_directly_after_eof_newline_passes() -> None:
    """Append a new H2 directly after the file's trailing newline → SHA gate passes.

    Boundary rule (spec §388): v3.7.1 MAY add new prompt sections OUTSIDE
    the v3.6.7 PATTERN PROTECTION block. When the v3.6.7 block runs to EOF
    (the case for all three current manifest files), the appended H2 must
    be placed IMMEDIATELY after the file's trailing newline — no extra
    blank line — so the heading-based extractor's range stays byte-equal
    to the base commit's range. (The extractor terminates at the next
    H1/H2/H3 line; the bytes inside the range are file[marker_pos:next_h_line].
    Inserting a blank line between EOF and the new H2 would extend the
    extracted range by those blank-line bytes and trigger SHA mismatch.)

    This test pins the contract for Step 3a's "Two-Layer Citation Emission"
    section addition: append directly, no blank-line separator.
    """
    with _Snapshot(TARGET_AGENT):
        text = TARGET_AGENT.read_text(encoding="utf-8")
        # File already ends with a trailing newline; append H2 immediately.
        # NO leading "\n\n" — that would expand the v3.6.7 block range.
        assert text.endswith("\n"), "fixture assumption (file ends with newline) violated"
        appended = text + "## Two-Layer Citation Emission (v3.7.1 placeholder)\n\nbody\n"
        TARGET_AGENT.write_text(appended, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 0, (
            f"Appending H2 directly after EOF newline must keep byte-"
            f"equivalence; lint should PASS.\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )


def test_inserting_blank_line_between_v367_and_step3a_blocks_fails() -> None:
    """Inserting a blank line between the v3.6.7 PATTERN PROTECTION block and
    the Step 3a Two-Layer Citation Emission block → SHA mismatch.

    Pins the contract: the Step 3a block heading must directly follow the
    v3.6.7 block's last byte (no blank-line separator), otherwise the
    blank-line bytes get absorbed into the v3.6.7 extractor's range and
    break byte-equivalence.

    Step 3a populated the v3.6.7-protected files with a `## Two-Layer
    Citation Emission (v3.7.1)` block immediately following the
    `## PATTERN PROTECTION (v3.6.7)` block (no blank line). This test
    inserts a single blank line at the boundary and asserts the SHA gate
    catches it.

    Pre-Step-3a, the v3.6.7 block ran to EOF; the analogous test was
    `test_appending_new_h2_with_blank_line_separator_fails`. Step 3a's
    arrival means the v3.6.7 block now ends at the Two-Layer heading line,
    so the failure mode shifts from "blank line absorbed at EOF" to "blank
    line absorbed at the boundary between two H2 sections" — same lint
    behaviour, updated geometry.
    """
    with _Snapshot(TARGET_AGENT):
        text = TARGET_AGENT.read_text(encoding="utf-8")
        marker_step3a = "## Two-Layer Citation Emission (v3.7.1)"
        idx = text.find(marker_step3a)
        assert idx != -1, (
            "fixture missing Step 3a block; cannot test boundary contract"
        )
        # Insert a single blank line right before the Step 3a heading.
        # Pre-mutation: ...state.\n## Two-Layer...
        # Post-mutation: ...state.\n\n## Two-Layer...
        # The extra "\n" falls inside the v3.6.7 extractor's range
        # (v3.6.7 block is text[v367_pos : step3a_heading_line_start]).
        mutated = text[:idx] + "\n" + text[idx:]
        TARGET_AGENT.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            "Inserting a blank line between v3.6.7 and Step 3a blocks must "
            "trigger SHA mismatch (the blank line bytes fall inside the "
            "v3.6.7 extractor range). If this test fails, the contract for "
            "Step 3a's no-blank-line boundary has weakened and v3.7.1 "
            "boundary rule is at risk."
        )
        assert "BYTE-EQUIVALENCE FAIL" in result.stdout


def test_v3_6_8_manifest_scope_must_be_correct() -> None:
    """Wrong scope tag → lint refuses to run (clear error)."""
    with _Snapshot(V3_6_8_MANIFEST):
        data = json.loads(V3_6_8_MANIFEST.read_text(encoding="utf-8"))
        data["scope"] = "v3.6.7-only"  # wrong — this is v3.6.8 manifest
        V3_6_8_MANIFEST.write_text(json.dumps(data), encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1
        assert "v3.6.8-only" in result.stdout
        assert "scope" in result.stdout


def test_v3_6_8_manifest_files_must_be_list() -> None:
    """'files' as non-list → reject."""
    with _Snapshot(V3_6_8_MANIFEST):
        V3_6_8_MANIFEST.write_text(
            json.dumps({"scope": "v3.6.8-only", "files": "not-a-list"}),
            encoding="utf-8",
        )
        result = _run_lint()
        assert result.returncode == 1
        assert "list of strings" in result.stdout


def test_pr1_initial_state_empty_files_list_is_ok() -> None:
    """PR-1 ships v3.6.8 manifest with files: [] until Step 3a populates."""
    with _Snapshot(V3_6_8_MANIFEST):
        V3_6_8_MANIFEST.write_text(
            json.dumps({"scope": "v3.6.8-only", "files": []}),
            encoding="utf-8",
        )
        result = _run_lint()
        assert result.returncode == 0, (
            f"Empty v3.6.8 'files' list is the expected PR-1 state and must "
            f"NOT block the lint.\nstdout:\n{result.stdout}"
        )


def test_v3_6_7_manifest_deletion_hard_fails() -> None:
    """v3.6.7 manifest is the source of truth. Missing it → hard error.

    After the round-2 anti-self-baseline guard, deletion is caught earlier:
    the guard's HEAD-vs-base comparison sees the file missing at HEAD but
    present at the PR base and rejects with a deletion-specific message.
    The guard message is more precise than the legacy "manifest missing"
    bare error, so this test just asserts a hard failure with a v3.7.1 lint
    error that mentions the manifest.
    """
    with _Snapshot(V3_6_7_MANIFEST):
        V3_6_7_MANIFEST.unlink()
        result = _run_lint()
        assert result.returncode == 1
        # Either the guard catches it ("missing at PR HEAD") or the inner
        # loader catches it ("v3.6.7 manifest missing"); both are correct.
        assert (
            "v3.6.7 manifest" in result.stdout
            and ("missing" in result.stdout or "guard" in result.stdout)
        ), f"Expected manifest-missing error; got: {result.stdout}"


def test_v3_6_8_manifest_deletion_hard_fails() -> None:
    """Missing v3.6.8 manifest → hard error (lint configuration broken)."""
    with _Snapshot(V3_6_8_MANIFEST):
        V3_6_8_MANIFEST.unlink()
        result = _run_lint()
        assert result.returncode == 1
        assert "v3.6.8 manifest missing" in result.stdout


def test_heading_prefix_mutation_is_caught() -> None:
    """Round-3 codex P2 closure: spec § 388 says the canonical byte range
    starts at the LINE containing `## PATTERN PROTECTION (v3.6.7)`, so the
    `## ` heading prefix is part of the hashed bytes.

    The v3.6.7 lint's underlying `_extract_block` does case-insensitive
    substring search for the marker text and returns a slice starting at
    `PATTERN...` — silently dropping the heading prefix. That's fine for
    v3.6.7's invariant greps, but it would let the v3.7.1 SHA gate accept
    a `## → ### ` mutation as byte-equivalent.

    This test mutates `## PATTERN PROTECTION (v3.6.7)` to
    `### PATTERN PROTECTION (v3.6.7)` and asserts the gate FAILS. The
    v3.6.8 lint extends the extractor's start position backward to the
    start of the marker's line specifically to close this gap.
    """
    with _Snapshot(TARGET_AGENT):
        text = TARGET_AGENT.read_text(encoding="utf-8")
        mutated = text.replace(
            "## PATTERN PROTECTION (v3.6.7)",
            "### PATTERN PROTECTION (v3.6.7)",
            1,
        )
        assert mutated != text, "heading-mutation fixture failed to apply"
        TARGET_AGENT.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            "Heading-prefix mutation must be caught by the SHA gate "
            "(round-3 codex P2 closure)."
        )
        assert "BYTE-EQUIVALENCE FAIL" in result.stdout


def test_extractor_includes_heading_prefix_bytes() -> None:
    """Verify the v3.6.8 extractor wraps the v3.6.7 extractor with line-start
    backtracking so heading prefix bytes are in the hashed range.
    """
    from scripts.check_v3_6_8_pattern_protection import _extract_block_bytes
    h2_bytes_in = "prelude\n\n## PATTERN PROTECTION (v3.6.7)\n\nbody1\n".encode("utf-8")
    h3_bytes_in = "prelude\n\n### PATTERN PROTECTION (v3.6.7)\n\nbody1\n".encode("utf-8")
    h2_bytes = _extract_block_bytes(h2_bytes_in)
    h3_bytes = _extract_block_bytes(h3_bytes_in)
    assert h2_bytes is not None and h3_bytes is not None
    # The extractor must distinguish H2 vs H3 in its returned bytes.
    assert h2_bytes != h3_bytes, (
        "heading prefix must be inside the byte range; H2 vs H3 "
        "should produce different SHAs"
    )
    # And the prefix bytes must literally be present.
    assert h2_bytes.startswith(b"## PATTERN")
    assert h3_bytes.startswith(b"### PATTERN")


def test_prose_mention_does_not_truncate_block_range() -> None:
    """Round-10 codex P2 closure: not only must the START be heading-anchored
    (round-9 closure), the END must also come from an independent search
    after the heading line — not from the v3.6.7 legacy extractor's
    substring-anchored slice length.

    Scenario: prose mention BEFORE the heading mentions the marker. The
    pre-round-10 implementation took `block` from the v3.6.7 extractor
    (which used substring search, latching onto the prose mention), then
    used `len(block)` as the slice length from the heading position. That
    `len(block)` equalled "from prose to next heading", which (when added
    to the heading line_start) covered the WRONG byte range — could be
    truncated or could overshoot, depending on relative offsets.

    This test pins the correct behaviour: the extracted block bytes must
    be the bytes from the heading line through the next heading (or EOF),
    inclusive of the heading prefix, regardless of whether prose mentions
    appear earlier in the file.
    """
    from scripts.check_v3_6_8_pattern_protection import _extract_block_bytes
    text = (
        "## Two-Layer Citation Emission (v3.7.1)\n"
        "\n"
        "This relates to the existing PATTERN PROTECTION (v3.6.7) block.\n"
        "\n"
        "## PATTERN PROTECTION (v3.6.7)\n"
        "\n"
        "real block body line 1\n"
        "real block body line 2\n"
    ).encode("utf-8")
    block = _extract_block_bytes(text)
    assert block is not None
    # The block must START at the real heading line.
    assert block.startswith(b"## PATTERN PROTECTION (v3.6.7)\n"), (
        f"Round-10 anchor broken; block doesn't start at heading: {block!r}"
    )
    # The block must contain the FULL real body, not a truncated fragment.
    assert b"real block body line 1" in block
    assert b"real block body line 2" in block
    # And the prose paragraph from the v3.7.1 section must NOT be inside.
    assert b"This relates to" not in block
    assert b"Two-Layer Citation Emission" not in block


def test_prose_mention_of_marker_does_not_misanchor_extractor() -> None:
    """Round-9 codex P3 closure: anchor the marker search to a Markdown
    heading line, not a free substring.

    A v3.7.1 PR may legitimately add prose BEFORE the protected block that
    mentions `PATTERN PROTECTION (v3.6.7)` — e.g. in a "Two-Layer Citation
    Emission" section's introductory paragraph that explains how the new
    invariants relate to the v3.6.7 PATTERN PROTECTION block. The pre-
    round-9 substring search would have matched the prose mention first,
    hashed the wrong byte range, and false-failed CI on a valid edit.

    This test verifies that an extractor invocation against text containing
    a prose mention of the marker before the actual heading still returns
    the heading-anchored block.
    """
    from scripts.check_v3_6_8_pattern_protection import _extract_block_bytes
    text = (
        "## Two-Layer Citation Emission (v3.7.1)\n"
        "\n"
        "This section relates to the existing PATTERN PROTECTION (v3.6.7) "
        "block by extending its invariant set. Note that the prose mention "
        "above must NOT misanchor the v3.7.1 SHA gate's extractor.\n"
        "\n"
        "## PATTERN PROTECTION (v3.6.7)\n"
        "\n"
        "real block body\n"
    ).encode("utf-8")
    block = _extract_block_bytes(text)
    assert block is not None
    # The extracted block must START with the heading line, not the prose
    # mention. The prose mention had no `## ` prefix so the bytes would
    # differ obviously.
    assert block.startswith(b"## PATTERN PROTECTION (v3.6.7)\n"), (
        f"Extractor anchored on prose mention instead of heading; got: {block!r}"
    )
    assert b"real block body" in block
    assert b"This section relates to" not in block, (
        "Extractor swallowed prose; round-9 anchor regex broken"
    )


def test_extractor_strips_only_file_level_bom_not_block_level() -> None:
    """Round-8 codex P2 closure: spec § Step 0 says "the FILE's BOM (if any)
    is excluded". The exclusion is FILE-level (byte 0). A BOM inserted later
    in the file (e.g. immediately before `## PATTERN PROTECTION`) is a real
    content mutation and MUST stay in the hashed range so the gate detects it.
    """
    from scripts.check_v3_6_8_pattern_protection import _extract_block_bytes
    BOM = b"\xef\xbb\xbf"
    base = "prelude\n\n## PATTERN PROTECTION (v3.6.7)\n\nbody\n".encode("utf-8")
    # Variant A: BOM at file start. This is a file-level BOM; spec says strip.
    file_bom_in = BOM + base
    # Variant B: BOM right before the heading (mid-file). NOT spec-stripped.
    block_bom_in = (
        "prelude\n\n".encode("utf-8")
        + BOM
        + "## PATTERN PROTECTION (v3.6.7)\n\nbody\n".encode("utf-8")
    )
    base_block = _extract_block_bytes(base)
    file_bom_block = _extract_block_bytes(file_bom_in)
    block_bom_block = _extract_block_bytes(block_bom_in)
    assert base_block is not None
    # File-level BOM stripped → block bytes equal to base.
    assert file_bom_block == base_block, (
        "File-level BOM (byte 0) MUST be stripped per spec § Step 0; got: "
        f"file_bom_block={file_bom_block!r} vs base_block={base_block!r}"
    )
    # Block-level BOM NOT stripped → block bytes differ from base.
    assert block_bom_block != base_block, (
        "BOM inserted before the heading (mid-file) MUST stay in the hashed "
        "range so the gate catches it (round-8 codex P2 closure). "
        f"block_bom_block={block_bom_block!r} vs base_block={base_block!r}"
    )


def test_bom_before_heading_attack_caught_by_lint() -> None:
    """End-to-end mutation test for the round-8 BOM attack: insert U+FEFF
    immediately before the v3.6.7 heading on disk and verify the lint FAILS.

    Round-9 anchored the marker search to a Markdown heading line. After
    that change, a BOM injected directly before `## PATTERN PROTECTION`
    breaks the heading line's `^[ \\t]*#{1,3}[ \\t]+...` shape (the BOM
    bytes sit between the line start and the `#`), so the heading regex
    no longer matches. The lint then takes the "marker missing at PR
    HEAD" diagnostic path instead of "BYTE-EQUIVALENCE FAIL". Both are
    correct — the gate rejects the mutation either way. This test
    accepts either diagnostic.
    """
    BOM = b"\xef\xbb\xbf"
    with _Snapshot(TARGET_AGENT):
        original = TARGET_AGENT.read_bytes()
        marker = b"## PATTERN PROTECTION (v3.6.7)"
        idx = original.find(marker)
        assert idx >= 0, "fixture missing marker"
        mutated = original[:idx] + BOM + original[idx:]
        TARGET_AGENT.write_bytes(mutated)
        result = _run_lint()
        assert result.returncode == 1, (
            "BOM-before-heading mutation must be caught by the SHA gate "
            "(round-8 codex P2 closure)."
        )
        assert (
            "BYTE-EQUIVALENCE FAIL" in result.stdout
            or "marker missing at PR HEAD" in result.stdout
        ), f"Expected gate rejection; got: {result.stdout}"


def test_anti_self_baseline_guard_rejects_manifest_mutation_in_pr(monkeypatch) -> None:
    """Round-2 codex P2 closure: refuse to run on PRs that mutate the v3.6.7
    manifest, because `git log -1 -- manifest` would otherwise resolve to the
    PR's own commit and the SHA comparison would hash modified content against
    itself.

    The guard's BYTE-comparison backstop catches a worktree-level mutation
    (no commit needed). The round-4 history-scan layer catches the more
    subtle touch-and-revert pattern; that layer is exercised by the
    `test_anti_self_baseline_guard_history_scan_called` test below.

    GITHUB_BASE_REF is set explicitly so the guard exits the "advisory mode"
    branch (no PR base detectable → guard returns advisory pass). On
    GitHub `push` event runs, GITHUB_BASE_REF is unset and origin/HEAD
    resolution may fail; this test injects the env var so the guard's
    real reject path is exercised regardless of trigger event.
    """
    monkeypatch.setenv("GITHUB_BASE_REF", "main")
    with _Snapshot(V3_6_7_MANIFEST):
        text = V3_6_7_MANIFEST.read_text(encoding="utf-8")
        # Mutate `rationale_doc` so the byte-equivalence check fires while
        # leaving the schema valid (so the broken-schema branch isn't what
        # triggers the failure).
        mutated = text.replace(
            '"rationale_doc"',
            '"rationale_doc_mutated_for_test"',
            1,
        )
        assert mutated != text, "mutation fixture failed to apply"
        V3_6_7_MANIFEST.write_text(mutated, encoding="utf-8")

        result = _run_lint()
        assert result.returncode == 1, (
            "Guard MUST refuse to run when v3.6.7 manifest is modified in the "
            "PR (otherwise the SHA gate would self-baseline)."
        )
        assert "anti-self-baseline guard" in result.stdout
        # Worktree-mutation triggers the byte-mismatch backstop branch.
        assert (
            "manifest bytes differ" in result.stdout
            or "manifest touched by" in result.stdout
        ), f"Expected guard rejection; got: {result.stdout}"


def test_anti_self_baseline_guard_history_scan_called(monkeypatch) -> None:
    """Round-4 codex P2 closure: the guard MUST scan merge-base..HEAD for any
    commit touching the manifest, not just compare final bytes.

    The touch-and-revert attack: commit A modifies manifest + protected block,
    commit B reverts manifest only. Final bytes match base, but `git log -1`
    still resolves to commit B and `git show B:<protected>` returns modified
    content.

    Reproducing the attack in a unit test would require building a fake git
    history; instead, this test patches `_run_git` to inject a synthetic
    `git log merge-base..HEAD -- manifest` result and asserts the guard
    rejects when commits ARE listed (touch-and-revert simulation).

    GITHUB_BASE_REF is set so the guard's "no PR base detectable → advisory
    pass" branch is bypassed (matters on `push` event CI where the env var
    is normally absent).
    """
    monkeypatch.setenv("GITHUB_BASE_REF", "main")
    from scripts import check_v3_6_8_pattern_protection as mod

    real_run_git = mod._run_git
    fake_log_output = "abcdef1234567890" * 1  # one fake touching commit SHA

    def patched_run_git(args, cwd=None):
        # Intercept the merge-base..HEAD log query with the manifest path.
        if (
            len(args) >= 2
            and args[0] == "log"
            and any("v3_6_7_inversion_manifest.json" in a for a in args)
            and args[1] == "--format=%H"
        ):
            return 0, fake_log_output, ""
        return real_run_git(args, cwd=cwd) if cwd is not None else real_run_git(args)

    monkeypatch.setattr(mod, "_run_git", patched_run_git)
    # Call the guard directly (not via subprocess — monkeypatch wouldn't apply).
    ok, err = mod._v3_6_7_manifest_unchanged_in_pr()
    assert ok is False, "Guard must reject when history scan finds touching commits"
    assert err and "manifest touched by" in err
    assert "round-2 + round-4 codex P2 closure" in err


def test_v3_6_7_marker_removed_at_head_fails() -> None:
    """Removing the v3.6.7 marker line is a boundary violation; must hard-fail.

    This catches an attempt to evade the SHA gate by renaming the heading
    (which would make _extract_block return None at HEAD).
    """
    with _Snapshot(TARGET_AGENT):
        text = TARGET_AGENT.read_text(encoding="utf-8")
        # Replace marker text so the case-insensitive find returns -1.
        mutated = text.replace(PROTECTION_MARKER, "## (former pattern protection heading)")
        assert mutated != text, "test fixture failed to apply mutation"
        TARGET_AGENT.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1
        assert "marker missing at PR HEAD" in result.stdout


# ---------- Module-level smoke test for the SHA-normalization helpers ----------


def test_strip_file_bom_only_at_byte_zero() -> None:
    """File-level BOM stripping per spec § Step 0. Round-8 closure renamed
    `_normalize_bytes` → `_strip_file_bom` to make the file-level scope
    explicit (the old name was ambiguous about what it normalized).
    """
    from scripts.check_v3_6_8_pattern_protection import _strip_file_bom
    assert _strip_file_bom(b"\xef\xbb\xbfhello") == b"hello"
    assert _strip_file_bom(b"hello") == b"hello"
    # Multi-byte payloads with no BOM are passed through unchanged.
    assert _strip_file_bom(b"\xe4\xb8\xad\xe6\x96\x87") == b"\xe4\xb8\xad\xe6\x96\x87"
    # BOM appearing in the middle of input is NOT stripped — only byte 0.
    assert _strip_file_bom(b"hi\xef\xbb\xbfworld") == b"hi\xef\xbb\xbfworld"


def test_sha256_helper_matches_hashlib() -> None:
    import hashlib
    from scripts.check_v3_6_8_pattern_protection import _sha256
    assert _sha256(b"abc") == hashlib.sha256(b"abc").hexdigest()


# =============================================================================
# Step 3a — Two-Layer Citation Emission invariant tests (v3.7.1)
# =============================================================================
#
# Spec § Step 3a (line 439): the v3.7.1 lint enforces three invariants on the
# Two-Layer Citation Emission prompt block in each manifest-listed agent:
#   (i)   two-layer form regex on emitted citations in agent test fixtures
#   (ii)  absence of "finalizer / orchestrator / stage gate" prose inside the
#         Two-Layer Citation Emission prompt blocks
#   (iii) absence of any frontmatter-read instruction in those blocks
#
# Manifest after Step 3a populates:
#   - deep-research/agents/synthesis_agent.md
#   - academic-paper/agents/draft_writer_agent.md
#   - deep-research/agents/report_compiler_agent.md
#
# The block is added OUTSIDE the v3.6.7 PATTERN PROTECTION block (boundary
# rule), with no blank-line separator on EOF-terminating files (per the
# `test_appending_new_h2_directly_after_eof_newline_passes` contract).

TWO_LAYER_BLOCK_MARKER = "## Two-Layer Citation Emission (v3.7.1)"

STEP3A_AGENT_PATHS = [
    "deep-research/agents/synthesis_agent.md",
    "academic-paper/agents/draft_writer_agent.md",
    "deep-research/agents/report_compiler_agent.md",
]


def _agent_path(rel: str) -> Path:
    return REPO_ROOT / rel


def test_step3a_each_manifest_agent_carries_two_layer_block() -> None:
    """All three Step 3a manifest agents must carry the canonical block heading."""
    for rel in STEP3A_AGENT_PATHS:
        text = _agent_path(rel).read_text(encoding="utf-8")
        assert TWO_LAYER_BLOCK_MARKER in text, (
            f"{rel} missing '{TWO_LAYER_BLOCK_MARKER}' heading; Step 3a "
            f"requires every manifest-listed agent to carry the prompt block"
        )


def test_step3a_lint_passes_on_clean_tree() -> None:
    """Clean tree (after Step 3a populates) → lint passes invariants AND SHA gate."""
    result = _run_lint()
    assert result.returncode == 0, (
        f"Step 3a invariants must pass on clean tree.\n"
        f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
    )
    # Both layers exercised: SHA gate (existing) + Step 3a invariants (new).
    assert "PASSED" in result.stdout
    # Step 3a lint must report each manifest file by name.
    for rel in STEP3A_AGENT_PATHS:
        agent_basename = Path(rel).name
        assert agent_basename in result.stdout, (
            f"Step 3a lint output must mention {agent_basename}; got:\n{result.stdout}"
        )


def test_step3a_v3_6_8_manifest_lists_three_agents() -> None:
    """v3.6.8 inversion manifest 'files' list must populate with the 3 agent paths."""
    data = json.loads(V3_6_8_MANIFEST.read_text(encoding="utf-8"))
    assert data["scope"] == "v3.6.8-only"
    files = data["files"]
    for rel in STEP3A_AGENT_PATHS:
        assert rel in files, (
            f"v3.6.8 manifest 'files' must contain {rel} after Step 3a populates"
        )


def test_step3a_invariant_i_two_layer_form_required() -> None:
    """Invariant (i): block must specify the two-layer form including the
    `<!--ref:slug-->` HTML comment and `<author-year>` visible form.

    Removing the `<!--ref:` token from the block must make the lint fail.
    """
    target = _agent_path("deep-research/agents/synthesis_agent.md")
    with _Snapshot(target):
        text = target.read_text(encoding="utf-8")
        # Replace every `<!--ref:` literal inside the block scope with a
        # placeholder that doesn't carry the two-layer form contract.
        # Find block scope first so we don't accidentally mutate prose
        # outside the block.
        block_pos = text.find(TWO_LAYER_BLOCK_MARKER)
        assert block_pos != -1, "fixture missing two-layer block (test vacuous)"
        # Block ends at next H1/H2/H3 or EOF.
        import re as _re
        next_h_re = _re.compile(r"(?m)^[ \t]*#{1,3}[ \t]+")
        next_h = next_h_re.search(text, block_pos + len(TWO_LAYER_BLOCK_MARKER))
        block_end = next_h.start() if next_h else len(text)
        block_scope = text[block_pos:block_end]
        # Mutate: drop every `<!--ref:` literal in the block.
        mutated_scope = block_scope.replace("<!--ref:", "<!--XXXX:")
        assert mutated_scope != block_scope, (
            "block must contain at least one `<!--ref:` literal (invariant i)"
        )
        target.write_text(text[:block_pos] + mutated_scope + text[block_end:], encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            "Removing `<!--ref:` from the block must trigger invariant (i) "
            f"failure; got rc={result.returncode}\nstdout:\n{result.stdout}"
        )
        assert "two-layer" in result.stdout.lower() or "<!--ref:" in result.stdout


def _inject_into_block_body(target: Path, injection: str) -> None:
    """Inject `injection` into the body of the Two-Layer block (after the
    heading line), not into the heading line itself.

    R2 P2 closure tightened the canonical-heading regex to require a clean
    EOL anchor; mutations that appended text on the heading line caused the
    heading to no longer match the canonical form (so the block was reported
    "missing" instead of the intended "invariant violated"). This helper
    targets the BODY of the block, which is the right place for the
    invariant-ii / -iii mutations.
    """
    text = target.read_text(encoding="utf-8")
    block_pos = text.find(TWO_LAYER_BLOCK_MARKER)
    assert block_pos != -1, (
        f"fixture missing two-layer block in {target.name}"
    )
    eol = text.index("\n", block_pos)
    target.write_text(text[: eol + 1] + injection + text[eol + 1:], encoding="utf-8")


def test_step3a_invariant_ii_finalizer_mention_forbidden() -> None:
    """Invariant (ii): block body must NOT mention 'finalizer'.

    Inserting the word 'finalizer' inside the block body (not the heading
    line) must make the lint fail (strict partial-inversion: agent must
    not know about the resolver layer).
    """
    target = _agent_path("deep-research/agents/synthesis_agent.md")
    with _Snapshot(target):
        _inject_into_block_body(
            target,
            "\nThe finalizer will resolve these markers downstream.\n",
        )
        result = _run_lint()
        assert result.returncode == 1, (
            "Inserting 'finalizer' inside the block must trigger invariant "
            f"(ii) failure; got rc={result.returncode}\nstdout:\n{result.stdout}"
        )
        assert "finalizer" in result.stdout.lower() or "partial-inversion" in result.stdout.lower()


def test_step3a_invariant_ii_orchestrator_mention_forbidden() -> None:
    """Invariant (ii): block body must NOT mention 'orchestrator'."""
    target = _agent_path("academic-paper/agents/draft_writer_agent.md")
    with _Snapshot(target):
        _inject_into_block_body(
            target,
            "\nThe orchestrator dispatches the next stage of the pipeline.\n",
        )
        result = _run_lint()
        assert result.returncode == 1
        assert "orchestrator" in result.stdout.lower() or "partial-inversion" in result.stdout.lower()


def test_step3a_invariant_ii_stage_gate_mention_forbidden() -> None:
    """Invariant (ii): block body must NOT mention 'stage gate'."""
    target = _agent_path("deep-research/agents/report_compiler_agent.md")
    with _Snapshot(target):
        _inject_into_block_body(
            target,
            "\nThe stage gate inspects this output before publication.\n",
        )
        result = _run_lint()
        assert result.returncode == 1
        assert "stage gate" in result.stdout.lower() or "partial-inversion" in result.stdout.lower()


def test_step3a_invariant_iii_frontmatter_read_instruction_forbidden() -> None:
    """Invariant (iii): block must NOT instruct the agent to read frontmatter."""
    target = _agent_path("deep-research/agents/synthesis_agent.md")
    with _Snapshot(target):
        text = target.read_text(encoding="utf-8")
        block_pos = text.find(TWO_LAYER_BLOCK_MARKER)
        assert block_pos != -1
        nl = text.index("\n", block_pos)
        # Insert a frontmatter-read instruction.
        mutated = (
            text[: nl]
            + "\n\nBefore emitting, read the entry frontmatter to look up the slug.\n"
            + text[nl:]
        )
        target.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            "A frontmatter-read instruction inside the block must trigger "
            f"invariant (iii) failure; got rc={result.returncode}\nstdout:\n{result.stdout}"
        )
        assert "frontmatter" in result.stdout.lower()


def test_step3a_block_missing_from_manifest_agent_fails() -> None:
    """Removing the entire block from a manifest-listed agent → lint fails.

    Mutates synthesis_agent by replacing the block heading with a non-marker
    heading; lint must report block absence for that file.
    """
    target = _agent_path("deep-research/agents/synthesis_agent.md")
    with _Snapshot(target):
        text = target.read_text(encoding="utf-8")
        assert TWO_LAYER_BLOCK_MARKER in text
        # Replace marker so the block cannot be located.
        mutated = text.replace(
            TWO_LAYER_BLOCK_MARKER,
            "## (former two-layer block heading)",
            1,
        )
        target.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            "Block absence from manifest agent must hard-fail; "
            f"got rc={result.returncode}\nstdout:\n{result.stdout}"
        )
        assert "Two-Layer Citation Emission" in result.stdout or "block missing" in result.stdout.lower()


def test_step3a_invariant_iii_unrelated_negation_does_not_bless_read_instruction() -> None:
    """R1 P1-2 closure: a negation token elsewhere in the same sentence must
    NOT bless a positive frontmatter-read instruction.

    Pre-R1 negation rule: any negation in the sentence → pass.
    Post-R1 rule: negation must be within ≤30 chars BEFORE the read verb.

    Mutation: insert a sentence like "Never guess; read the entry frontmatter
    to find the slug" — a sloppy negation that would have slipped past R0.
    """
    target = _agent_path("deep-research/agents/synthesis_agent.md")
    with _Snapshot(target):
        text = target.read_text(encoding="utf-8")
        block_pos = text.find(TWO_LAYER_BLOCK_MARKER)
        assert block_pos != -1
        nl = text.index("\n", block_pos)
        # The "Never" applies to "guess", not to "read frontmatter". Pre-R1
        # this slipped past; post-R1 it must FAIL invariant (iii).
        injection = (
            "\n\nNever guess. Always read the entry frontmatter "
            "to find the slug.\n"
        )
        mutated = text[: nl] + injection + text[nl:]
        target.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            "R1 P1-2: a sentence with unrelated negation must NOT bless a "
            f"positive read-frontmatter instruction; got rc={result.returncode}\n"
            f"stdout:\n{result.stdout}"
        )
        assert "frontmatter" in result.stdout.lower()


def test_step3a_invariant_iii_front_matter_two_word_variant_caught() -> None:
    """R1 P1-3 closure: `front matter` (two-word) variant must be caught."""
    target = _agent_path("deep-research/agents/synthesis_agent.md")
    with _Snapshot(target):
        text = target.read_text(encoding="utf-8")
        block_pos = text.find(TWO_LAYER_BLOCK_MARKER)
        assert block_pos != -1
        nl = text.index("\n", block_pos)
        injection = "\n\nIf needed, read the entry's front matter for the slug.\n"
        mutated = text[: nl] + injection + text[nl:]
        target.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            "R1 P1-3: `front matter` (two-word) variant must be caught"
        )
        assert "front" in result.stdout.lower()


def test_step3a_invariant_iii_front_dash_matter_variant_caught() -> None:
    """R1 P1-3 closure: `front-matter` (hyphenated) variant must be caught."""
    target = _agent_path("academic-paper/agents/draft_writer_agent.md")
    with _Snapshot(target):
        text = target.read_text(encoding="utf-8")
        block_pos = text.find(TWO_LAYER_BLOCK_MARKER)
        assert block_pos != -1
        nl = text.index("\n", block_pos)
        injection = "\n\nIf needed, read the entry's front-matter for the slug.\n"
        mutated = text[: nl] + injection + text[nl:]
        target.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            "R1 P1-3: `front-matter` (hyphenated) variant must be caught"
        )


def test_step3a_invariant_iii_wrapped_read_instruction_caught() -> None:
    """R1 P1-3 closure: `read the entry\\nfrontmatter` (line-wrapped) must be caught."""
    target = _agent_path("deep-research/agents/report_compiler_agent.md")
    with _Snapshot(target):
        text = target.read_text(encoding="utf-8")
        block_pos = text.find(TWO_LAYER_BLOCK_MARKER)
        assert block_pos != -1
        nl = text.index("\n", block_pos)
        # A bullet that wraps the read verb away from the target.
        injection = "\n\n- read the entry's full\n  frontmatter to find the slug\n"
        mutated = text[: nl] + injection + text[nl:]
        target.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            "R1 P1-3: line-wrapped read-frontmatter instruction must be caught"
        )


def test_step3a_invariant_iii_canonical_negation_still_passes() -> None:
    """R1 P1-2 sanity: the canonical `NEVER read the entry frontmatter`
    prohibition (the actual block prose) must continue to pass invariant (iii).

    This is the explicit happy-path test for the negation rule; before R1 it
    was implicit in `test_step3a_lint_passes_on_clean_tree`.
    """
    # No mutation — just verify clean tree passes.
    result = _run_lint()
    assert result.returncode == 0, (
        f"Canonical 'NEVER read the entry frontmatter' must pass invariant "
        f"(iii); got rc={result.returncode}\nstdout:\n{result.stdout}"
    )


def test_step3a_duplicate_block_rejected() -> None:
    """R1 P2 closure: a manifest agent file with two canonical Two-Layer
    block headings must FAIL the lint."""
    target = _agent_path("deep-research/agents/synthesis_agent.md")
    with _Snapshot(target):
        text = target.read_text(encoding="utf-8")
        # Append a second canonical heading at EOF.
        duplicate = (
            "\n## Two-Layer Citation Emission (v3.7.1)\n\n"
            "duplicate body — this should be caught\n"
        )
        target.write_text(text + duplicate, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            "R1 P2: duplicate canonical Two-Layer Citation Emission heading "
            "must be rejected"
        )
        assert "exactly one" in result.stdout.lower() or "duplicate" in result.stdout.lower() or "headings found" in result.stdout.lower()


def test_step3a_invariant_iii_bullet_boundary_is_clause_terminator() -> None:
    """R2 P1-A closure: a `\\n- ` bullet boundary must act as a clause
    terminator so `NEVER` in the previous bullet does not bless a positive
    `read frontmatter` instruction in the next bullet.

    Pre-R2: bullets were not terminators; `- NEVER omit markers\\n- read the
    entry frontmatter` slipped past because `NEVER` sat in the 30-char
    left window.
    """
    target = _agent_path("deep-research/agents/synthesis_agent.md")
    with _Snapshot(target):
        text = target.read_text(encoding="utf-8")
        block_pos = text.find(TWO_LAYER_BLOCK_MARKER)
        assert block_pos != -1
        nl = text.index("\n", block_pos)
        # Two adjacent bullets, no period, `NEVER` in bullet 1 leaks into
        # bullet 2's left window pre-R2 (≤30 chars from `read`).
        injection = (
            "\n\n- NEVER skip\n"
            "- read the entry frontmatter to find the slug\n"
        )
        mutated = text[: nl] + injection + text[nl:]
        target.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            "R2 P1-A: bullet boundary must terminate the negation window; "
            "got rc=" + str(result.returncode) + "\nstdout:\n" + result.stdout
        )


def test_step3a_invariant_ii_finalizer_agent_substring_caught() -> None:
    """R2 P1-B closure: `cite_provenance_finalizer_agent` must be caught.

    Python `\\b` treats `_` as a word char, so `\\bfinalizer\\b` does NOT
    match the agent identifier introduced by Step 3c. R2 switches to
    identifier-aware boundaries `(?<![A-Za-z0-9])` / `(?![A-Za-z0-9])`
    which DO treat `_` as a word boundary, catching this attack surface.
    """
    target = _agent_path("deep-research/agents/synthesis_agent.md")
    with _Snapshot(target):
        text = target.read_text(encoding="utf-8")
        block_pos = text.find(TWO_LAYER_BLOCK_MARKER)
        assert block_pos != -1
        nl = text.index("\n", block_pos)
        injection = (
            "\n\nThe markers are consumed by cite_provenance_finalizer_agent "
            "downstream.\n"
        )
        mutated = text[: nl] + injection + text[nl:]
        target.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            "R2 P1-B: `cite_provenance_finalizer_agent` must be flagged "
            "(identifier-aware boundary, underscore as boundary)"
        )
        assert "finalizer" in result.stdout.lower() or "partial-inversion" in result.stdout.lower()


def test_step3a_invariant_ii_terminal_gate_agent_substring_caught() -> None:
    """R2 P1-B closure: `cite_provenance_terminal_gate_agent` must be caught."""
    target = _agent_path("academic-paper/agents/draft_writer_agent.md")
    with _Snapshot(target):
        text = target.read_text(encoding="utf-8")
        block_pos = text.find(TWO_LAYER_BLOCK_MARKER)
        assert block_pos != -1
        nl = text.index("\n", block_pos)
        injection = (
            "\n\nThe `cite_provenance_terminal_gate_agent` will inspect "
            "this output before publication.\n"
        )
        mutated = text[: nl] + injection + text[nl:]
        target.write_text(mutated, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            "R2 P1-B: `cite_provenance_terminal_gate_agent` must be flagged"
        )


def test_step3a_h3_same_title_duplicate_rejected() -> None:
    """R2 P2 closure: an H3 same-title heading is a duplicate and must
    be rejected. Pre-R2 this slipped past because `_extract_two_layer_block`
    stops at H3 headings (the H3 same-title sat outside the canonical block
    scan range and could carry contradictory instructions).
    """
    target = _agent_path("deep-research/agents/report_compiler_agent.md")
    with _Snapshot(target):
        text = target.read_text(encoding="utf-8")
        # Append an H3 same-title heading at EOF.
        duplicate_h3 = (
            "\n### Two-Layer Citation Emission (v3.7.1)\n\n"
            "duplicate body — H3 typo or attack\n"
        )
        target.write_text(text + duplicate_h3, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            "R2 P2: H3 same-title heading must be rejected as a duplicate"
        )
        assert (
            "headings found" in result.stdout.lower()
            or "exactly one" in result.stdout.lower()
        )


def test_step3a_invariant_ii_plural_finalizers_caught() -> None:
    """R3 P1-B closure: `finalizers` (plural) must be caught."""
    target = _agent_path("deep-research/agents/synthesis_agent.md")
    with _Snapshot(target):
        _inject_into_block_body(
            target,
            "\nThe finalizers will resolve markers downstream.\n",
        )
        result = _run_lint()
        assert result.returncode == 1
        assert "finalizer" in result.stdout.lower() or "partial-inversion" in result.stdout.lower()


def test_step3a_invariant_ii_plural_orchestrators_caught() -> None:
    """R3 P1-B closure: `orchestrators` (plural) must be caught."""
    target = _agent_path("academic-paper/agents/draft_writer_agent.md")
    with _Snapshot(target):
        _inject_into_block_body(
            target,
            "\nMultiple orchestrators dispatch the next stage.\n",
        )
        result = _run_lint()
        assert result.returncode == 1


def test_step3a_invariant_ii_plural_resolvers_caught() -> None:
    """R3 P1-B closure: `resolvers` (plural) must be caught."""
    target = _agent_path("deep-research/agents/report_compiler_agent.md")
    with _Snapshot(target):
        _inject_into_block_body(
            target,
            "\nThe resolvers process this output.\n",
        )
        result = _run_lint()
        assert result.returncode == 1


def test_step3a_invariant_iii_function_call_read_frontmatter_caught() -> None:
    """R3 P1-C closure: `read_frontmatter()` function-style call must be caught.

    Python `\\b` treats `_` as a word char, so the bare `\\bread\\b` regex
    did NOT match `read_frontmatter` (one token). R3 switches to
    identifier-aware boundaries so `_` IS a boundary; the function name
    is now caught.
    """
    target = _agent_path("deep-research/agents/synthesis_agent.md")
    with _Snapshot(target):
        _inject_into_block_body(
            target,
            "\nCall read_frontmatter() to discover the slug.\n",
        )
        result = _run_lint()
        assert result.returncode == 1, (
            "R3 P1-C: function-style `read_frontmatter()` must be flagged "
            f"under invariant (iii); got rc={result.returncode}\n"
            f"stdout:\n{result.stdout}"
        )
        assert "frontmatter" in result.stdout.lower() or "front" in result.stdout.lower()


def test_step3a_heading_drift_with_trailing_text_rejected() -> None:
    """R3 P1-A closure: a heading with trailing text after the canonical
    title must be rejected as drift duplicate.

    Pre-R3, `### Two-Layer Citation Emission (v3.7.1) — extended` slipped
    past because:
    1. The exact-title regex required `[ \\t]*$` EOL, so this drift
       heading was NOT counted as a duplicate.
    2. `_extract_two_layer_block` stops at the next H1/H2/H3, so the H3
       drift heading sat OUTSIDE the canonical block range and any
       forbidden text under it was invisible to per-block invariants.

    R3 introduces a drift detector that catches headings whose title
    BEGINS with the canonical title but has trailing non-whitespace.
    """
    target = _agent_path("academic-paper/agents/draft_writer_agent.md")
    with _Snapshot(target):
        text = target.read_text(encoding="utf-8")
        drift_block = (
            "\n### Two-Layer Citation Emission (v3.7.1) — extended\n\n"
            "The finalizer will resolve markers.\n"
        )
        target.write_text(text + drift_block, encoding="utf-8")
        result = _run_lint()
        assert result.returncode == 1, (
            "R3 P1-A: heading drift `### Two-Layer ... — extended` must be "
            f"rejected as duplicate-by-drift; got rc={result.returncode}\n"
            f"stdout:\n{result.stdout}"
        )
        assert "drift" in result.stdout.lower() or "duplicate" in result.stdout.lower()


def test_step3a_block_addition_does_not_break_v3_6_7_sha_gate() -> None:
    """Defense-in-depth: with Two-Layer Citation Emission blocks present in
    all three v3.6.7-protected files, the SHA gate must still pass.

    This is the existing `test_happy_path_passes_on_clean_tree` invariant
    re-asserted under the post-Step-3a tree (the SHA gate hashes only the
    v3.6.7 PATTERN PROTECTION block, not the appended Step 3a block).
    """
    result = _run_lint()
    assert result.returncode == 0
    # SHA gate must still report all 3 v3.6.7 files passing.
    assert "[v3.7.1 SHA gate] PASSED" in result.stdout
