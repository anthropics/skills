"""Unit tests for check_v3_6_7_pattern_protection.py (ARS v3.6.7 lint).

Mutation evidence preserved from codex review rounds R3-R5 (B2 phase). Each
test mutates a v3.6.7 PATTERN PROTECTION clause in a temporary copy of the
repo and asserts the lint flags it. This guards against future regressions
in the lint contract — without these tests, CI would only verify that the
*current* prompt prose passes, but a checker regression that silently
accepts weakened obligations would be caught only by ad-hoc mutation runs.

The test suite operates on a sandboxed copy of the repo: each test
constructs the copy via `git archive HEAD | tar -x`, applies a single
mutation, and runs `scripts/check_v3_6_7_pattern_protection.py` against
that copy. The repo's actual files are never modified.
"""
from __future__ import annotations

import subprocess
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
LINT_SCRIPT_REL = "scripts/check_v3_6_7_pattern_protection.py"


def _archive_repo(dest: Path) -> None:
    """Materialise current `HEAD` into `dest` via git archive | tar."""
    archive = subprocess.Popen(
        ["git", "archive", "HEAD"], cwd=REPO_ROOT, stdout=subprocess.PIPE
    )
    try:
        subprocess.run(
            ["tar", "-x", "-C", str(dest)], stdin=archive.stdout, check=True
        )
    finally:
        if archive.stdout is not None:
            archive.stdout.close()
        archive.wait()
    if archive.returncode != 0:
        raise RuntimeError(f"git archive failed: rc={archive.returncode}")


def _run_lint(repo_dir: Path) -> tuple[int, str, str]:
    """Run the v3.6.7 lint inside `repo_dir`. Returns (rc, stdout, stderr)."""
    proc = subprocess.run(
        ["python3", LINT_SCRIPT_REL],
        cwd=repo_dir,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    return proc.returncode, proc.stdout, proc.stderr


def _mutate(repo_dir: Path, rel_path: str, old: str, new: str) -> None:
    """Apply a single replace mutation to `repo_dir/rel_path`. Asserts the
    `old` string is present (so a refactored prompt that no longer matches
    surfaces as a clear test failure rather than silently-no-op)."""
    path = repo_dir / rel_path
    text = path.read_text(encoding="utf-8")
    if old not in text:
        raise AssertionError(
            f"Mutation source string not found in {rel_path}: "
            f"{old[:80]!r}..."
        )
    path.write_text(text.replace(old, new, 1), encoding="utf-8")


class _MutationTestBase(unittest.TestCase):
    """Each test materialises a fresh repo copy under self._repo_dir."""

    def setUp(self) -> None:
        self._tmpdir = tempfile.TemporaryDirectory(prefix="ars-v367-test.")
        self._repo_dir = Path(self._tmpdir.name)
        _archive_repo(self._repo_dir)

    def tearDown(self) -> None:
        self._tmpdir.cleanup()

    def assert_baseline_passes(self) -> None:
        rc, _stdout, stderr = _run_lint(self._repo_dir)
        self.assertEqual(rc, 0, f"baseline lint should pass; stderr={stderr}")

    def assert_mutation_fails(self) -> None:
        rc, _stdout, _stderr = _run_lint(self._repo_dir)
        self.assertNotEqual(rc, 0, "mutation should make lint fail")


class BaselineTest(_MutationTestBase):
    def test_unmutated_repo_passes(self) -> None:
        self.assert_baseline_passes()


class R2MutationTests(_MutationTestBase):
    """R2-001 closure: per-regex allow_prohibition stops C3's `must not`
    exemption from leaking into C1's assertion-style obligation."""

    def test_c1_inverted_must_not_preserve_fails(self) -> None:
        _mutate(
            self._repo_dir,
            "deep-research/agents/report_compiler_agent.md",
            "Compression must preserve protected hedging phrases",
            "Compression must not preserve protected hedging phrases",
        )
        self.assert_mutation_fails()

    def test_c3_audit_passed_sentence_deleted_fails(self) -> None:
        # Phase 6.7 merged line 178 into the canonical Clause 1 line
        # bullet. The "audit-passed state" segment is now part of a single
        # whole-line bullet, so the mutation deletes that segment from
        # within the canonical line and asserts the now-incomplete bullet
        # fails the C3 + INV-1 regex pair.
        _mutate(
            self._repo_dir,
            "deep-research/agents/report_compiler_agent.md",
            " Output metadata must not claim audit-passed state.",
            "",
        )
        self.assert_mutation_fails()


class R3MutationTests(_MutationTestBase):
    """R3-001 (span-restricted prohibition exemption), R3-002 (token →
    regex), R3-003 (except/unless weakeners)."""

    def test_r3_001_trailing_must_not_be_enforced_fails(self) -> None:
        _mutate(
            self._repo_dir,
            "deep-research/agents/report_compiler_agent.md",
            "Output metadata must not claim audit-passed state.",
            "Output metadata must not claim audit-passed state; this must not be enforced.",
        )
        self.assert_mutation_fails()

    def test_r3_002_a2_pending_verification_optional_fails(self) -> None:
        _mutate(
            self._repo_dir,
            "deep-research/agents/synthesis_agent.md",
            'wrap claims in explicit hedge ("pending verification of X" / "inferred from upstream Y").',
            "pending verification language is optional; claims may be written as facts.",
        )
        self.assert_mutation_fails()

    def test_r3_002_c2_may_use_year_range_fails(self) -> None:
        _mutate(
            self._repo_dir,
            "deep-research/agents/report_compiler_agent.md",
            'Reflexivity disclosure must use explicit temporal bounds: explicit year range, past-tense disambiguating verb, or "former" prefix. Deictic temporal phrases ("during this period" / "at the time") are forbidden.',
            'Reflexivity disclosure may use an explicit year range, but deictic temporal phrases ("during this period" / "at the time") are allowed when shorter.',
        )
        self.assert_mutation_fails()

    def test_r3_003_no_subsetting_except_when_concise_fails(self) -> None:
        _mutate(
            self._repo_dir,
            "deep-research/agents/research_architect_agent.md",
            "No subsetting, no over-setting, no scope cross-contamination.",
            "No subsetting except when concise, no over-setting, no scope cross-contamination.",
        )
        self.assert_mutation_fails()


class R4MutationTests(_MutationTestBase):
    """R4-001 (modal verb scope), R4-002 (sub-clause coverage)."""

    def test_r4_001_a2_may_wrap_fails(self) -> None:
        _mutate(
            self._repo_dir,
            "deep-research/agents/synthesis_agent.md",
            'For any source flagged "pending verification" upstream: wrap claims in explicit hedge',
            'For any source flagged "pending verification" upstream: may wrap claims in explicit hedge',
        )
        self.assert_mutation_fails()

    def test_r4_001_a3_may_include_fails(self) -> None:
        _mutate(
            self._repo_dir,
            "deep-research/agents/synthesis_agent.md",
            "For each substantive claim: include a one-line anchor justification.",
            "For each substantive claim: may include a one-line anchor justification.",
        )
        self.assert_mutation_fails()

    def test_r4_001_a1_recommended_fails(self) -> None:
        _mutate(
            self._repo_dir,
            "deep-research/agents/synthesis_agent.md",
            "pre-list the source's effect inventory and run a cross-section consistency self-check before output.",
            "pre-list the source's effect inventory and cross-section consistency self-check are recommended before output.",
        )
        self.assert_mutation_fails()

    def test_r4_002_a4_may_be_quoted_fails(self) -> None:
        _mutate(
            self._repo_dir,
            "deep-research/agents/synthesis_agent.md",
            "surrounding context paraphrased and unquoted.",
            "surrounding context may be quoted.",
        )
        self.assert_mutation_fails()

    def test_r4_002_a5_drop_conditional_fails(self) -> None:
        _mutate(
            self._repo_dir,
            "deep-research/agents/synthesis_agent.md",
            'use conditional language ("if document X argues Y, this chapter could dialogue by Z") or explicit gap acknowledgment. Declarative claims about un-provided documents are forbidden.',
            "Declarative claims about un-provided documents are forbidden.",
        )
        self.assert_mutation_fails()

    def test_r4_002_b4_allow_chapter_vocab_fails(self) -> None:
        _mutate(
            self._repo_dir,
            "deep-research/agents/research_architect_agent.md",
            "Item phrasing must be neutral/balanced. Chapter argument vocabulary is forbidden in instrument items.",
            "Item phrasing may use chapter argument vocabulary in instrument items.",
        )
        self.assert_mutation_fails()

    def test_r4_002_b5_allow_overset_fails(self) -> None:
        _mutate(
            self._repo_dir,
            "deep-research/agents/research_architect_agent.md",
            "No subsetting, no over-setting, no scope cross-contamination.",
            "No subsetting. Over-setting and scope cross-contamination are allowed.",
        )
        self.assert_mutation_fails()

    def test_r4_002_c1_drop_buffer_fails(self) -> None:
        _mutate(
            self._repo_dir,
            "deep-research/agents/report_compiler_agent.md",
            "Word budget uses whitespace-split convention (`body.split()`), not hyphenated-as-1. Reserve 3–5% buffer below hard cap.",
            "Word budget uses whitespace-split convention (`body.split()`), not hyphenated-as-1.",
        )
        self.assert_mutation_fails()

    def test_r4_002_c2_drop_past_tense_form_fails(self) -> None:
        _mutate(
            self._repo_dir,
            "deep-research/agents/report_compiler_agent.md",
            'Reflexivity disclosure must use explicit temporal bounds: explicit year range, past-tense disambiguating verb, or "former" prefix.',
            "Reflexivity disclosure must use explicit temporal bounds: explicit year range.",
        )
        self.assert_mutation_fails()


class R5MutationTests(_MutationTestBase):
    """R5-001 (advisory weakeners: should/can/permitted)."""

    def test_r5_001_a2_should_wrap_fails(self) -> None:
        _mutate(
            self._repo_dir,
            "deep-research/agents/synthesis_agent.md",
            'For any source flagged "pending verification" upstream: wrap claims in explicit hedge',
            'For any source flagged "pending verification" upstream: should wrap claims in explicit hedge',
        )
        self.assert_mutation_fails()

    def test_r5_001_a3_should_include_fails(self) -> None:
        _mutate(
            self._repo_dir,
            "deep-research/agents/synthesis_agent.md",
            "For each substantive claim: include a one-line anchor justification.",
            "For each substantive claim: should include a one-line anchor justification.",
        )
        self.assert_mutation_fails()

    def test_r5_001_a4_can_be_quoted_tail_fails(self) -> None:
        _mutate(
            self._repo_dir,
            "deep-research/agents/synthesis_agent.md",
            "surrounding context paraphrased and unquoted.",
            "surrounding context paraphrased and unquoted, but can be quoted for flow.",
        )
        self.assert_mutation_fails()

    def test_r5_001_b5_overset_permitted_fails(self) -> None:
        _mutate(
            self._repo_dir,
            "deep-research/agents/research_architect_agent.md",
            "No subsetting, no over-setting, no scope cross-contamination.",
            "No subsetting, no scope cross-contamination; over-setting is permitted when concise.",
        )
        self.assert_mutation_fails()

    def test_r5_001_b5_should_declare_fails(self) -> None:
        _mutate(
            self._repo_dir,
            "deep-research/agents/research_architect_agent.md",
            "Any list-of-options item must declare its primary-source list and enumerate fully.",
            "Any list-of-options item should declare its primary-source list and enumerate fully.",
        )
        self.assert_mutation_fails()

    def test_r5_001_c1_should_preserve_fails(self) -> None:
        _mutate(
            self._repo_dir,
            "deep-research/agents/report_compiler_agent.md",
            "Compression must preserve protected hedging phrases identified by upstream calibration as budget-protected (the dispatch context carries the list).",
            "Compression should preserve protected hedging phrases identified by upstream calibration as budget-protected (the dispatch context carries the list).",
        )
        self.assert_mutation_fails()


class R6MutationTests(_MutationTestBase):
    """R6-001 (future/conditional modals + advisory adverb weakeners)."""

    def test_r6_001_c1_will_not_preserve_fails(self) -> None:
        _mutate(
            self._repo_dir,
            "deep-research/agents/report_compiler_agent.md",
            "Compression must preserve protected hedging phrases",
            "Compression will not preserve protected hedging phrases",
        )
        self.assert_mutation_fails()

    def test_r6_001_c1_would_preserve_fails(self) -> None:
        _mutate(
            self._repo_dir,
            "deep-research/agents/report_compiler_agent.md",
            "Compression must preserve protected hedging phrases",
            "Compression would preserve protected hedging phrases",
        )
        self.assert_mutation_fails()

    def test_r6_001_a2_ought_to_wrap_fails(self) -> None:
        _mutate(
            self._repo_dir,
            "deep-research/agents/synthesis_agent.md",
            'For any source flagged "pending verification" upstream: wrap claims in explicit hedge',
            'For any source flagged "pending verification" upstream: ought to wrap claims in explicit hedge',
        )
        self.assert_mutation_fails()

    def test_r6_001_a3_ideally_include_fails(self) -> None:
        _mutate(
            self._repo_dir,
            "deep-research/agents/synthesis_agent.md",
            "For each substantive claim: include a one-line anchor justification.",
            "For each substantive claim: ideally include a one-line anchor justification.",
        )
        self.assert_mutation_fails()

    def test_r6_001_b5_preferably_enumerate_fails(self) -> None:
        _mutate(
            self._repo_dir,
            "deep-research/agents/research_architect_agent.md",
            "Any list-of-options item must declare its primary-source list and enumerate fully.",
            "Any list-of-options item must declare its primary-source list and preferably enumerate fully.",
        )
        self.assert_mutation_fails()

    def test_r6_001_a3_we_recommend_that_fails(self) -> None:
        _mutate(
            self._repo_dir,
            "deep-research/agents/synthesis_agent.md",
            "For each substantive claim: include a one-line anchor justification.",
            "We recommend that each substantive claim include a one-line anchor justification.",
        )
        self.assert_mutation_fails()


class INV1MutationTests(_MutationTestBase):
    """INV-1 (Phase 6.7 §6.3): canonical Clause 1 line MUST appear exactly
    once in each manifest file's PATTERN PROTECTION block. Deleting the
    line, duplicating it, or replacing it with a near-miss MUST fail lint."""

    CANONICAL_BULLET = (
        "- DO NOT simulate any audit step. DO NOT claim to have run "
        "codex/external review. Output metadata must not claim audit-passed "
        "state."
    )

    def test_inv1_synthesis_canonical_line_deleted_fails(self) -> None:
        _mutate(
            self._repo_dir,
            "deep-research/agents/synthesis_agent.md",
            "\n" + self.CANONICAL_BULLET,
            "",
        )
        self.assert_mutation_fails()

    def test_inv1_architect_canonical_line_deleted_fails(self) -> None:
        _mutate(
            self._repo_dir,
            "deep-research/agents/research_architect_agent.md",
            "\n" + self.CANONICAL_BULLET,
            "",
        )
        self.assert_mutation_fails()

    def test_inv1_compiler_canonical_line_deleted_fails(self) -> None:
        _mutate(
            self._repo_dir,
            "deep-research/agents/report_compiler_agent.md",
            "\n" + self.CANONICAL_BULLET,
            "",
        )
        self.assert_mutation_fails()

    def test_inv1_synthesis_canonical_line_duplicated_fails(self) -> None:
        # Duplicating the bullet trips INV-1 uniqueness (`hits == 1`)
        # without breaking the per-file C-style positive regex.
        _mutate(
            self._repo_dir,
            "deep-research/agents/synthesis_agent.md",
            self.CANONICAL_BULLET,
            self.CANONICAL_BULLET + "\n" + self.CANONICAL_BULLET,
        )
        self.assert_mutation_fails()


class INV2MutationTests(_MutationTestBase):
    """INV-2 (Phase 6.7 §6.3): four Clause 2 disclosure regex patterns
    (a)-(d) MUST not match anything inside a PATTERN PROTECTION block.
    Each test injects one canonical violation phrase as a new bullet
    above the canonical Clause 1 line and asserts lint fails."""

    CANONICAL_BULLET = INV1MutationTests.CANONICAL_BULLET

    def _inject_violation(self, file_rel: str, violation: str) -> None:
        """Insert a violation bullet immediately above the canonical line."""
        new_block = f"- {violation}\n{self.CANONICAL_BULLET}"
        _mutate(
            self._repo_dir,
            file_rel,
            self.CANONICAL_BULLET,
            new_block,
        )

    def test_inv2_a_orchestrator_audit_fails(self) -> None:
        # Pattern (a): \bthe orchestrator\b.*\baudit\b
        self._inject_violation(
            "deep-research/agents/synthesis_agent.md",
            "The orchestrator runs codex audit afterward.",
        )
        self.assert_mutation_fails()

    def test_inv2_b_cross_model_audit_template_fails(self) -> None:
        # Pattern (b): \bcross-model audit (?:follows|covers)\b.*codex_audit_multifile_template
        self._inject_violation(
            "deep-research/agents/research_architect_agent.md",
            "Cross-model audit covers these via dimension §3.5 of "
            "`shared/templates/codex_audit_multifile_template.md`.",
        )
        self.assert_mutation_fails()

    def test_inv2_c_audit_will_be_run_fails(self) -> None:
        # Pattern (c): \baudit (?:afterwards?|will be run|is dispatched)\b
        self._inject_violation(
            "deep-research/agents/report_compiler_agent.md",
            "An audit will be run on the deliverable.",
        )
        self.assert_mutation_fails()

    def test_inv2_d_downstream_audit_fails(self) -> None:
        # Pattern (d): \bdownstream audit\b
        self._inject_violation(
            "deep-research/agents/synthesis_agent.md",
            "A downstream audit covers narrative claims.",
        )
        self.assert_mutation_fails()

    def test_inv2_d_this_output_will_be_audited_fails(self) -> None:
        # Pattern (d) second alternative: \bthis output (?:is|will be) audited\b
        self._inject_violation(
            "deep-research/agents/research_architect_agent.md",
            "This output will be audited by codex downstream.",
        )
        self.assert_mutation_fails()


class INV3MutationTests(_MutationTestBase):
    """INV-3 (Phase 6.7 §6.3): canonical Clause 1 line MUST NOT appear in
    any agent prompt outside the v3.6.7 inversion manifest. Adding the
    line to a non-manifest agent prompt OR shrinking the manifest below
    the three v3.6.7 downstream agents MUST fail lint."""

    CANONICAL_BULLET = INV1MutationTests.CANONICAL_BULLET

    def test_inv3_canonical_in_non_manifest_agent_fails(self) -> None:
        # Add the canonical line to bibliography_agent (which is NOT in
        # the v3.6.7 inversion manifest). The §6 sweep is v3.6.7-only;
        # widening to a fourth file is the §9 L2 deferred question and
        # MUST fail lint as a guard against accidental sweep widening.
        non_manifest_path = self._repo_dir / "deep-research/agents/bibliography_agent.md"
        # Sanity-check the file exists and isn't already in the manifest.
        self.assertTrue(non_manifest_path.exists())
        original = non_manifest_path.read_text(encoding="utf-8")
        non_manifest_path.write_text(
            original + "\n\n" + self.CANONICAL_BULLET + "\n",
            encoding="utf-8",
        )
        self.assert_mutation_fails()

    def test_inv3_manifest_shrunk_to_two_files_fails(self) -> None:
        # Drop one entry from the manifest. The dropped file's canonical
        # line is now "outside" the manifest from INV-3's perspective and
        # must be flagged.
        manifest_path = self._repo_dir / "scripts/v3_6_7_inversion_manifest.json"
        import json
        data = json.loads(manifest_path.read_text(encoding="utf-8"))
        self.assertEqual(len(data["files"]), 3)
        data["files"] = data["files"][:2]
        manifest_path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
        self.assert_mutation_fails()

    def test_inv3_manifest_extra_nonexistent_entry_fails(self) -> None:
        # Adding a fourth file to the manifest that does not carry the
        # canonical line must fail INV-1 (the manifest claims a file that
        # is not actually swept). This guards against drift where someone
        # widens the manifest without doing the corresponding prompt edit.
        manifest_path = self._repo_dir / "scripts/v3_6_7_inversion_manifest.json"
        import json
        data = json.loads(manifest_path.read_text(encoding="utf-8"))
        data["files"].append("deep-research/agents/bibliography_agent.md")
        manifest_path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
        self.assert_mutation_fails()


class CodexR1MutationTests(_MutationTestBase):
    """Codex R1 (Phase 6.7 review) closures: 3 P2 findings against the
    initial INV-1/INV-2/INV-3 implementation. Each test re-introduces the
    bypass codex demonstrated and asserts lint now fails."""

    CANONICAL_BULLET = INV1MutationTests.CANONICAL_BULLET

    def test_r1_p2_inv2_wrapped_disclosure_fails(self) -> None:
        # Codex R1 P2: INV-2 patterns compiled without re.DOTALL allow a
        # forbidden Clause 2 sentence to be Markdown-soft-wrapped across
        # newlines and slip past the regex. Inject a wrapped (a) violation
        # ("the orchestrator" on one line, "audit" on the next) and
        # assert lint fails. Phase 6.7 R1 closure compiles INV-2 with
        # IGNORECASE | DOTALL so `.` crosses newlines.
        wrapped_violation = (
            "- The orchestrator dispatches against the\n"
            "  template and codex audit covers each deliverable."
        )
        _mutate(
            self._repo_dir,
            "deep-research/agents/synthesis_agent.md",
            self.CANONICAL_BULLET,
            wrapped_violation + "\n" + self.CANONICAL_BULLET,
        )
        self.assert_mutation_fails()

    def test_r1_p2_inv1_canonical_with_tail_weakener_fails(self) -> None:
        # Codex R1 P2: the prior CANONICAL_CLAUSE_1_RE stopped at
        # `state\b` so a manifest prompt could keep the canonical
        # sentence yet append ` if feasible.` and INV-1 still passed.
        # Phase 6.7 R1 closure anchors the regex to `state\.\s*$` with
        # re.MULTILINE so any tail content on the same bullet line
        # breaks the match. Both INV-1 and the C3 regex must reject this
        # mutation (defense in depth — the C3 negation post-filter also
        # catches `if feasible` via _ALWAYS_NEGATION_PATTERNS).
        _mutate(
            self._repo_dir,
            "deep-research/agents/report_compiler_agent.md",
            "Output metadata must not claim audit-passed state.",
            "Output metadata must not claim audit-passed state if feasible.",
        )
        self.assert_mutation_fails()

    def test_r1_p2_manifest_widening_with_canonical_copy_fails(self) -> None:
        # Codex R1 P2: a copy-paste widening attack — add a fourth file
        # to the manifest AND copy the canonical bullet into that file's
        # PATTERN PROTECTION block. Pre-fix INV-1 passed for all four
        # (canonical line present everywhere) and INV-3 silently skipped
        # the new file because it was now in `manifest_set`. Phase 6.7
        # R1 closure validates manifest['files'] against the frozen
        # EXPECTED_MANIFEST_FILES set (exact match, no superset / no
        # drift); widening triggers L2 resolution per spec §6.3 line
        # 1807, which requires landing a v3.6.8+ manifest, not editing
        # the v3.6.7 one. Construct the attack and assert lint fails.
        bibliography = self._repo_dir / "deep-research/agents/bibliography_agent.md"
        original = bibliography.read_text(encoding="utf-8")
        bibliography.write_text(
            original
            + "\n\n## PATTERN PROTECTION (v3.6.7)\n\n"
            + self.CANONICAL_BULLET
            + "\n",
            encoding="utf-8",
        )
        manifest_path = self._repo_dir / "scripts/v3_6_7_inversion_manifest.json"
        import json
        data = json.loads(manifest_path.read_text(encoding="utf-8"))
        data["files"].append("deep-research/agents/bibliography_agent.md")
        manifest_path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
        self.assert_mutation_fails()

    def test_r1_p2_manifest_duplicate_entry_fails(self) -> None:
        # Defense in depth on the same closure: a duplicate file path in
        # `files` should also fail (per uniqueness check added in the
        # R1 fix), even if the path is otherwise valid.
        manifest_path = self._repo_dir / "scripts/v3_6_7_inversion_manifest.json"
        import json
        data = json.loads(manifest_path.read_text(encoding="utf-8"))
        data["files"].append(data["files"][0])  # duplicate first entry
        manifest_path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
        self.assert_mutation_fails()


class CodexR2MutationTests(_MutationTestBase):
    """Codex R2 (Phase 6.7 review, after R1 fixes) closures: 2 P2
    findings against the bullet-text exactness contract and INV-2's
    cross-bullet `.*` over-reach."""

    CANONICAL_BULLET = INV1MutationTests.CANONICAL_BULLET

    def test_r2_p2_inv1_bullet_prefix_weakener_fails(self) -> None:
        # Codex R2 P2: a bullet of the form `- When feasible, DO NOT
        # simulate ...` carries the canonical sentences as a substring
        # but is NOT a verbatim canonical bullet. The pre-fix INV-1
        # regex search-anywhere accepted this; the bullet-extraction +
        # exact-match contract rejects it.
        _mutate(
            self._repo_dir,
            "deep-research/agents/report_compiler_agent.md",
            self.CANONICAL_BULLET,
            "- When feasible, DO NOT simulate any audit step. DO NOT "
            "claim to have run codex/external review. Output metadata "
            "must not claim audit-passed state.",
        )
        self.assert_mutation_fails()

    def test_r2_p2_inv1_softwrap_canonical_passes(self) -> None:
        # Codex R2 P2 dual: a soft-wrapped canonical bullet (line break
        # between `run` and `codex/external`) MUST still pass INV-1.
        # This is the false-negative side of the regex anchor problem
        # that the bullet-extraction + whitespace-normalization fix
        # closes. Asserts that this specific Markdown reflow does not
        # break baseline lint.
        _mutate(
            self._repo_dir,
            "deep-research/agents/synthesis_agent.md",
            "DO NOT claim to have run codex/external review.",
            "DO NOT claim to have run\n  codex/external review.",
        )
        # Mutation should leave lint passing — the soft-wrap is benign.
        rc, _stdout, stderr = _run_lint(self._repo_dir)
        self.assertEqual(
            rc,
            0,
            f"soft-wrapped canonical bullet should still pass; stderr={stderr}",
        )

    def test_r2_p2_inv2_cross_bullet_no_false_positive(self) -> None:
        # Codex R2 P2: prior INV-2(a) `\bthe orchestrator\b.*\baudit\b`
        # with re.DOTALL applied to raw block text would match across
        # bullets — a benign `the orchestrator` mention in one bullet
        # plus the canonical bullet's `audit step` mention would
        # false-positive even though no single bullet expresses the
        # forbidden disclosure. Insert a benign orchestrator mention as
        # a NEW bullet near the canonical bullet and assert lint still
        # passes (no false positive).
        benign_bullet = (
            "- The orchestrator may supply the dispatch context for this "
            "block when running this agent."
        )
        _mutate(
            self._repo_dir,
            "deep-research/agents/synthesis_agent.md",
            self.CANONICAL_BULLET,
            benign_bullet + "\n" + self.CANONICAL_BULLET,
        )
        rc, _stdout, stderr = _run_lint(self._repo_dir)
        self.assertEqual(
            rc,
            0,
            f"benign cross-bullet 'orchestrator' mention should not "
            f"false-positive INV-2; stderr={stderr}",
        )

    def test_r2_p2_inv2_in_bullet_violation_still_fails(self) -> None:
        # Defense in depth on R2-002: the per-bullet INV-2 must STILL
        # catch a real violation that lives inside a single bullet.
        violation = "- The orchestrator runs codex audit afterward on the deliverable."
        _mutate(
            self._repo_dir,
            "deep-research/agents/research_architect_agent.md",
            self.CANONICAL_BULLET,
            violation + "\n" + self.CANONICAL_BULLET,
        )
        self.assert_mutation_fails()


class CodexR3MutationTests(_MutationTestBase):
    """Codex R3 (Phase 6.7 review, after R2 fixes) closure: 1 P2
    finding restoring INV-2 coverage of intro-paragraph prose, not
    just bullets."""

    CANONICAL_BULLET = INV1MutationTests.CANONICAL_BULLET

    def test_r3_p2_inv2_intro_paragraph_disclosure_fails(self) -> None:
        # Codex R3 P2: the Phase 6.7 sweep removed Clause 2 disclosure
        # sentences that lived in the intro paragraph of each PATTERN
        # PROTECTION block (e.g. "Cross-model audit follows ...
        # codex_audit_multifile_template.md ..." in synthesis_agent.md
        # line 164). After R2's per-bullet refactor, INV-2 only
        # iterated bullets and the original disclosure could be
        # silently re-added to the intro paragraph. Phase 6.7 R3
        # closure adds prose-paragraph segments to INV-2's iteration
        # via `_iter_block_segments`. Re-introduce the original
        # `Cross-model audit follows ...` sentence into synthesis's
        # intro paragraph and assert lint catches it as a prose
        # violation.
        _mutate(
            self._repo_dir,
            "deep-research/agents/synthesis_agent.md",
            "documented in `docs/design/2026-04-29-ars-v3.6.7-downstream-agent-pattern-protection-spec.md` §3.1 (A1–A5).",
            "documented in `docs/design/2026-04-29-ars-v3.6.7-downstream-agent-pattern-protection-spec.md` §3.1 (A1–A5). "
            "Cross-model audit follows `shared/templates/codex_audit_multifile_template.md` audit dimensions §3.1, §3.2, §3.3, §3.4.",
        )
        self.assert_mutation_fails()


class CodexR4MutationTests(_MutationTestBase):
    """Codex R4 (Phase 6.7 review, after R3 fixes) closure: 1 P2
    finding restoring INV-2 coverage of post-bullet prose."""

    CANONICAL_BULLET = INV1MutationTests.CANONICAL_BULLET

    def test_r4_p2_inv2_post_bullet_prose_disclosure_fails(self) -> None:
        # Codex R4 P2: R3's `_iter_block_segments` only iterated prose
        # paragraphs in `block[:first_bullet]` — pre-first-bullet
        # only. A Clause 2 disclosure appended as a paragraph AFTER
        # the canonical bullet (or anywhere after the bullet list)
        # was outside the segmentation window and silently passed
        # lint. R4 closure rewrites segmentation to paragraph-split
        # the entire block, distinguishing bullet groups (`- ...`
        # paragraphs) from prose paragraphs uniformly. Append a
        # forbidden disclosure as a trailing prose paragraph and
        # assert lint catches it.
        _mutate(
            self._repo_dir,
            "deep-research/agents/synthesis_agent.md",
            "Output metadata must not claim audit-passed state.\n",
            "Output metadata must not claim audit-passed state.\n"
            "\nThe orchestrator runs codex audit afterward.\n",
        )
        self.assert_mutation_fails()


class CodexR5MutationTests(_MutationTestBase):
    """Codex R5 (Phase 6.7 review, after R4 fixes) closure: 1 P2
    finding — C3 regex was not whitespace-tolerant inside sentences,
    causing CI to fail on harmless Markdown soft-wraps that INV-1
    correctly accepts."""

    def test_r5_p2_compiler_softwrap_canonical_passes(self) -> None:
        # Codex R5 P2: C3 regex used literal spaces inside sentences,
        # so a soft-wrap between `run` and `codex/external` (the same
        # benign Markdown reflow R2's INV-1 test verifies for synthesis)
        # caused CI to fail on report_compiler. Phase 6.7 R5 closure
        # rewrites every inter-token space inside the canonical regex
        # to `\s+` so soft-wrap tolerance is uniform across INV-1 and
        # the C3 Check regex. Mutation should leave lint passing.
        _mutate(
            self._repo_dir,
            "deep-research/agents/report_compiler_agent.md",
            "DO NOT claim to have run codex/external review.",
            "DO NOT claim to have run\n  codex/external review.",
        )
        rc, _stdout, stderr = _run_lint(self._repo_dir)
        self.assertEqual(
            rc,
            0,
            f"compiler soft-wrap canonical bullet should pass; stderr={stderr}",
        )


class CodexR6MutationTests(_MutationTestBase):
    """Codex R6 (Phase 6.7 review, after R5 fixes) closure: 1 P2
    finding — INV-1 only counted exact canonical matches and ignored
    weakened near-duplicates that preserved an exact canonical bullet
    while adding a confusing variant alongside."""

    CANONICAL_BULLET = INV1MutationTests.CANONICAL_BULLET

    def test_r6_p2_inv1_weakened_duplicate_alongside_canonical_fails(self) -> None:
        # Codex R6 P2: an attacker keeps the exact canonical bullet
        # AND adds a second, weakened variant
        # (`- When feasible, DO NOT simulate ...`). Pre-fix INV-1 used
        # `count(exact) == 1` which stayed at 1; lint passed and the
        # block was left in a state where the agent reads two
        # contradictory bullets. Phase 6.7 R6 closure introduces
        # `_is_clause_1_like` that flags any bullet carrying canonical
        # fragment markers (`do not simulate`, `do not claim to have
        # run`, `audit-passed state`); each flagged bullet must equal
        # the canonical text byte-for-byte or lint fails.
        weakened = (
            "- When feasible, DO NOT simulate any audit step. DO NOT "
            "claim to have run codex/external review. Output metadata "
            "must not claim audit-passed state."
        )
        _mutate(
            self._repo_dir,
            "deep-research/agents/synthesis_agent.md",
            self.CANONICAL_BULLET,
            self.CANONICAL_BULLET + "\n" + weakened,
        )
        self.assert_mutation_fails()

    def test_r6_p2_inv1_tail_weakened_duplicate_fails(self) -> None:
        # Defense in depth on R6: tail-weakener variant of the same
        # attack (`... audit-passed state if feasible.`) — preserves
        # canonical, adds a near-duplicate with a tail weakener.
        weakened = (
            "- DO NOT simulate any audit step. DO NOT claim to have "
            "run codex/external review. Output metadata must not "
            "claim audit-passed state if feasible."
        )
        _mutate(
            self._repo_dir,
            "deep-research/agents/research_architect_agent.md",
            self.CANONICAL_BULLET,
            self.CANONICAL_BULLET + "\n" + weakened,
        )
        self.assert_mutation_fails()


class CodexR7R9MutationTests(_MutationTestBase):
    """Codex R7 → R9 architectural rewind: R7 originally extended INV-3
    with `_is_clause_1_like` to catch weakened variants outside the
    manifest. R9 surfaced that this over-extends: spec §6.3 INV-3
    detects "the canonical Clause 1 line found outside the manifest"
    (the actual sentence), not Clause 1-like variants. v3.6.7 does not
    lint variants outside the manifest. Test updated to reflect the
    correct contract: a weakened variant in a non-manifest agent
    passes lint."""

    def test_r9_inv3_weakened_clause_1_in_non_manifest_passes(self) -> None:
        # Codex R9 P2 architectural rewind: a weakened canonical
        # variant outside the manifest is NOT a v3.6.7 INV-3 violation.
        # Only the exact canonical sentence (whitespace-normalized
        # equal to CANONICAL_CLAUSE_1_TEXT) widens the scope. Variants
        # are a v3.6.8+ concern if/when L2 is reopened.
        bibliography = self._repo_dir / "deep-research/agents/bibliography_agent.md"
        original = bibliography.read_text(encoding="utf-8")
        weakened = (
            "\n\n- When feasible, DO NOT simulate any audit step. DO NOT "
            "claim to have run codex/external review. Output metadata "
            "must not claim audit-passed state.\n"
        )
        bibliography.write_text(original + weakened, encoding="utf-8")
        rc, _stdout, stderr = _run_lint(self._repo_dir)
        self.assertEqual(
            rc,
            0,
            f"weakened Clause 1 variant outside manifest is not a "
            f"v3.6.7 INV-3 violation per R9 architectural rewind; "
            f"stderr={stderr}",
        )


class CodexR8MutationTests(_MutationTestBase):
    """Codex R8 (Phase 6.7 review, after R7 fixes) closures: 2 P2
    findings — `_is_clause_1_like` was over-broad (rejected legitimate
    anti-fabrication guidance) AND INV-3 missed prose-form Clause 1
    copies."""

    CANONICAL_BULLET = INV1MutationTests.CANONICAL_BULLET

    def test_r8_p2_generic_do_not_simulate_in_non_manifest_passes(self) -> None:
        # Codex R8 P2 (a): the prior `_is_clause_1_like` flagged any
        # bullet containing `do not simulate`, which is common
        # anti-fabrication language. A legitimate non-manifest bullet
        # like `- Do not simulate data or sources.` would
        # false-positive INV-3 even though it has no audit-prohibition
        # semantics. Phase 6.7 R8 closure narrows the heuristic to
        # require an audit-specific fragment (`audit step`,
        # `audit-passed state`, or `codex/external review`). Inject
        # the generic bullet into bibliography_agent and assert lint
        # passes (no false positive).
        bibliography = self._repo_dir / "deep-research/agents/bibliography_agent.md"
        original = bibliography.read_text(encoding="utf-8")
        bibliography.write_text(
            original + "\n\n- Do not simulate data or sources.\n",
            encoding="utf-8",
        )
        rc, _stdout, stderr = _run_lint(self._repo_dir)
        self.assertEqual(
            rc,
            0,
            f"generic anti-fabrication bullet should not false-positive "
            f"INV-3 after R8 audit-specific tightening; stderr={stderr}",
        )

    def test_r8_p2_inv3_canonical_as_prose_in_non_manifest_fails(self) -> None:
        # Codex R8 P2 (b): the prior INV-3 only walked Markdown bullets.
        # A non-manifest agent prompt that pasted the exact canonical
        # sentence as a normal paragraph (not a `- ` bullet) silently
        # passed lint, even though the v3.6.7 prohibition was now
        # widened beyond the frozen manifest. Phase 6.7 R8 closure adds
        # a paragraph-level scan that compares whitespace-normalized
        # prose paragraphs against `CANONICAL_CLAUSE_1_TEXT` exactly.
        # Inject the canonical sentence as a prose paragraph in
        # bibliography_agent and assert lint fails.
        bibliography = self._repo_dir / "deep-research/agents/bibliography_agent.md"
        original = bibliography.read_text(encoding="utf-8")
        canon_prose = (
            "\n\nDO NOT simulate any audit step. DO NOT claim to have "
            "run codex/external review. Output metadata must not claim "
            "audit-passed state.\n"
        )
        bibliography.write_text(original + canon_prose, encoding="utf-8")
        self.assert_mutation_fails()


class CodexR9MutationTests(_MutationTestBase):
    """Codex R9 (Phase 6.7 review, after R8 fixes) architectural
    rewind: R7+R8 had over-extended INV-3 with the
    Clause 1-like heuristic (false-positives on legitimate audit-step
    mentions in non-manifest agents) AND under-extended prose scan
    (missed canonical-after-heading-no-blank-line). R9 closes both."""

    def test_r9_p2_inv3_audit_fragment_unrelated_bullet_passes(self) -> None:
        # Codex R9 P2 (a): a non-manifest agent prompt may legitimately
        # discuss audit steps in process-flow guidance, e.g.
        # `- Review each audit step before finalizing.`. R8's
        # heuristic flagged this as Clause 1-like even though the
        # bullet has no prohibition semantics. R9 closure scopes INV-3
        # to exact canonical sentence only.
        bibliography = self._repo_dir / "deep-research/agents/bibliography_agent.md"
        original = bibliography.read_text(encoding="utf-8")
        bibliography.write_text(
            original + "\n\n- Review each audit step before finalizing.\n",
            encoding="utf-8",
        )
        rc, _stdout, stderr = _run_lint(self._repo_dir)
        self.assertEqual(
            rc,
            0,
            f"unrelated audit-step bullet should not trip INV-3 after "
            f"R9 architectural rewind; stderr={stderr}",
        )

    def test_r9_p2_inv3_canonical_after_heading_no_blank_line_fails(self) -> None:
        # Codex R9 P2 (b): when the canonical sentence is pasted as
        # prose immediately after a Markdown heading with no blank
        # line, R8's `re.split(r"\n\s*\n", text)` kept the heading and
        # sentence in one paragraph, and the `startswith("## ")`
        # filter skipped the whole thing. R9 closure switches to
        # line-level heading-strip + whitespace-collapse so heading
        # adjacency does not bypass the prose scan.
        bibliography = self._repo_dir / "deep-research/agents/bibliography_agent.md"
        original = bibliography.read_text(encoding="utf-8")
        injection = (
            "\n\n## PATTERN PROTECTION (v3.6.7)\n"
            "DO NOT simulate any audit step. DO NOT claim to have run "
            "codex/external review. Output metadata must not claim "
            "audit-passed state.\n"
        )
        bibliography.write_text(original + injection, encoding="utf-8")
        self.assert_mutation_fails()


if __name__ == "__main__":
    unittest.main()
