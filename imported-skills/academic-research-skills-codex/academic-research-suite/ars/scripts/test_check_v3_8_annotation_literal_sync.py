"""Unit tests for v3.8 annotation-literal sync lint.

The lint enforces that every `ANNOTATION_HIGH_WARN_*` constant in
`scripts/claim_audit_finalizer.py` has a matching bracket-prefix in
`academic-paper/agents/formatter_agent.md` REFUSE list. The tests cover:

1. The prefix-extraction helper handles the three annotation literal
   shapes correctly (plain closed, parenthesized variable, em-dash
   contextual suffix).
2. The lint reports PASS on the current repo state.
3. The lint reports FAIL when a deliberately mutated finalizer module
   adds an extra HIGH-WARN constant that the formatter doesn't carry.

Run:
    python -m unittest scripts.test_check_v3_8_annotation_literal_sync -v
"""
from __future__ import annotations

import subprocess
import sys
import textwrap
import unittest
from pathlib import Path

from scripts.check_v3_8_annotation_literal_sync import (
    _annotation_prefix,
    _extract_refuse_block,
)


REPO_ROOT = Path(__file__).resolve().parent.parent
LINT_SCRIPT = REPO_ROOT / "scripts" / "check_v3_8_annotation_literal_sync.py"


class AnnotationPrefixHelperTest(unittest.TestCase):
    def test_plain_closed_literal_keeps_closing_bracket(self) -> None:
        # Step 8 codex R2 P2-1 closure: closed literals require exact match
        # INCLUDING the closing bracket. Cutting at `]` left the prefix without
        # the bracket, so a renamed formatter rule
        # `[HIGH-WARN-FABRICATED-REFERENCE-RENAMED]` would still satisfy the
        # check for finalizer literal `[HIGH-WARN-FABRICATED-REFERENCE]`.
        self.assertEqual(
            _annotation_prefix("[HIGH-WARN-CLAIM-NOT-SUPPORTED]"),
            "[HIGH-WARN-CLAIM-NOT-SUPPORTED]",
        )

    def test_interpolated_parenthesized_variable_cuts_at_space_paren(self) -> None:
        self.assertEqual(
            _annotation_prefix(
                "[HIGH-WARN-NEGATIVE-CONSTRAINT-VIOLATION ({violated_constraint_id})]"
            ),
            "[HIGH-WARN-NEGATIVE-CONSTRAINT-VIOLATION",
        )

    def test_em_dash_contextual_suffix_cuts_at_space_emdash(self) -> None:
        self.assertEqual(
            _annotation_prefix(
                "[HIGH-WARN-CLAIM-AUDIT-ANCHORLESS — v3.7.3 R-L3-1-A VIOLATION REACHED AUDIT]"
            ),
            "[HIGH-WARN-CLAIM-AUDIT-ANCHORLESS",
        )

    def test_interpolated_uncited_constraint_violation_prefix(self) -> None:
        self.assertEqual(
            _annotation_prefix(
                "[HIGH-WARN-CONSTRAINT-VIOLATION-UNCITED ({violated_constraint_id})]"
            ),
            "[HIGH-WARN-CONSTRAINT-VIOLATION-UNCITED",
        )

    def test_fabricated_reference_plain_literal(self) -> None:
        # Closed plain literal keeps the closing bracket for exact match
        # (Step 8 codex R2 P2-1 closure).
        self.assertEqual(
            _annotation_prefix("[HIGH-WARN-FABRICATED-REFERENCE]"),
            "[HIGH-WARN-FABRICATED-REFERENCE]",
        )


class RefuseBlockExtractorTest(unittest.TestCase):
    """Step 8 codex R1 P3 closure: lint scope restricted to REFUSE-rules block."""

    def test_extracts_block_starting_at_refuse_marker(self) -> None:
        sample = textwrap.dedent(
            """\
            ## Cite-Time Provenance Hard Gate

            Some intro prose mentioning HIGH-WARN-CLAIM-NOT-SUPPORTED here.

            **REFUSE to emit final output** when the draft contains any of:

            1. Rule one.
            6. A literal `[HIGH-WARN-CLAIM-NOT-SUPPORTED]` annotation.

            ## Output Format

            Mentions HIGH-WARN-CLAIM-NOT-SUPPORTED outside the REFUSE block.
            """
        )
        block = _extract_refuse_block(sample)
        self.assertIsNotNone(block)
        self.assertIn("[HIGH-WARN-CLAIM-NOT-SUPPORTED]", block)
        # The intro mention before the REFUSE marker MUST be excluded.
        self.assertNotIn(
            "Some intro prose mentioning HIGH-WARN-CLAIM-NOT-SUPPORTED here.", block
        )
        # The Output Format mention after the next H2 MUST be excluded.
        self.assertNotIn(
            "Mentions HIGH-WARN-CLAIM-NOT-SUPPORTED outside the REFUSE block.", block
        )

    def test_returns_none_when_refuse_marker_absent(self) -> None:
        sample = "## Some heading\n\nNo REFUSE-list marker anywhere.\n"
        self.assertIsNone(_extract_refuse_block(sample))


class LintScriptTest(unittest.TestCase):
    def test_lint_passes_on_current_repo_state(self) -> None:
        # The lint MUST pass on the shipped repo — Step 8 commit cluster
        # closed the §3.6 + REFUSE list rules 6-10. A failure here means a
        # subsequent edit drifted the finalizer literals away from the
        # formatter prose without updating both sides.
        result = subprocess.run(
            [sys.executable, str(LINT_SCRIPT)],
            capture_output=True,
            text=True,
            cwd=str(REPO_ROOT),
        )
        self.assertEqual(
            result.returncode,
            0,
            f"lint exited with code {result.returncode}; stdout={result.stdout!r}; "
            f"stderr={result.stderr!r}",
        )
        self.assertIn("PASS", result.stdout)

    def test_lint_detects_dynamic_literal_substring_match_attack(self) -> None:
        # Step 8 codex R3 P2 closure: interpolated/em-dash literals MUST
        # also require a boundary character following the token in formatter
        # prose, not raw substring match. A rename that appends text
        # (`[HIGH-WARN-NEGATIVE-CONSTRAINT-VIOLATION-RENAMED`) would have
        # passed the R1/R2 lint via prefix-substring containment.
        import tempfile
        import shutil

        with tempfile.TemporaryDirectory() as td:
            tmp_root = Path(td) / "repo"
            shutil.copytree(REPO_ROOT, tmp_root, ignore=shutil.ignore_patterns(
                ".git", "node_modules", "__pycache__", "*.pyc", "venv*", ".venv"
            ))
            tmp_formatter = tmp_root / "academic-paper" / "agents" / "formatter_agent.md"
            text = tmp_formatter.read_text()
            mutated = text.replace(
                "`[HIGH-WARN-NEGATIVE-CONSTRAINT-VIOLATION`",
                "`[HIGH-WARN-NEGATIVE-CONSTRAINT-VIOLATION-RENAMED`",
            )
            self.assertNotEqual(text, mutated, "mutation should replace the literal")
            tmp_formatter.write_text(mutated)

            result = subprocess.run(
                [sys.executable, str(tmp_root / "scripts" / "check_v3_8_annotation_literal_sync.py")],
                capture_output=True,
                text=True,
                cwd=str(tmp_root),
            )
            self.assertEqual(
                result.returncode,
                1,
                f"expected lint to fail on dynamic-literal rename; "
                f"stdout={result.stdout!r}",
            )
            self.assertIn(
                "HIGH-WARN-NEGATIVE-CONSTRAINT-VIOLATION",
                result.stdout,
            )

    def test_lint_detects_closed_literal_substring_match_attack(self) -> None:
        # Step 8 codex R2 P2-1 closure: the lint MUST NOT pass when the
        # formatter prose contains a SUPERSTRING of the finalizer literal
        # (e.g. finalizer says `[HIGH-WARN-FABRICATED-REFERENCE]` but
        # formatter REFUSE list was edited to `[HIGH-WARN-FABRICATED-
        # REFERENCE-RENAMED]`). The closing bracket is the contract
        # terminator for closed literals.
        import tempfile
        import shutil

        with tempfile.TemporaryDirectory() as td:
            tmp_root = Path(td) / "repo"
            shutil.copytree(REPO_ROOT, tmp_root, ignore=shutil.ignore_patterns(
                ".git", "node_modules", "__pycache__", "*.pyc", "venv*", ".venv"
            ))
            tmp_formatter = tmp_root / "academic-paper" / "agents" / "formatter_agent.md"
            text = tmp_formatter.read_text()
            # Replace the closed literal in the formatter REFUSE rule with a
            # superstring that PRESERVES the original as a prefix. A naive
            # `prefix in text` check would still pass; the exact-closing-
            # bracket contract catches it.
            mutated = text.replace(
                "[HIGH-WARN-FABRICATED-REFERENCE]",
                "[HIGH-WARN-FABRICATED-REFERENCE-RENAMED]",
            )
            self.assertNotEqual(text, mutated, "mutation should replace the literal")
            tmp_formatter.write_text(mutated)

            result = subprocess.run(
                [sys.executable, str(tmp_root / "scripts" / "check_v3_8_annotation_literal_sync.py")],
                capture_output=True,
                text=True,
                cwd=str(tmp_root),
            )
            self.assertEqual(
                result.returncode,
                1,
                f"expected lint to fail on superstring formatter literal; "
                f"stdout={result.stdout!r}",
            )
            self.assertIn("HIGH-WARN-FABRICATED-REFERENCE", result.stdout)

    def test_lint_detects_renamed_constant_missing_from_formatter(self) -> None:
        # Simulate the canonical drift scenario: the finalizer renames an
        # existing HIGH-WARN constant's literal (e.g. CLAIM-NOT-SUPPORTED →
        # CLAIM-UNSUPPORTED) without coordinating with the formatter prose.
        # The lint MUST exit 1 and surface the renamed prefix as missing.
        # Renaming (not adding) keeps the count at 5 so the constant-count
        # gate doesn't fire first — the real failure mode is the literal-
        # match gate, which is what we want this test to pin.
        import tempfile
        import shutil

        with tempfile.TemporaryDirectory() as td:
            tmp_root = Path(td) / "repo"
            shutil.copytree(REPO_ROOT, tmp_root, ignore=shutil.ignore_patterns(
                ".git", "node_modules", "__pycache__", "*.pyc", "venv*", ".venv"
            ))
            tmp_finalizer = tmp_root / "scripts" / "claim_audit_finalizer.py"
            text = tmp_finalizer.read_text()
            # Rename the CLAIM-NOT-SUPPORTED literal in place — the formatter
            # prose still says NOT-SUPPORTED, so the lint must surface the
            # divergence on the renamed literal.
            mutated = text.replace(
                'ANNOTATION_HIGH_WARN_CLAIM_NOT_SUPPORTED = "[HIGH-WARN-CLAIM-NOT-SUPPORTED]"',
                'ANNOTATION_HIGH_WARN_CLAIM_NOT_SUPPORTED = "[HIGH-WARN-CLAIM-UNSUPPORTED-RENAMED]"',
            )
            self.assertNotEqual(text, mutated, "mutation should have replaced the literal")
            tmp_finalizer.write_text(mutated)

            result = subprocess.run(
                [sys.executable, str(tmp_root / "scripts" / "check_v3_8_annotation_literal_sync.py")],
                capture_output=True,
                text=True,
                cwd=str(tmp_root),
            )
            self.assertEqual(
                result.returncode,
                1,
                f"expected lint to fail on mutated finalizer; stdout={result.stdout!r}",
            )
            self.assertIn("HIGH-WARN-CLAIM-UNSUPPORTED-RENAMED", result.stdout)


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
