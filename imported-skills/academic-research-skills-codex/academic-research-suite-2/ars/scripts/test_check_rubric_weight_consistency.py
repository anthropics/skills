"""Unit tests for check_rubric_weight_consistency.py (#396 lint)."""
from __future__ import annotations

import subprocess
import textwrap
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from tests.test_helpers import run_script

SCRIPT = Path(__file__).resolve().parent / "check_rubric_weight_consistency.py"
REPO_ROOT = SCRIPT.parent.parent


def _run(root: Path) -> subprocess.CompletedProcess:
    return run_script(SCRIPT, "--root", str(root))


def _write_rubrics(
    root: Path,
    *,
    header_originality: int = 20,
    formula_originality: str = "0.20",
    formula_writing: str = "0.15",
) -> None:
    path = root / "academic-paper-reviewer" / "references" / "quality_rubrics.md"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        textwrap.dedent(
            f"""\
            # Quality Rubrics

            ## Dimension 1: Originality (Weight: {header_originality}%)

            | Score Range | Descriptor |
            |------------|------------|
            | 90-100 | Exceptional |

            ## Dimension 2: Methodological Rigor (Weight: 25%)

            ## Dimension 3: Evidence Sufficiency (Weight: 25%)

            ## Dimension 4: Argument Coherence (Weight: 15%)

            ## Dimension 5: Writing Quality (Weight: 15%)

            ## Aggregation Formula

            ```
            Final Score = (Originality x {formula_originality}) + (Methodology x 0.25) + (Evidence x 0.25) + (Coherence x 0.15) + (Writing x {formula_writing})
            ```
            """
        ),
        encoding="utf-8",
    )


def _write_framework(root: Path, *, restate_weight: bool = False) -> None:
    path = (
        root
        / "academic-paper-reviewer"
        / "references"
        / "review_criteria_framework.md"
    )
    path.parent.mkdir(parents=True, exist_ok=True)
    suffix = " — Weight 15%" if restate_weight else ""
    path.write_text(
        textwrap.dedent(
            f"""\
            # Review Criteria Framework

            Weights are single-sourced in `quality_rubrics.md`.

            ### Dimension 1: Originality{suffix}

            | Level | Score | Description |
            |-------|-------|-------------|
            | Outstanding | 5 | New theory |
            """
        ),
        encoding="utf-8",
    )


def _write_paper_skill(root: Path, *, originality: int = 20) -> None:
    path = root / "academic-paper" / "SKILL.md"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        textwrap.dedent(
            f"""\
            # academic-paper

            14. **Five dimensions** — Originality ({originality}%), Methodological Rigor (25%), Evidence Sufficiency (25%), Argument Coherence (15%), Writing Quality (15%)
            """
        ),
        encoding="utf-8",
    )


def _write_consistent_tree(root: Path) -> None:
    _write_rubrics(root)
    _write_framework(root)
    _write_paper_skill(root)


class TestRubricWeightConsistency(unittest.TestCase):
    def test_consistent_tree_passes(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_consistent_tree(root)
            result = _run(root)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("rubric weights consistent", result.stdout)

    def test_header_vs_formula_mismatch_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_consistent_tree(root)
            _write_rubrics(root, header_originality=30)
            result = _run(root)
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            self.assertIn("header says 30%, formula says 20%", result.stderr)

    def test_skill_rule_drift_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_consistent_tree(root)
            _write_paper_skill(root, originality=15)
            result = _run(root)
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            self.assertIn("SKILL.md", result.stderr)

    def test_framework_weight_restatement_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_consistent_tree(root)
            _write_framework(root, restate_weight=True)
            result = _run(root)
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            self.assertIn("restates a weight", result.stderr)

    def test_framework_percent_parenthetical_fails(self) -> None:
        # The other restatement shape: a "(NN%)" aggregation-style term.
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_consistent_tree(root)
            path = (
                root
                / "academic-paper-reviewer"
                / "references"
                / "review_criteria_framework.md"
            )
            path.write_text(
                path.read_text(encoding="utf-8") + "\nTotal = Originality (15%) + ...\n",
                encoding="utf-8",
            )
            result = _run(root)
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            self.assertIn("restates a weight", result.stderr)

    def test_weights_not_summing_to_100_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_consistent_tree(root)
            # Drop Writing from 15 to 10 in BOTH header and formula: internally
            # consistent and matching, but the sum is 95.
            _write_rubrics(root, formula_writing="0.10")
            rubrics = (
                root / "academic-paper-reviewer" / "references" / "quality_rubrics.md"
            )
            rubrics.write_text(
                rubrics.read_text(encoding="utf-8").replace(
                    "Writing Quality (Weight: 15%)", "Writing Quality (Weight: 10%)"
                ),
                encoding="utf-8",
            )
            _write_paper_skill(root)
            result = _run(root)
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            self.assertIn("sum to 95%", result.stderr)

    def test_missing_formula_heading_is_parse_error(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_consistent_tree(root)
            rubrics = (
                root / "academic-paper-reviewer" / "references" / "quality_rubrics.md"
            )
            rubrics.write_text(
                rubrics.read_text(encoding="utf-8").replace(
                    "## Aggregation Formula", "## Renamed Heading"
                ),
                encoding="utf-8",
            )
            result = _run(root)
            self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
            self.assertIn("PARSE ERROR", result.stderr)

    def test_missing_file_is_parse_error(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_consistent_tree(root)
            (root / "academic-paper" / "SKILL.md").unlink()
            result = _run(root)
            self.assertEqual(result.returncode, 2, result.stdout + result.stderr)

    def test_real_repo_is_consistent(self) -> None:
        result = _run(REPO_ROOT)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
