"""Unit tests for check_pipeline_integrity.py (v3.9.2 advisory verifier)."""
import json
import subprocess
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from tests.test_helpers import run_script

SCRIPT = Path(__file__).resolve().parent / "check_pipeline_integrity.py"


def _run(workdir: Path, *extra_args: str) -> subprocess.CompletedProcess:
    return run_script(SCRIPT, str(workdir), *extra_args)


def _build_workspace(root: Path, structure: dict[str, list[str]]) -> None:
    """Materialize a fixture: {phase_dir_name: [file1, file2, ...]}."""
    for dir_name, files in structure.items():
        d = root / dir_name
        d.mkdir(parents=True, exist_ok=True)
        for fname in files:
            (d / fname).touch()


class CheckPipelineIntegrityTests(unittest.TestCase):

    def test_empty_workdir_no_findings(self) -> None:
        with TemporaryDirectory() as td:
            result = _run(Path(td))
        self.assertEqual(result.returncode, 0)
        self.assertIn("No advisory findings.", result.stdout)

    def test_no_phase_dirs_no_findings(self) -> None:
        with TemporaryDirectory() as td:
            (Path(td) / "some_other_dir").mkdir()
            (Path(td) / "README.md").touch()
            result = _run(Path(td))
        self.assertEqual(result.returncode, 0)
        self.assertIn("No advisory findings.", result.stdout)

    def test_issue_133_inflation_case_phase5_missing_reviewers(self) -> None:
        """STRUCTURAL: phase5 with only generic review.md should flag missing
        attribution. This is the exact #133 reported failure pattern."""
        with TemporaryDirectory() as td:
            _build_workspace(Path(td), {
                "phase2_bibliography": ["annotated_bib.md"],
                "phase3_synthesis": ["synthesis.md"],
                "phase4_draft": ["draft_v1.md"],
                "phase5_review": ["review.md"],
                "phase6_revision": ["draft_v2.md"],
            })
            result = _run(Path(td))
        self.assertEqual(result.returncode, 0)
        self.assertIn("STRUCTURAL", result.stdout)
        self.assertIn("phase5_missing_independent_reviewer", result.stdout)
        self.assertIn("devil's advocate", result.stdout)
        self.assertIn("editorial/EIC", result.stdout)
        self.assertIn("ethics or panel reviewer", result.stdout)

    def test_legitimate_phase5_with_three_reviewer_files_passes(self) -> None:
        """Phase 5 with separate DA + EIC + Ethics files should produce
        no STRUCTURAL findings."""
        with TemporaryDirectory() as td:
            _build_workspace(Path(td), {
                "phase2_bibliography": ["annotated_bib.md"],
                "phase3_synthesis": ["synthesis.md"],
                "phase4_draft": ["draft_v1.md"],
                "phase5_review": [
                    "devils_advocate_report.md",
                    "editor_in_chief_decision.md",
                    "ethics_review.md",
                ],
                "phase6_revision": ["draft_v2.md"],
            })
            result = _run(Path(td))
        self.assertEqual(result.returncode, 0)
        self.assertNotIn("STRUCTURAL", result.stdout)
        self.assertIn("No advisory findings.", result.stdout)

    def test_phase5_methodology_domain_perspective_also_counts(self) -> None:
        """Alternative attribution: DA + EIC + 1 panel reviewer satisfies the
        3-category rule (any of methodology/domain/perspective for the
        'ethics or panel reviewer' category)."""
        with TemporaryDirectory() as td:
            _build_workspace(Path(td), {
                "phase5_review": [
                    "devils_advocate_card.md",
                    "eic_card.md",
                    "methodology_reviewer_card.md",
                ],
            })
            result = _run(Path(td))
        self.assertEqual(result.returncode, 0)
        self.assertIn("No advisory findings.", result.stdout)

    def test_phase5_empty_dir_flags_advisory(self) -> None:
        with TemporaryDirectory() as td:
            (Path(td) / "phase5_review").mkdir()
            result = _run(Path(td))
        self.assertEqual(result.returncode, 0)
        self.assertIn("phase5_empty", result.stdout)

    def test_phase5_with_only_editorial_synthesizer_flags_missing_da(self) -> None:
        """editorial_synthesizer alone is NOT enough — DA category and
        ethics/panel category are still missing."""
        with TemporaryDirectory() as td:
            _build_workspace(Path(td), {
                "phase5_review": ["editorial_synthesizer_letter.md"],
            })
            result = _run(Path(td))
        self.assertEqual(result.returncode, 0)
        self.assertIn("phase5_missing_independent_reviewer", result.stdout)
        self.assertIn("devil's advocate", result.stdout)
        self.assertIn("ethics or panel reviewer", result.stdout)
        # EIC/editorial category is satisfied by editorial_synthesizer
        self.assertNotIn("editorial/EIC", result.stdout)

    def test_strict_flag_triggers_heuristic(self) -> None:
        """--strict enables the adjacent-phase-same-window heuristic."""
        with TemporaryDirectory() as td:
            _build_workspace(Path(td), {
                "phase2_bibliography": ["annotated_bib.md"],
                "phase3_synthesis": ["synthesis.md"],
            })
            result = _run(Path(td), "--strict")
        self.assertEqual(result.returncode, 0)
        self.assertIn("HEURISTIC", result.stdout)
        self.assertIn("adjacent_phase_same_window", result.stdout)

    def test_no_strict_flag_skips_heuristic(self) -> None:
        """Default mode does NOT run the timestamp heuristic."""
        with TemporaryDirectory() as td:
            _build_workspace(Path(td), {
                "phase2_bibliography": ["annotated_bib.md"],
                "phase3_synthesis": ["synthesis.md"],
            })
            result = _run(Path(td))
        self.assertEqual(result.returncode, 0)
        self.assertNotIn("HEURISTIC", result.stdout)
        self.assertNotIn("adjacent_phase_same_window", result.stdout)

    def test_json_output_format(self) -> None:
        with TemporaryDirectory() as td:
            _build_workspace(Path(td), {
                "phase5_review": ["review.md"],
            })
            result = _run(Path(td), "--json")
        self.assertEqual(result.returncode, 0)
        payload = json.loads(result.stdout)
        self.assertIn("workdir", payload)
        self.assertIn("phase_dirs", payload)
        self.assertIn("findings", payload)
        self.assertGreaterEqual(len(payload["findings"]), 1)
        # Find the structural finding
        rules = [f["rule"] for f in payload["findings"]]
        self.assertIn("phase5_missing_independent_reviewer", rules)

    def test_invalid_workdir_returns_exit_1(self) -> None:
        result = _run(Path("/tmp/nonexistent_dir_for_test_xyz_133"))
        self.assertEqual(result.returncode, 1)
        self.assertIn("not found", result.stderr)

    def test_non_phase_dirs_ignored(self) -> None:
        """Directories not matching phase[1-6]_* pattern are skipped."""
        with TemporaryDirectory() as td:
            (Path(td) / "phase0_intake").mkdir()  # Phase 0 outside 1-6 range
            (Path(td) / "phase7_format").mkdir()  # Phase 7 outside 1-6 range
            (Path(td) / "stage5_review").mkdir()  # Wrong prefix
            result = _run(Path(td))
        self.assertEqual(result.returncode, 0)
        self.assertIn("No advisory findings.", result.stdout)

    def test_dotfiles_in_phase5_ignored(self) -> None:
        """Hidden files (.DS_Store, .gitkeep, Thumbs.db) should not count as
        review reports. They're noise from the OS/git, not authored content."""
        with TemporaryDirectory() as td:
            _build_workspace(Path(td), {
                "phase5_review": [
                    ".DS_Store",
                    ".gitkeep",
                    "devils_advocate_card.md",
                    "eic_card.md",
                    "ethics_review.md",
                ],
            })
            result = _run(Path(td))
        self.assertEqual(result.returncode, 0)
        self.assertIn("No advisory findings.", result.stdout)

    def test_multiple_phase5_dirs_each_independently_checked(self) -> None:
        """phase5_review_r1/ + phase5_review_r2/ (multi-round) should each be
        evaluated independently. If one is complete and the other isn't, only
        the incomplete one flags."""
        with TemporaryDirectory() as td:
            _build_workspace(Path(td), {
                "phase5_review_r1": [
                    "devils_advocate_card.md",
                    "eic_card.md",
                    "ethics_review.md",
                ],
                "phase5_review_r2": [
                    "review.md",  # Incomplete — missing all 3 categories
                ],
            })
            result = _run(Path(td))
        self.assertEqual(result.returncode, 0)
        # The complete dir produces no finding; the incomplete one does.
        # The 'phase5_missing_independent_reviewer' rule should fire exactly once.
        self.assertEqual(result.stdout.count("phase5_missing_independent_reviewer"), 1)
        # Confirm only the r2 path is in the finding output, not r1.
        self.assertIn("phase5_review_r2", result.stdout)

    def test_unicode_filenames_with_canonical_stem_match(self) -> None:
        """Filenames with non-ASCII characters but containing the canonical
        agent stem in ASCII should still match. E.g., devils_advocate_報告.md"""
        with TemporaryDirectory() as td:
            _build_workspace(Path(td), {
                "phase5_review": [
                    "devils_advocate_報告.md",
                    "editor_in_chief_決定.md",
                    "ethics_review_報告.md",
                ],
            })
            result = _run(Path(td))
        self.assertEqual(result.returncode, 0)
        self.assertIn("No advisory findings.", result.stdout)

    def test_nested_files_in_phase5_count(self) -> None:
        """rglob recurses; reviewer card in a subdirectory should still match."""
        with TemporaryDirectory() as td:
            sub = Path(td) / "phase5_review" / "round1"
            sub.mkdir(parents=True)
            (sub / "devils_advocate.md").touch()
            (sub / "editor_in_chief.md").touch()
            (sub / "ethics_review.md").touch()
            result = _run(Path(td))
        self.assertEqual(result.returncode, 0)
        self.assertIn("No advisory findings.", result.stdout)


if __name__ == "__main__":
    unittest.main()
