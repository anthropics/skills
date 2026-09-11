"""Offline regression tests for eval isolation and loop failure handling."""

import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts.generate_report import generate_html
from scripts.run_eval import _raise_if_shadowed, _tool_use_mentions
from scripts.run_loop import run_loop


class FollowupGuardTests(unittest.TestCase):
    def make_skill(self, root: Path) -> Path:
        skill = root / "candidate"
        skill.mkdir()
        (skill / "SKILL.md").write_text(
            "---\nname: pdf\ndescription: test description\n---\n\n# pdf\n"
        )
        return skill

    def loop_args(self, skill_path: Path, max_iterations: int = 0) -> dict:
        return {
            "eval_set": [{"query": "q", "should_trigger": True}],
            "skill_path": skill_path,
            "description_override": None,
            "num_workers": 1,
            "timeout": 1,
            "max_iterations": max_iterations,
            "runs_per_query": 1,
            "trigger_threshold": 0.5,
            "holdout": 0,
            "model": "unused",
            "verbose": False,
        }

    def test_same_name_user_skill_fails_before_eval(self):
        with tempfile.TemporaryDirectory() as tmp:
            home = Path(tmp)
            installed = home / ".claude" / "skills" / "pdf"
            installed.mkdir(parents=True)
            with mock.patch("scripts.run_eval.Path.home", return_value=home):
                with self.assertRaisesRegex(RuntimeError, "would shadow"):
                    _raise_if_shadowed("pdf")

    def test_no_same_name_user_skill_is_allowed(self):
        with tempfile.TemporaryDirectory() as tmp:
            with mock.patch(
                "scripts.run_eval.Path.home", return_value=Path(tmp)
            ):
                _raise_if_shadowed("pdf")

    def test_short_skill_name_does_not_match_unrelated_tool_input(self):
        self.assertFalse(
            _tool_use_mentions("pdf", "Skill", {"skill": "pdf-tools"})
        )
        self.assertFalse(
            _tool_use_mentions("pdf", "Read", {"file_path": "/tmp/report.pdf"})
        )
        self.assertFalse(
            _tool_use_mentions(
                "pdf", "Bash", {"command": "convert report.pdf output.png"}
            )
        )

    def test_field_scoped_trigger_matching_handles_real_and_windows_paths(self):
        self.assertTrue(_tool_use_mentions("pdf", "Skill", {"skill": "pdf"}))
        self.assertTrue(
            _tool_use_mentions(
                "pdf",
                "Read",
                {"file_path": "/tmp/project/.claude/skills/pdf/SKILL.md"},
            )
        )
        self.assertTrue(
            _tool_use_mentions(
                "pdf",
                "Read",
                {"file_path": r"C:\tmp\project\.claude\skills\pdf\SKILL.md"},
            )
        )

    def test_zero_iterations_returns_renderable_result(self):
        with tempfile.TemporaryDirectory() as tmp:
            output = run_loop(**self.loop_args(self.make_skill(Path(tmp))))
        self.assertEqual(output["history"], [])
        self.assertEqual(output["best_description"], "test description")
        self.assertIsNone(output["best_score"])
        self.assertEqual(output["exit_reason"], "max_iterations (0)")
        self.assertIn("Skill Description Optimization", generate_html(output))

    def test_improvement_failure_keeps_completed_iteration(self):
        eval_output = {
            "results": [
                {
                    "query": "q",
                    "should_trigger": True,
                    "pass": False,
                    "triggers": 0,
                    "runs": 1,
                }
            ]
        }
        with tempfile.TemporaryDirectory() as tmp:
            args = self.loop_args(self.make_skill(Path(tmp)), max_iterations=2)
            with mock.patch("scripts.run_loop.run_eval", return_value=eval_output), mock.patch(
                "scripts.run_loop.improve_description",
                side_effect=RuntimeError("rate limited"),
            ):
                output = run_loop(**args)

        self.assertEqual(output["iterations_run"], 1)
        self.assertEqual(output["history"][0]["description"], "test description")
        self.assertEqual(output["best_description"], "test description")
        self.assertIn("rate limited", output["exit_reason"])


if __name__ == "__main__":
    unittest.main()
