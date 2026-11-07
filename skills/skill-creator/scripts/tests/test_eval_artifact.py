"""Regression tests for the trigger-eval artifact itself.

These tests pin the core invariant behind #1298: auto-trigger evaluation must
install the candidate as a real skill, not as a slash-command decoy. If this
regresses back to `.claude/commands`, the harness can once again measure a
surface that is not present in Claude Code's model-facing skill registry.
"""

import shutil
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts.run_eval import create_eval_project


class EvalArtifactTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name) / "eval-root"
        self.home = Path(self.tmp.name) / "home"
        self.home.mkdir(parents=True)

        self.root_patch = mock.patch(
            "scripts.run_eval.EVAL_PROJECTS_ROOT", self.root
        )
        self.home_patch = mock.patch(
            "scripts.run_eval.Path.home", return_value=self.home
        )
        self.root_patch.start()
        self.home_patch.start()

    def tearDown(self):
        self.home_patch.stop()
        self.root_patch.stop()
        self.tmp.cleanup()

    def _create(self, name="pdf", description="Handle PDF documents") -> Path:
        project = create_eval_project(name, description, stale_hours=12.0)
        self.addCleanup(shutil.rmtree, project, ignore_errors=True)
        return project

    def test_candidate_is_installed_as_real_skill(self):
        project = self._create()

        skill_file = project / ".claude" / "skills" / "pdf" / "SKILL.md"
        self.assertTrue(skill_file.is_file())
        self.assertFalse((project / ".claude" / "commands").exists())

    def test_eval_skill_keeps_real_name_and_description(self):
        project = self._create(description="Rate PDF files accurately")
        text = (
            project / ".claude" / "skills" / "pdf" / "SKILL.md"
        ).read_text()

        self.assertIn("name: pdf", text)
        self.assertIn("description: |", text)
        self.assertIn("Rate PDF files accurately", text)
        self.assertNotIn("pdf-skill-", text)
        self.assertNotIn("pdf-eval-", text)

    def test_parallel_runs_get_distinct_project_roots(self):
        first = self._create()
        second = self._create()

        self.assertNotEqual(first, second)
        self.assertEqual(first.parent, self.root)
        self.assertEqual(second.parent, self.root)
        self.assertTrue(
            (first / ".claude" / "skills" / "pdf" / "SKILL.md").exists()
        )
        self.assertTrue(
            (second / ".claude" / "skills" / "pdf" / "SKILL.md").exists()
        )

    def test_artifact_is_never_written_into_callers_project(self):
        caller = Path(self.tmp.name) / "caller-project"
        caller.mkdir()

        project = self._create()

        self.assertNotEqual(project, caller)
        self.assertFalse((caller / ".claude").exists())


if __name__ == "__main__":
    unittest.main()
