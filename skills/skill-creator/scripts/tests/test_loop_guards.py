"""Offline tests for the optimize loop's degenerate-run guards.

A run that exits before the first eval (e.g. --max-iterations 0) once crashed
on max([]); these pin that it returns cleanly instead. No `claude` subprocess
and no API cost — with zero iterations run_loop never spawns an eval. Run from
the skill-creator directory:

    python -m unittest scripts.tests.test_loop_guards
"""

import tempfile
import unittest
from pathlib import Path

from scripts.generate_report import generate_html
from scripts.run_loop import run_loop


class TestDegenerateLoop(unittest.TestCase):
    def _skill_dir(self) -> Path:
        d = Path(tempfile.mkdtemp())
        (d / "SKILL.md").write_text("---\nname: pdf\ndescription: test\n---\n\n# pdf\n")
        return d

    def test_run_loop_zero_iterations_returns_cleanly(self):
        # --max-iterations 0 exits before any eval, leaving history empty;
        # the loop must return the original description, not raise on max([]).
        out = run_loop(
            eval_set=[{"query": "q", "should_trigger": True}],
            skill_path=self._skill_dir(),
            description_override=None,
            num_workers=1, timeout=1, max_iterations=0, runs_per_query=1,
            trigger_threshold=0.5, holdout=0, model="unused", verbose=False,
        )
        self.assertEqual(out["iterations_run"], 0)
        self.assertEqual(out["best_description"], "test")

    def test_generate_html_empty_history(self):
        html = generate_html({"history": [], "original_description": "test"})
        self.assertIn("Skill Description Optimization", html)


if __name__ == "__main__":
    unittest.main()
