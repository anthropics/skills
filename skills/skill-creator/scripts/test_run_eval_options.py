"""Regression tests for eval options that can produce false success."""

import unittest
from pathlib import Path

from scripts.run_eval import run_eval


class RunEvalOptionTests(unittest.TestCase):
    def test_zero_runs_cannot_report_an_empty_success(self):
        eval_set = [{"query": "use the skill", "should_trigger": True}]

        with self.assertRaisesRegex(ValueError, "runs_per_query must be positive"):
            run_eval(eval_set, "example", "description", 1, 30, Path.cwd(), runs_per_query=0)

    def test_negative_runs_are_rejected(self):
        eval_set = [{"query": "use the skill", "should_trigger": True}]

        with self.assertRaisesRegex(ValueError, "runs_per_query must be positive"):
            run_eval(eval_set, "example", "description", 1, 30, Path.cwd(), runs_per_query=-2)


if __name__ == "__main__":
    unittest.main()
