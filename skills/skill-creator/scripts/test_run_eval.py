"""Regression tests for trigger evaluation input handling."""

import unittest
from concurrent.futures import Future
from pathlib import Path
from unittest.mock import patch

from scripts import run_eval


class CompletedExecutor:
    submitted = 0

    def __init__(self, max_workers):
        pass

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        pass

    def submit(self, *args):
        type(self).submitted += 1
        future = Future()
        future.set_result(True)
        return future


class RunEvalTests(unittest.TestCase):
    def setUp(self):
        CompletedExecutor.submitted = 0

    def test_duplicate_queries_are_rejected_before_running_workers(self):
        eval_set = [
            {"query": "same prompt", "should_trigger": True},
            {"query": "same prompt", "should_trigger": False},
        ]

        with patch.object(run_eval, "ProcessPoolExecutor", CompletedExecutor):
            with self.assertRaisesRegex(ValueError, "Duplicate eval query"):
                run_eval.run_eval(eval_set, "example", "description", 2, 30, Path.cwd())

        self.assertEqual(CompletedExecutor.submitted, 0)

    def test_distinct_queries_keep_separate_results(self):
        eval_set = [
            {"query": "first prompt", "should_trigger": True},
            {"query": "second prompt", "should_trigger": False},
        ]

        with patch.object(run_eval, "ProcessPoolExecutor", CompletedExecutor):
            output = run_eval.run_eval(eval_set, "example", "description", 2, 30, Path.cwd())

        self.assertEqual(output["summary"]["total"], 2)
        self.assertEqual(CompletedExecutor.submitted, 2)


if __name__ == "__main__":
    unittest.main()
