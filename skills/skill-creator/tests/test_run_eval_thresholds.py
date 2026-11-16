import unittest
from concurrent.futures import Future
from pathlib import Path
from unittest.mock import patch

from scripts import run_eval


class ImmediateExecutor:
    def __init__(self, max_workers):
        self.max_workers = max_workers

    def __enter__(self):
        return self

    def __exit__(self, *args):
        return False

    def submit(self, function, query, *args):
        future = Future()
        future.set_result(function(query, *args))
        return future


class RunEvalThresholdTests(unittest.TestCase):
    def evaluate(self, **kwargs):
        eval_set = [
            {"query": "positive", "should_trigger": True},
            {"query": "negative", "should_trigger": False},
        ]
        run_counts = {}

        def trigger_half(query, *_):
            run_counts[query] = run_counts.get(query, 0) + 1
            return run_counts[query] % 2 == 1

        with patch.object(run_eval, "ProcessPoolExecutor", ImmediateExecutor), patch.object(
            run_eval, "run_single_query", side_effect=trigger_half
        ):
            return run_eval.run_eval(
                eval_set=eval_set,
                skill_name="example",
                description="example skill",
                num_workers=2,
                timeout=1,
                project_root=Path("."),
                runs_per_query=2,
                **kwargs,
            )

    def test_legacy_threshold_applies_to_both_query_kinds(self):
        results = self.evaluate(trigger_threshold=0.5)["results"]

        self.assertEqual([result["pass"] for result in results], [True, False])

    def test_separate_thresholds_control_positive_and_negative_queries(self):
        results = self.evaluate(
            trigger_threshold=0.5,
            should_trigger_threshold=0.5,
            should_not_trigger_threshold=0.75,
        )["results"]

        self.assertEqual([result["pass"] for result in results], [True, True])

    def test_positive_threshold_does_not_change_negative_threshold(self):
        results = self.evaluate(
            trigger_threshold=0.5,
            should_trigger_threshold=0.4,
            should_not_trigger_threshold=0.5,
        )["results"]

        self.assertEqual([result["pass"] for result in results], [True, False])


if __name__ == "__main__":
    unittest.main()
