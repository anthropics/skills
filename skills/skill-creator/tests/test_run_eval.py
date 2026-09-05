import sys
import unittest
from pathlib import Path


SKILL_CREATOR_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SKILL_CREATOR_ROOT))

from scripts.run_eval import aggregate_results


class AggregateResultsTest(unittest.TestCase):
    def setUp(self):
        self.items = {
            "positive": {"query": "positive", "should_trigger": True},
            "negative": {"query": "negative", "should_trigger": False},
        }

    def test_completed_outcomes_are_scored_normally(self):
        results, summary = aggregate_results(
            query_triggers={"positive": [True], "negative": [False]},
            query_items=self.items,
            query_errors={},
            trigger_threshold=0.5,
        )

        self.assertEqual([result["pass"] for result in results], [True, True])
        self.assertEqual(summary, {"total": 2, "passed": 2, "failed": 0, "errored": 0})

    def test_error_does_not_become_passing_negative_outcome(self):
        results, summary = aggregate_results(
            query_triggers={"positive": [True], "negative": []},
            query_items=self.items,
            query_errors={"negative": 1},
            trigger_threshold=0.5,
        )

        negative = results[1]
        self.assertIsNone(negative["trigger_rate"])
        self.assertEqual(negative["runs"], 0)
        self.assertEqual(negative["errored"], 1)
        self.assertFalse(negative["pass"])
        self.assertEqual(summary, {"total": 2, "passed": 1, "failed": 1, "errored": 1})

    def test_partial_error_fails_closed_without_changing_denominator(self):
        results, summary = aggregate_results(
            query_triggers={"positive": [True], "negative": [False]},
            query_items=self.items,
            query_errors={"negative": 1},
            trigger_threshold=0.5,
        )

        negative = results[1]
        self.assertEqual(negative["trigger_rate"], 0.0)
        self.assertEqual(negative["runs"], 1)
        self.assertEqual(negative["errored"], 1)
        self.assertFalse(negative["pass"])
        self.assertEqual(summary["errored"], 1)


if __name__ == "__main__":
    unittest.main()
