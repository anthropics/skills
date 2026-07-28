import json
import tempfile
import unittest
from pathlib import Path

from aggregate_benchmark import load_run_results


def _write_grading(path: Path, pass_rate: float):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(
            {
                "summary": {
                    "pass_rate": pass_rate,
                    "passed": 1,
                    "failed": 0,
                    "total": 1,
                }
            }
        )
    )


class GradingLayoutTests(unittest.TestCase):
    def test_flat_single_run_layout_is_loaded(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _write_grading(root / "eval-0" / "with_skill" / "grading.json", 1.0)

            results = load_run_results(root)

        self.assertEqual(results["with_skill"][0]["run_number"], 1)
        self.assertEqual(results["with_skill"][0]["pass_rate"], 1.0)

    def test_nested_runs_keep_their_run_numbers(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _write_grading(root / "eval-0" / "with_skill" / "run-2" / "grading.json", 0.5)

            results = load_run_results(root)

        self.assertEqual(results["with_skill"][0]["run_number"], 2)
        self.assertEqual(results["with_skill"][0]["pass_rate"], 0.5)


if __name__ == "__main__":
    unittest.main()
