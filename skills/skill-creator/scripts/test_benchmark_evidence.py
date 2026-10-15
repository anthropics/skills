"""Regression tests for measured benchmark evidence and repetition counts."""

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from scripts.aggregate_benchmark import generate_benchmark, generate_markdown


class BenchmarkEvidenceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def run_fixture(self, eval_id, config, number=1, graded=True, pass_rate=1):
        directory = self.root / f"eval-{eval_id}" / config / f"run-{number}"
        directory.mkdir(parents=True)
        if graded:
            (directory / "grading.json").write_text(json.dumps({
                "summary": {"pass_rate": pass_rate}, "expectations": [],
            }), encoding="utf-8")

    def test_missing_baseline_is_error_and_preserves_existing_outputs(self):
        self.run_fixture(1, "with_skill")
        self.run_fixture(1, "without_skill", graded=False)
        output = self.root / "benchmark.json"
        output.write_text("previous evidence", encoding="utf-8")
        completed = subprocess.run([
            sys.executable, "-B", "-m", "scripts.aggregate_benchmark", str(self.root),
        ], capture_output=True, text=True)
        self.assertNotEqual(completed.returncode, 0)
        self.assertIn("without_skill", completed.stderr)
        self.assertEqual(output.read_text(), "previous evidence")
        self.assertFalse(output.with_suffix(".md").exists())

    def test_counts_actual_repetitions_per_eval_and_configuration(self):
        for eval_id in (1, 2):
            for config in ("with_skill", "without_skill"):
                self.run_fixture(eval_id, config, pass_rate=0)
        benchmark = generate_benchmark(self.root)
        self.assertEqual(benchmark["metadata"]["runs_per_configuration"], 1)
        self.assertIn("1 runs each per configuration", generate_markdown(benchmark))
        self.assertEqual(benchmark["run_summary"]["with_skill"]["pass_rate"]["mean"], 0)

    def test_uneven_repetitions_are_not_reported_as_uniform(self):
        for config in ("with_skill", "without_skill"):
            self.run_fixture(1, config)
        self.run_fixture(1, "with_skill", 2)
        benchmark = generate_benchmark(self.root)
        self.assertIsNone(benchmark["metadata"]["runs_per_configuration"])
        self.assertIn("variable runs per eval/configuration", generate_markdown(benchmark))

    def test_missing_eval_configuration_is_not_uniform(self):
        self.run_fixture(1, "with_skill")
        self.run_fixture(2, "without_skill")
        self.assertIsNone(generate_benchmark(self.root)["metadata"]["runs_per_configuration"])


if __name__ == "__main__":
    unittest.main()
