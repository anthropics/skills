"""CLI regressions for benchmark timing and token selection (standard library only)."""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).resolve().parents[1] / "skills/skill-creator/scripts/aggregate_benchmark.py"


class BenchmarkTimingTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def write_run(self, config="with_skill", *, legacy=False, duration=191.0,
                  chars=12450, timing=None):
        parent = self.root / "runs" if legacy else self.root
        run = parent / "eval-1" / config / "run-1"
        run.mkdir(parents=True)
        grading = {
            "summary": {"passed": 1, "failed": 0, "total": 1, "pass_rate": 1.0},
            "execution_metrics": {"output_chars": chars, "total_tool_calls": 2},
            "timing": {"total_duration_seconds": duration},
        }
        (run / "grading.json").write_text(json.dumps(grading), encoding="utf-8")
        if timing is not None:
            (run / "timing.json").write_text(timing, encoding="utf-8")
        return run

    def aggregate(self):
        inputs = {path: path.read_bytes() for path in self.root.rglob("*.json") if path.is_file()}
        env = dict(os.environ, PYTHONUTF8="1")
        result = subprocess.run(
            [sys.executable, str(SCRIPT), str(self.root), "--skill-name", "test"],
            capture_output=True, text=True, encoding="utf-8", env=env, timeout=15,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        for path, content in inputs.items():
            self.assertEqual(path.read_bytes(), content, str(path))
        benchmark = json.loads((self.root / "benchmark.json").read_text(encoding="utf-8"))
        markdown = (self.root / "benchmark.md").read_text(encoding="utf-8")
        return benchmark, markdown

    def assert_recorded_tokens(self, legacy):
        self.write_run(legacy=legacy, timing=json.dumps({
            "total_tokens": 84852, "total_duration_seconds": 23.3,
        }))
        benchmark, markdown = self.aggregate()
        result = benchmark["runs"][0]["result"]
        self.assertEqual(result["tokens"], 84852)
        self.assertEqual(result["time_seconds"], 191.0)
        self.assertEqual(result["tool_calls"], 2)
        self.assertEqual(benchmark["run_summary"]["with_skill"]["tokens"]["mean"], 84852)
        self.assertIn("| Tokens | 84852", markdown)

    def test_recorded_tokens_with_existing_duration(self):
        self.assert_recorded_tokens(legacy=False)

    def test_recorded_tokens_in_legacy_layout(self):
        self.assert_recorded_tokens(legacy=True)

    def test_comparison_uses_tokens_not_output_characters(self):
        self.write_run(timing='{"total_tokens": 84852}')
        self.write_run("without_skill", chars=20000, timing='{"total_tokens": 30000}')
        benchmark, markdown = self.aggregate()
        self.assertEqual(benchmark["run_summary"]["delta"]["tokens"], "+54852")
        self.assertIn("| Tokens | 84852", markdown)
        self.assertIn("| +54852 |", markdown)

    def test_duration_falls_back_to_timing_file(self):
        self.write_run(duration=0, timing='{"total_tokens": 84852, "total_duration_seconds": 23.3}')
        benchmark, _ = self.aggregate()
        self.assertEqual(benchmark["runs"][0]["result"]["time_seconds"], 23.3)
        self.assertEqual(benchmark["runs"][0]["result"]["tokens"], 84852)

    def test_missing_timing_file_keeps_existing_fallback(self):
        self.write_run()
        benchmark, _ = self.aggregate()
        self.assertEqual(benchmark["runs"][0]["result"]["tokens"], 12450)
        self.assertEqual(benchmark["runs"][0]["result"]["time_seconds"], 191.0)

    def test_invalid_timing_json_keeps_existing_fallback(self):
        self.write_run(timing="{invalid")
        benchmark, _ = self.aggregate()
        self.assertEqual(benchmark["runs"][0]["result"]["tokens"], 12450)
        self.assertEqual(benchmark["runs"][0]["result"]["time_seconds"], 191.0)

    def test_missing_token_count_keeps_existing_fallback(self):
        self.write_run(timing='{"total_duration_seconds": 23.3}')
        benchmark, _ = self.aggregate()
        self.assertEqual(benchmark["runs"][0]["result"]["tokens"], 12450)
        self.assertEqual(benchmark["runs"][0]["result"]["time_seconds"], 191.0)

    def test_non_object_timing_keeps_fallback(self):
        self.write_run(timing="null")
        benchmark, _ = self.aggregate()
        self.assertEqual(benchmark["runs"][0]["result"]["tokens"], 12450)
        self.assertEqual(benchmark["runs"][0]["result"]["time_seconds"], 191.0)

    def test_unreadable_timing_path_keeps_fallback(self):
        run = self.write_run()
        (run / "timing.json").mkdir()
        benchmark, _ = self.aggregate()
        self.assertEqual(benchmark["runs"][0]["result"]["tokens"], 12450)
        self.assertEqual(benchmark["runs"][0]["result"]["time_seconds"], 191.0)

    def test_invalid_timing_encoding_keeps_fallback(self):
        run = self.write_run()
        (run / "timing.json").write_bytes(b"\xff")
        benchmark, _ = self.aggregate()
        self.assertEqual(benchmark["runs"][0]["result"]["tokens"], 12450)
        self.assertEqual(benchmark["runs"][0]["result"]["time_seconds"], 191.0)

    def test_zero_token_count_keeps_existing_fallback(self):
        self.write_run(timing='{"total_tokens": 0}')
        benchmark, _ = self.aggregate()
        self.assertEqual(benchmark["runs"][0]["result"]["tokens"], 12450)


if __name__ == "__main__":
    unittest.main()
