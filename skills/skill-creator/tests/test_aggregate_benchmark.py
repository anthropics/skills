"""Tests for skills/skill-creator/scripts/aggregate_benchmark.py.

Covers issue #518: eval-directory discovery must not depend on the eval-*
name prefix, non-directory entries must never crash the loader, misplaced
grading files must warn instead of vanishing silently, and variant
expectation field names must be mapped to the standard schema.

Run with: python -m unittest tests.test_aggregate_benchmark -v
from the skills/skill-creator directory (or python3 the file directly).
"""

import io
import json
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import importlib.util

_SCRIPT = Path(__file__).resolve().parent.parent / "scripts" / "aggregate_benchmark.py"
_spec = importlib.util.spec_from_file_location("aggregate_benchmark", _SCRIPT)
agg = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(agg)


def grading(pass_rate=1.0, expectations=None):
    return {
        "summary": {"pass_rate": pass_rate, "passed": 1, "failed": 0, "total": 1},
        "expectations": expectations
        if expectations is not None
        else [{"text": "criterion", "passed": True, "evidence": "ev"}],
        "timing": {"total_duration_seconds": 10.0},
        "execution_metrics": {
            "total_tool_calls": 3,
            "output_chars": 100,
            "errors_encountered": 0,
        },
    }


def write(path: Path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    if isinstance(obj, str):
        path.write_text(obj)
    else:
        path.write_text(json.dumps(obj))


class AggregateBenchmarkTest(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.root = Path(self._tmp.name)

    def tearDown(self):
        self._tmp.cleanup()

    def bench(self, name="bench"):
        path = self.root / name
        path.mkdir(parents=True)
        return path

    def std_runs(self, bench, eval_name, cfgs=("with_skill", "without_skill")):
        for cfg in cfgs:
            write(bench / eval_name / cfg / "run-1" / "grading.json", grading())

    def load(self, bench):
        out = io.StringIO()
        with redirect_stdout(out):
            results = agg.load_run_results(bench)
        return results, out.getvalue()

    def test_descriptive_only_dirs_are_discovered(self):
        """Issue item 3: descriptive eval names must not be silently dropped."""
        bench = self.bench()
        self.std_runs(bench, "group-membership-check")
        self.std_runs(bench, "role-assignment-list")
        results, _ = self.load(bench)
        self.assertEqual(sorted(results), ["with_skill", "without_skill"])
        self.assertEqual(len(results["with_skill"]), 2)
        self.assertEqual(len(results["without_skill"]), 2)

    def test_root_file_matching_eval_glob_does_not_crash(self):
        """Issue item 4 (eval level): a stray file must be skipped, not iterated."""
        bench = self.bench()
        self.std_runs(bench, "eval-0")
        write(bench / "eval-notes.txt", "notes")
        results, _ = self.load(bench)
        self.assertEqual(len(results["with_skill"]), 1)

    def test_stray_file_inside_eval_dir_is_skipped(self):
        """Issue item 4 (config level): files among config dirs are skipped."""
        bench = self.bench()
        self.std_runs(bench, "eval-0")
        write(bench / "eval-0" / "screenshot.png", "fake-png")
        results, _ = self.load(bench)
        self.assertEqual(len(results["with_skill"]), 1)

    def test_legacy_runs_layout_still_works(self):
        bench = self.bench()
        self.std_runs(bench / "runs", "eval-0")
        results, _ = self.load(bench)
        self.assertEqual(len(results["with_skill"]), 1)
        self.assertEqual(len(results["without_skill"]), 1)

    def test_runs_layout_takes_precedence_over_direct_dirs(self):
        bench = self.bench()
        self.std_runs(bench / "runs", "eval-0")
        self.std_runs(bench, "eval-1")
        results, _ = self.load(bench)
        # Only the runs/ eval is read; the direct eval-1 is ignored.
        self.assertEqual(len(results["with_skill"]), 1)
        self.assertEqual(results["with_skill"][0]["eval_id"], 0)

    def test_eval_prefixed_descriptive_name_is_a_regression_guard(self):
        bench = self.bench()
        self.std_runs(bench, "eval-group-check")
        results, _ = self.load(bench)
        self.assertEqual(len(results["with_skill"]), 1)

    def test_config_level_grading_json_is_skipped_with_warning(self):
        """Direct grading.json without run-* dirs is not read by this script
        (that layout belongs to open #1661/#1453); it must warn, not vanish."""
        bench = self.bench()
        write(bench / "eval-0" / "with_skill" / "grading.json", grading())
        results, output = self.load(bench)
        self.assertEqual(results, {})
        self.assertIn("no run-* subdirectories", output)

    def test_eval_root_grading_json_warns_and_is_ignored(self):
        """Issue item 1: a grading file at the eval root must warn; the
        valid run next to it must still be read."""
        bench = self.bench()
        self.std_runs(bench, "eval-0")
        write(bench / "eval-0" / "grading.json", grading())
        results, output = self.load(bench)
        self.assertEqual(len(results["with_skill"]), 1)
        self.assertIn("eval directory root", output)

    def test_variant_expectation_fields_are_mapped(self):
        """Issue item 5: name/met/details must map to text/passed/evidence
        with a warning, instead of showing empty cells."""
        bench = self.bench()
        self.std_runs(bench, "eval-0", cfgs=("with_skill",))
        write(
            bench / "eval-0" / "with_skill" / "run-1" / "grading.json",
            grading(expectations=[{"name": "criterion", "met": True, "details": "ev"}]),
        )
        results, output = self.load(bench)
        exp = results["with_skill"][0]["expectations"][0]
        self.assertEqual(exp["text"], "criterion")
        self.assertTrue(exp["passed"])
        self.assertEqual(exp["evidence"], "ev")
        self.assertIn("variant", output)

    def test_variant_non_boolean_met_is_not_mapped(self):
        bench = self.bench()
        self.std_runs(bench, "eval-0", cfgs=("with_skill",))
        write(
            bench / "eval-0" / "with_skill" / "run-1" / "grading.json",
            grading(expectations=[{"name": "criterion", "met": "yes", "details": "ev"}]),
        )
        results, output = self.load(bench)
        exp = results["with_skill"][0]["expectations"][0]
        self.assertEqual(exp["text"], "criterion")
        self.assertNotIn("passed", exp)
        self.assertIn("missing required fields", output)

    def test_non_numeric_run_dir_is_skipped_with_warning(self):
        """Same name-assumption bug class as item 4: run-abc must not crash."""
        bench = self.bench()
        self.std_runs(bench, "eval-0", cfgs=("with_skill",))
        write(bench / "eval-0" / "with_skill" / "run-abc" / "grading.json", grading())
        results, output = self.load(bench)
        self.assertEqual(len(results["with_skill"]), 1)
        self.assertEqual(results["with_skill"][0]["run_number"], 1)
        self.assertIn("non-numeric run directory", output)

    def test_empty_benchmark_dir_returns_empty(self):
        bench = self.bench()
        results, output = self.load(bench)
        self.assertEqual(results, {})
        self.assertIn("No eval directories found", output)

    def test_eval_dir_with_only_inputs_is_not_discovered(self):
        bench = self.bench()
        (bench / "notes" / "inputs").mkdir(parents=True)
        results, output = self.load(bench)
        self.assertEqual(results, {})
        self.assertIn("No eval directories found", output)

    def test_metadata_eval_id_is_preserved(self):
        bench = self.bench()
        self.std_runs(bench, "eval-5")
        write(bench / "eval-5" / "eval_metadata.json", {"eval_id": 42})
        results, _ = self.load(bench)
        self.assertEqual(
            sorted(r["eval_id"] for r in results["with_skill"]), [42]
        )

    def test_descriptive_eval_id_falls_back_to_index(self):
        bench = self.bench()
        self.std_runs(bench, "group-membership-check")
        results, _ = self.load(bench)
        # Sorted first, so the single descriptive eval gets index 0.
        self.assertEqual(results["with_skill"][0]["eval_id"], 0)

    def test_end_to_end_benchmark_on_descriptive_fixture(self):
        bench = self.bench()
        self.std_runs(bench, "group-membership-check")
        out = io.StringIO()
        with redirect_stdout(out):
            benchmark = agg.generate_benchmark(bench, "demo-skill", "/tmp/demo")
        self.assertEqual(len(benchmark["runs"]), 2)
        self.assertEqual(benchmark["run_summary"]["delta"]["pass_rate"], "+0.00")


if __name__ == "__main__":
    unittest.main()
