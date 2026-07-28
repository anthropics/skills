import contextlib
import io
import json
import tempfile
import unittest
from pathlib import Path

from aggregate_benchmark import load_run_results


def write_grading(path: Path, pass_rate: float) -> None:
    path.write_text(
        json.dumps({"summary": {
            "pass_rate": pass_rate,
            "passed": int(pass_rate * 10),
            "failed": int((1 - pass_rate) * 10),
            "total": 10,
        }}),
        encoding="utf-8",
    )


class AggregateBenchmarkTests(unittest.TestCase):
    def test_flat_single_run_layout_is_loaded_as_run_one(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            config = Path(temp_dir) / "eval-0" / "with_skill"
            config.mkdir(parents=True)
            write_grading(config / "grading.json", 0.8)

            results = load_run_results(Path(temp_dir))

            self.assertEqual(results["with_skill"][0]["run_number"], 1)
            self.assertEqual(results["with_skill"][0]["pass_rate"], 0.8)

    def test_nested_run_layout_remains_supported(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            run = Path(temp_dir) / "eval-0" / "without_skill" / "run-2"
            run.mkdir(parents=True)
            write_grading(run / "grading.json", 0.4)

            results = load_run_results(Path(temp_dir))

            self.assertEqual(results["without_skill"][0]["run_number"], 2)
            self.assertEqual(results["without_skill"][0]["pass_rate"], 0.4)

    def test_empty_configs_emit_a_visible_warning(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            (Path(temp_dir) / "eval-0" / "with_skill").mkdir(parents=True)
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                results = load_run_results(Path(temp_dir))

            self.assertEqual(results, {})
            self.assertIn("no grading.json files found", output.getvalue())


if __name__ == "__main__":
    unittest.main()
