"""Unit tests for check_benchmark_report.py."""
import json
import subprocess
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from tests.test_helpers import run_script

SCRIPT = Path(__file__).resolve().parent / "check_benchmark_report.py"
SCHEMA = Path(__file__).resolve().parent.parent / "shared" / "benchmark_report.schema.json"


def _valid_report() -> dict:
    return {
        "ars_version": "3.3.5",
        "task_definition": {
            "description": "Literature review on X",
            "task_type": "open-ended",
            "outcome_gradable": False,
        },
        "human_baseline": {
            "sample_size": 3,
            "author_independence": "third-party-conducted",
            "hours_spent": 20,
            "recruitment": "Posted on university mailing list",
            "tools_allowed": ["Google Scholar", "Zotero"],
        },
        "ars_run": {
            "hours_spent": 4,
            "cost_usd": 15.20,
            "skills_used": ["deep-research", "academic-paper"],
            "data_access_level_declared": "raw",
        },
        "metrics": {
            "primary_metric": "rubric_score_0_100",
            "primary_metric_value": 72,
            "scoring_independence": "blind-scored",
        },
        "caveats": ["Small baseline sample; single task type"],
    }


def _run(path: Path) -> subprocess.CompletedProcess:
    return run_script(SCRIPT, str(path))


class TestBenchmarkReport(unittest.TestCase):
    def test_valid_report_passes(self) -> None:
        with TemporaryDirectory() as tmp:
            p = Path(tmp) / "r.json"
            p.write_text(json.dumps(_valid_report()))
            result = _run(p)
            self.assertEqual(result.returncode, 0, msg=result.stderr + result.stdout)

    def test_missing_sample_size_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            r = _valid_report()
            del r["human_baseline"]["sample_size"]
            p = Path(tmp) / "r.json"
            p.write_text(json.dumps(r))
            result = _run(p)
            self.assertEqual(result.returncode, 1)
            self.assertIn("sample_size", result.stdout)

    def test_zero_sample_size_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            r = _valid_report()
            r["human_baseline"]["sample_size"] = 0
            p = Path(tmp) / "r.json"
            p.write_text(json.dumps(r))
            result = _run(p)
            self.assertEqual(result.returncode, 1)

    def test_empty_caveats_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            r = _valid_report()
            r["caveats"] = []
            p = Path(tmp) / "r.json"
            p.write_text(json.dumps(r))
            result = _run(p)
            self.assertEqual(result.returncode, 1)
            self.assertIn("caveats", result.stdout)

    def test_invalid_author_independence_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            r = _valid_report()
            r["human_baseline"]["author_independence"] = "unspecified"
            p = Path(tmp) / "r.json"
            p.write_text(json.dumps(r))
            result = _run(p)
            self.assertEqual(result.returncode, 1)

    def test_self_scored_passes_with_warning(self) -> None:
        with TemporaryDirectory() as tmp:
            r = _valid_report()
            r["metrics"]["scoring_independence"] = "self-scored"
            p = Path(tmp) / "r.json"
            p.write_text(json.dumps(r))
            result = _run(p)
            # Schema permits; script emits warning to stderr, exits 0.
            self.assertEqual(result.returncode, 0)
            self.assertIn("self-scored", result.stderr.lower() + result.stdout.lower())

    def test_empty_tools_allowed_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            r = _valid_report()
            r["human_baseline"]["tools_allowed"] = []
            p = Path(tmp) / "r.json"
            p.write_text(json.dumps(r))
            result = _run(p)
            self.assertEqual(result.returncode, 1)
            self.assertIn("tools_allowed", result.stdout)


if __name__ == "__main__":
    unittest.main()
