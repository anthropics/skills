"""Tests for skill-creator aggregate_benchmark.load_run_results."""

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from aggregate_benchmark import load_run_results, calculate_stats, aggregate_results


def _make_grading(passed=1, failed=1, total=2, pass_rate=0.5):
    return {"summary": {"pass_rate": pass_rate, "passed": passed, "failed": failed, "total": total}}


def test_malformed_run_dir_name_does_not_crash(tmp_path):
    """Regression: a run-* directory with a non-numeric suffix (e.g. run-bad)
    raised ValueError and aborted the whole aggregation. It should be skipped
    with a warning instead."""
    run_dir = tmp_path / "eval-1" / "with_skill" / "run-bad"
    run_dir.mkdir(parents=True)
    (run_dir / "grading.json").write_text(json.dumps(_make_grading()))

    good_dir = tmp_path / "eval-1" / "with_skill" / "run-1"
    good_dir.mkdir(parents=True)
    (good_dir / "grading.json").write_text(json.dumps(_make_grading()))

    results = load_run_results(tmp_path)
    # The good run is still picked up; the malformed one is skipped.
    assert "with_skill" in results
    assert len(results["with_skill"]) == 1
    assert results["with_skill"][0]["run_number"] == 1


def test_calculate_stats_empty():
    stats = calculate_stats([])
    assert stats == {"mean": 0.0, "stddev": 0.0, "min": 0.0, "max": 0.0}


def test_calculate_stats_single():
    stats = calculate_stats([5.0])
    assert stats["mean"] == 5.0
    assert stats["stddev"] == 0.0
    assert stats["min"] == 5.0
    assert stats["max"] == 5.0


def test_calculate_stats_multiple():
    stats = calculate_stats([1.0, 2.0, 3.0])
    assert stats["mean"] == 2.0
    assert stats["min"] == 1.0
    assert stats["max"] == 3.0
    assert stats["stddev"] > 0


def test_aggregate_results_empty():
    summary = aggregate_results({})
    assert "delta" in summary
