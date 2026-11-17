"""Regression tests for aggregate_benchmark.py.

Covers the fabricated-delta bug: with only a single configuration of runs
(e.g. only with_skill, which the loader supports), aggregate_results()
previously emitted a "delta" against an invented zero baseline, so
benchmark reports claimed a pass-rate/time/token improvement that no
comparison supported.
"""

import sys
from pathlib import Path

import pytest

SKILL_CREATOR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SKILL_CREATOR))

from scripts.aggregate_benchmark import aggregate_results, generate_markdown  # noqa: E402


def _run(pass_rate: float, time_seconds: float = 45.0, tokens: int = 3800) -> dict:
    return {
        "eval_id": 1,
        "run_number": 1,
        "pass_rate": pass_rate,
        "passed": 8,
        "failed": 2,
        "total": 10,
        "time_seconds": time_seconds,
        "tokens": tokens,
        "tool_calls": 18,
        "errors": 0,
        "expectations": [],
        "notes": [],
    }


def _benchmark(run_summary: dict) -> dict:
    return {
        "metadata": {
            "skill_name": "docx",
            "executor_model": "m",
            "timestamp": "t",
            "evals_run": [1],
            "runs_per_configuration": 1,
        },
        "run_summary": run_summary,
        "notes": [],
    }


def test_single_config_has_no_delta() -> None:
    summary = aggregate_results({"with_skill": [_run(0.80)]})
    assert "delta" not in summary
    assert summary["with_skill"]["pass_rate"]["mean"] == pytest.approx(0.80)


def test_single_config_markdown_omits_delta_column() -> None:
    summary = aggregate_results({"with_skill": [_run(0.80)]})
    markdown = generate_markdown(_benchmark(summary))
    assert "Delta" not in markdown
    assert "Config B" not in markdown
    assert "+0.80" not in markdown
    assert "80% ± 0%" in markdown


def test_two_configs_still_report_delta() -> None:
    summary = aggregate_results(
        {
            "with_skill": [_run(0.85), _run(0.71)],
            "without_skill": [_run(0.35, time_seconds=32.0, tokens=2100)],
        }
    )
    assert summary["delta"] == {
        "pass_rate": "+0.43",
        "time_seconds": "+13.0",
        "tokens": "+1700",
    }
    markdown = generate_markdown(_benchmark(summary))
    assert "| Metric | With Skill | Without Skill | Delta |" in markdown
    assert "+0.43" in markdown
