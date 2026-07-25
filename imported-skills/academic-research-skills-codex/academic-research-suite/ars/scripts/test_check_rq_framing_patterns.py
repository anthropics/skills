from __future__ import annotations

import subprocess
import sys
from pathlib import Path

from scripts import check_rq_framing_patterns as checker


REPO_ROOT = Path(__file__).resolve().parents[1]
WP_IDS = {f"WP{i:02d}" for i in range(1, 21)}


def _read(rel_path: str) -> str:
    return (REPO_ROOT / rel_path).read_text(encoding="utf-8")


def test_reference_pattern_set_has_twenty_ids() -> None:
    ids = [spec.pattern_id for spec in checker.REFERENCE_PATTERNS]
    assert len(ids) == 20
    assert set(ids) == WP_IDS


def test_detector_is_wording_only_on_smoke_cases() -> None:
    cliche = checker.analyze_framing("Exploring the impact of AI feedback on student motivation.")
    assert cliche["trigger_advisory"] is True
    assert "WP01" in cliche["matched_pattern_ids"]

    native = checker.analyze_framing(
        "Which cues do Taiwanese vocational students use when deciding whether a feedback comment is actionable?"
    )
    assert native["trigger_advisory"] is False
    assert native["matched_pattern_ids"] == []


def test_gold_set_calibration_passes_thresholds() -> None:
    result = checker.validate_gold_set()
    assert result["errors"] == []
    assert result["counts"] == {
        "tp": 20,
        "tn": 20,
        "fp": 0,
        "fn": 0,
        "positives": 20,
        "negatives": 20,
    }
    assert result["metrics"]["fnr"] < 0.30
    assert result["metrics"]["fpr"] < 0.20
    assert result["metrics"]["balanced_accuracy"] >= 0.75


def test_cli_reports_metrics() -> None:
    result = subprocess.run(
        [sys.executable, "-m", "scripts.check_rq_framing_patterns"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0, result.stderr
    assert "fnr=0.000" in result.stdout
    assert "fpr=0.000" in result.stdout
    assert "balanced_accuracy=1.000" in result.stdout


def test_socratic_agents_define_wording_pattern_advisory() -> None:
    for rel_path in (
        "deep-research/agents/socratic_mentor_agent.md",
        "academic-paper/agents/socratic_mentor_agent.md",
    ):
        text = _read(rel_path)
        assert "## Wording-Pattern Advisory (Kong #257)" in text
        assert "WORDING_PATTERN_ADVISORY" in text
        assert "surface phrasing only" in text
        assert "not about idea quality" in text
        assert "Do not generate alternative ideas" in text
        for pattern_id in WP_IDS:
            assert pattern_id in text, f"{rel_path} missing {pattern_id}"


def test_lit_review_agents_define_distributional_skew_advisory() -> None:
    for rel_path in (
        "deep-research/agents/bibliography_agent.md",
        "academic-paper/agents/literature_strategist_agent.md",
    ):
        text = _read(rel_path)
        assert "Distributional Skew Advisory (Kong #257)" in text
        assert "DISTRIBUTIONAL_SKEW_ADVISORY" in text
        assert ">= 70%" in text
        assert "time distribution" in text
        assert "geographic distribution" in text
        assert "methodological distribution" in text
        assert "venue tier distribution" in text
        assert "uncovered_topics" in text
        assert "never blocks" in text


def test_example_and_design_doc_cover_boundaries() -> None:
    example = _read("deep-research/examples/idea_diversity_coverage_gap_advisory.md")
    assert "WORDING_PATTERN_ADVISORY" in example
    assert "DISTRIBUTIONAL_SKEW_ADVISORY" in example
    assert "not say the idea is generic or bad" in example

    design = _read("docs/design/2026-05-28-kong-257-idea-diversity-coverage-gap-advisory.md")
    assert "## #134 Boundary" in design
    assert "What mode should we be in?" in design
    assert "Does this proposed RQ wording resemble an AI-typical shell?" in design
    assert "FNR < 0.30" in design
    assert "FPR < 0.20" in design
    assert "balanced accuracy >= 0.75" in design
