"""Tests for skill-creator generate_report.generate_html."""

from generate_report import generate_html


def test_empty_history_does_not_crash():
    """Regression: generate_html used to call max() on an empty history list,
    raising ValueError. An empty history (e.g. run_loop produced no iterations)
    should render an empty report instead of crashing."""
    data = {
        "history": [],
        "original_description": "orig",
        "best_description": "best",
        "best_score": "1/1",
    }
    html_out = generate_html(data)
    assert "<table>" in html_out
    assert "Skill Description Optimization" in html_out


def test_single_iteration_with_train_results():
    data = {
        "history": [
            {
                "iteration": 1,
                "description": "a description",
                "train_passed": 2,
                "train_total": 3,
                "results": [
                    {"query": "do thing", "should_trigger": True, "pass": True, "triggers": 3, "runs": 3},
                    {"query": "other", "should_trigger": False, "pass": False, "triggers": 1, "runs": 3},
                ],
            }
        ],
        "original_description": "orig",
        "best_description": "a description",
        "best_score": "2/3",
    }
    html_out = generate_html(data)
    assert "do thing" in html_out
    assert "a description" in html_out


def test_iteration_with_test_results_highlights_best():
    data = {
        "history": [
            {
                "iteration": 1,
                "description": "v1",
                "train_passed": 1,
                "train_total": 2,
                "test_passed": 0,
                "test_total": 2,
                "train_results": [
                    {"query": "q1", "should_trigger": True, "pass": True, "triggers": 2, "runs": 2},
                ],
                "test_results": [
                    {"query": "tq1", "should_trigger": True, "pass": False, "triggers": 0, "runs": 2},
                ],
            },
            {
                "iteration": 2,
                "description": "v2",
                "train_passed": 2,
                "train_total": 2,
                "test_passed": 2,
                "test_total": 2,
                "train_results": [
                    {"query": "q1", "should_trigger": True, "pass": True, "triggers": 2, "runs": 2},
                ],
                "test_results": [
                    {"query": "tq1", "should_trigger": True, "pass": True, "triggers": 2, "runs": 2},
                ],
            },
        ],
        "original_description": "orig",
        "best_description": "v2",
        "best_score": "2/2",
    }
    html_out = generate_html(data)
    # best row (iteration 2) should be highlighted
    assert "best-row" in html_out
    assert "tq1" in html_out
