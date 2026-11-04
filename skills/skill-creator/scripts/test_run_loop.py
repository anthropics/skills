"""Tests for skill-creator run_loop.select_best_iteration."""

import sys
from pathlib import Path

# run_loop uses `from scripts.X import ...`, so the skill-creator directory
# (parent of this scripts/ folder) must be on the path for the package import
# to resolve.
SKILL_CREATOR_DIR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SKILL_CREATOR_DIR))

from scripts.run_loop import select_best_iteration


def test_empty_history_returns_none():
    best, score = select_best_iteration([], has_test_set=False)
    assert best is None
    assert score == ""


def test_empty_history_with_test_set_returns_none():
    best, score = select_best_iteration([], has_test_set=True)
    assert best is None
    assert score == ""


def _iter(i, train_passed, train_total, test_passed=None, test_total=None):
    return {
        "iteration": i,
        "description": f"desc-{i}",
        "train_passed": train_passed,
        "train_total": train_total,
        "test_passed": test_passed,
        "test_total": test_total,
    }


def test_selects_highest_train_without_test_set():
    history = [
        _iter(1, 1, 3),
        _iter(2, 3, 3),
        _iter(3, 2, 3),
    ]
    best, score = select_best_iteration(history, has_test_set=False)
    assert best["iteration"] == 2
    assert score == "3/3"


def test_selects_highest_test_with_test_set():
    history = [
        _iter(1, 2, 3, test_passed=0, test_total=3),
        _iter(2, 1, 3, test_passed=2, test_total=3),
        _iter(3, 3, 3, test_passed=1, test_total=3),
    ]
    best, score = select_best_iteration(history, has_test_set=True)
    assert best["iteration"] == 2
    assert score == "2/3"


def test_handles_none_test_passed():
    """test_passed can be None when a test set exists but an iteration had no
    test results; the `or 0` fallback must not crash."""
    history = [
        _iter(1, 1, 3, test_passed=None, test_total=None),
        _iter(2, 2, 3, test_passed=2, test_total=3),
    ]
    best, score = select_best_iteration(history, has_test_set=True)
    assert best["iteration"] == 2
    assert score == "2/3"
