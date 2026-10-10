"""Regression tests for run_loop.split_eval_set.

Covers the degenerate-split bug: with a small eval set and holdout > 0, the
train split could come back empty (or missing a polarity class), which made
the optimization loop exit with "all_passed" on iteration 1 without testing
anything.
"""

import sys
from pathlib import Path

import pytest

SKILL_CREATOR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SKILL_CREATOR))

from scripts.run_loop import split_eval_set  # noqa: E402


def _eval_set(n_trigger: int, n_no_trigger: int) -> list[dict]:
    return [
        {"query": f"trigger-{i}", "should_trigger": True} for i in range(n_trigger)
    ] + [
        {"query": f"no-trigger-{i}", "should_trigger": False}
        for i in range(n_no_trigger)
    ]


def test_balanced_set_splits_both_classes() -> None:
    train, test = split_eval_set(_eval_set(3, 3), holdout=0.4)
    assert train and test
    assert any(e["should_trigger"] for e in train)
    assert any(not e["should_trigger"] for e in train)
    assert len(train) + len(test) == 6


def test_single_trigger_query_fails_loudly() -> None:
    with pytest.raises(ValueError, match="train split"):
        split_eval_set(_eval_set(1, 3), holdout=0.4)


def test_single_no_trigger_query_fails_loudly() -> None:
    with pytest.raises(ValueError, match="train split"):
        split_eval_set(_eval_set(3, 1), holdout=0.4)


def test_two_query_eval_set_fails_loudly() -> None:
    # 1 trigger + 1 no-trigger with the default holdout leaves an empty train
    # split — the loop used to report "all_passed" instead of failing.
    with pytest.raises(ValueError, match="train split"):
        split_eval_set(_eval_set(1, 1), holdout=0.4)


def test_empty_eval_set_fails_loudly() -> None:
    with pytest.raises(ValueError, match="empty"):
        split_eval_set([], holdout=0.4)
