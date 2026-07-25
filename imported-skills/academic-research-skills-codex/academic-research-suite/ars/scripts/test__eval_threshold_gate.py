"""Tests for scripts/_eval_threshold_gate.py (#184 Delta 3 / Fix 1; #328 per-class gate).

The absolute-threshold gate must fail a PR when ANY declared binding threshold
regresses — aggregate OR per-class. Manifests declare both (e.g.
citation_extraction: aggregate accuracy >= 0.90 AND per_class accuracy >= 0.85),
run_evals stamps ``per_class[].passed`` against the per-class threshold, and the
gate must honour it. #328: the gate previously inspected only the aggregate, so a
per-class-fail-but-aggregate-pass report passed the gate when it should block.
"""
from __future__ import annotations

from scripts import _eval_threshold_gate as gate


def _task(task_name="citation_extraction", agg_metric="accuracy",
          agg_passed=True, per_class=None, status="measured"):
    entry = {
        "task_name": task_name,
        "status": status,
        "aggregate_metric": {"metric": agg_metric, "passed": agg_passed},
    }
    if per_class is not None:
        entry["per_class"] = per_class
    return entry


def _report(*tasks):
    return {"per_task": list(tasks)}


# ---------------------------------------------------------------------------
# Aggregate gate (pre-#328 behaviour, must stay)
# ---------------------------------------------------------------------------
def test_aggregate_pass_no_failure():
    assert gate.failed_tasks(_report(_task(agg_passed=True))) == []


def test_aggregate_fail_reported():
    assert gate.failed_tasks(_report(_task(agg_passed=False))) == [
        "citation_extraction.aggregate.accuracy"
    ]


def test_no_threshold_not_gated():
    # aggregate without a ``passed`` key (task declares no threshold) is not gated
    t = {"task_name": "t", "status": "measured", "aggregate_metric": {"metric": "accuracy"}}
    assert gate.failed_tasks(_report(t)) == []


def test_pending_task_never_gated():
    assert gate.failed_tasks(_report(_task(status="pending", agg_passed=False))) == []


def test_unknown_nonmeasured_status_never_gated():
    # symmetric with the lift gate: a future non-measured status is skipped, not gated
    assert gate.failed_tasks(_report(_task(status="error", agg_passed=False))) == []


def test_missing_status_treated_as_measured():
    # back-compat: a task with no status key is gated (pre-status reports stay valid)
    t = {"task_name": "t", "aggregate_metric": {"metric": "accuracy", "passed": False}}
    assert gate.failed_tasks(_report(t)) == ["t.aggregate.accuracy"]


# ---------------------------------------------------------------------------
# Per-class gate (#328 — the hole)
# ---------------------------------------------------------------------------
def test_per_class_fail_with_aggregate_pass_is_reported():
    """The #328 regression case: aggregate passes, a binding per-class fails.

    e.g. citation_extraction.false.accuracy drops below 0.85 while the aggregate
    stays >= 0.90. The gate MUST surface it.
    """
    report = _report(_task(
        agg_passed=True,
        per_class=[
            {"class_name": "true", "metric": "accuracy", "passed": True},
            {"class_name": "false", "metric": "accuracy", "passed": False},
            {"class_name": "unresolvable", "metric": "accuracy", "passed": True},
        ],
    ))
    assert gate.failed_tasks(report) == ["citation_extraction.false.accuracy"]


def test_per_class_key_shape_matches_lift_gate():
    """Per-class failures use the ``<task>.<class>.<metric>`` shape (matches the
    lift gate's key shape, not the aggregate's ``<task>.aggregate.<metric>``)."""
    report = _report(_task(
        task_name="rq_framing_patterns", agg_metric="balanced_accuracy",
        agg_passed=True,
        per_class=[
            {"class_name": "fnr", "metric": "fnr", "passed": False},
            {"class_name": "fpr", "metric": "fpr", "passed": True},
        ],
    ))
    assert gate.failed_tasks(report) == ["rq_framing_patterns.fnr.fnr"]


def test_both_aggregate_and_per_class_fail_reported():
    report = _report(_task(
        agg_passed=False,
        per_class=[{"class_name": "false", "metric": "accuracy", "passed": False}],
    ))
    assert gate.failed_tasks(report) == [
        "citation_extraction.aggregate.accuracy",
        "citation_extraction.false.accuracy",
    ]


def test_per_class_without_threshold_not_gated():
    # a per_class row that carries no ``passed`` key (no per-class threshold) is
    # not gated — only ``passed is False`` blocks
    report = _report(_task(
        agg_passed=True,
        per_class=[{"class_name": "true", "metric": "accuracy"}],
    ))
    assert gate.failed_tasks(report) == []


def test_per_class_on_pending_task_never_gated():
    report = _report(_task(
        status="pending", agg_passed=True,
        per_class=[{"class_name": "false", "metric": "accuracy", "passed": False}],
    ))
    assert gate.failed_tasks(report) == []
