"""Tests for scripts/check_ranking_lift.py (#184 Delta 4 lift gate).

The OPEN-issue check is always monkeypatched; no test touches the network.
"""
from __future__ import annotations

import pytest

from scripts import check_ranking_lift as crl


# ---------------------------------------------------------------------------
# compute_signed_lift pure function: 6 polarity/zero combos
# ---------------------------------------------------------------------------
@pytest.mark.parametrize(
    "baseline,compare,direction,expected",
    [
        # higher_is_better
        (0.80, 0.90, "higher_is_better", 0.125),    # improvement
        (0.80, 0.40, "higher_is_better", -0.5),     # regression
        # lower_is_better (FNR): improvement when compare DROPS
        (0.40, 0.20, "lower_is_better", 0.5),       # FNR halved -> positive lift
        (0.20, 0.40, "lower_is_better", -1.0),      # FNR doubled -> negative lift
        # zero-baseline
        (0.0, 0.10, "higher_is_better", "+inf"),    # improved from 0
        (0.0, 0.0, "higher_is_better", 0.0),        # unchanged at 0
    ],
)
def test_compute_signed_lift_combos(baseline, compare, direction, expected):
    got = crl.compute_signed_lift(baseline, compare, direction)
    if isinstance(expected, str):
        assert got == expected
    else:
        assert got == pytest.approx(expected)


def test_zero_baseline_negative_inf_lower_is_better():
    # lower_is_better, baseline 0, compare worsens (goes up) -> -inf
    assert crl.compute_signed_lift(0.0, 0.10, "lower_is_better") == "-inf"


def test_compute_signed_lift_rejects_unknown_direction():
    with pytest.raises(ValueError):
        crl.compute_signed_lift(0.5, 0.6, "sideways")


# ---------------------------------------------------------------------------
# Report builders
# ---------------------------------------------------------------------------
def _report(task="citation_extraction", agg_value=0.95, agg_metric="accuracy",
            agg_direction="higher_is_better", per_class=None):
    task_entry = {
        "task_name": task,
        "manifest_version": "1.0.0",
        "aggregate_metric": {
            "metric": agg_metric, "value": agg_value, "direction": agg_direction,
        },
    }
    if per_class is not None:
        task_entry["per_class"] = per_class
    return {
        "harness_version": "1.0.0", "run_id": "r", "gold_set_version": "1.0.0",
        "per_task": [task_entry], "caveats": ["x"],
    }


# ---------------------------------------------------------------------------
# _flatten_report status filter (#328 P2 — pending-task baseline pollution)
# ---------------------------------------------------------------------------
def test_flatten_includes_measured_task():
    report = {"per_task": [{
        "task_name": "citation_extraction", "status": "measured",
        "aggregate_metric": {"metric": "accuracy", "value": 0.95},
    }]}
    flat = crl._flatten_report(report)
    assert ("citation_extraction", "aggregate", "accuracy") in flat
    assert flat[("citation_extraction", "aggregate", "accuracy")]["value"] == 0.95


def test_flatten_skips_pending_task():
    """A not-yet-landed task is emitted by run_evals._pending_result with
    ``status: "pending"`` and a placeholder ``aggregate_metric.value: 0.0``. That
    placeholder must NOT enter the baseline — else once the task is implemented and
    produces a real value, compute_signed_lift(baseline=0.0, …) hits the zero-
    baseline branch and the brand-new metric is spuriously flagged as a regression
    needing acknowledgement (#328 P2)."""
    report = {"per_task": [{
        "task_name": "future_phase2_task", "status": "pending",
        "aggregate_metric": {"metric": "accuracy", "value": 0.0,
                             "direction": "higher_is_better"},
    }]}
    flat = crl._flatten_report(report)
    assert flat == {}, "pending placeholder metric must not enter the baseline"


def test_flatten_skips_skipped_task():
    report = {"per_task": [{
        "task_name": "skipped_task", "status": "skipped",
        "aggregate_metric": {"metric": "accuracy", "value": 0.0},
    }]}
    assert crl._flatten_report(report) == {}


def test_flatten_skips_unknown_nonmeasured_status():
    """A future non-measured status (e.g. "error") is excluded too — the positive
    skip-unless-measured guard, not a pending/skipped blocklist, is what prevents
    a new status from silently polluting the baseline again (#328 P2)."""
    report = {"per_task": [{
        "task_name": "errored_task", "status": "error",
        "aggregate_metric": {"metric": "accuracy", "value": 0.0},
    }]}
    assert crl._flatten_report(report) == {}


def test_flatten_missing_status_treated_as_measured():
    """Back-compat: a task with no ``status`` key (pre-status reports) still
    flattens — only an explicit pending/skipped status is dropped."""
    report = {"per_task": [{
        "task_name": "legacy_task",
        "aggregate_metric": {"metric": "accuracy", "value": 0.88},
    }]}
    flat = crl._flatten_report(report)
    assert ("legacy_task", "aggregate", "accuracy") in flat


# ---------------------------------------------------------------------------
# Gate semantics
# ---------------------------------------------------------------------------
def test_higher_is_better_positive_passes(monkeypatch):
    monkeypatch.setattr(crl, "_issue_is_open", lambda url: True)
    base = _report(agg_value=0.90)
    cmp = _report(agg_value=0.95)
    result = crl.evaluate_gate(base, cmp, pr_body="")
    assert result["blocked"] is False


def test_regression_blocks_without_ack(monkeypatch):
    monkeypatch.setattr(crl, "_issue_is_open", lambda url: True)
    base = _report(agg_value=0.90)
    cmp = _report(agg_value=0.80)  # -0.111 signed lift < -0.05
    result = crl.evaluate_gate(base, cmp, pr_body="no acknowledgement here")
    assert result["blocked"] is True
    assert any("acknowledged" in r or "[ranking-regression-acknowledged]" in r
               for r in result["reasons"])


def test_lower_is_better_polarity_inverted(monkeypatch):
    # FNR improvement (drops 0.40 -> 0.20) is POSITIVE lift -> not a regression.
    monkeypatch.setattr(crl, "_issue_is_open", lambda url: True)
    pc_base = [{"class_name": "fnr", "metric": "fnr", "value": 0.40, "direction": "lower_is_better"}]
    pc_cmp = [{"class_name": "fnr", "metric": "fnr", "value": 0.20, "direction": "lower_is_better"}]
    base = _report(task="rq_framing_patterns", agg_metric="balanced_accuracy", per_class=pc_base)
    cmp = _report(task="rq_framing_patterns", agg_metric="balanced_accuracy", per_class=pc_cmp)
    result = crl.evaluate_gate(base, cmp, pr_body="")
    assert result["blocked"] is False
    fnr_lift = next(l for l in result["lifts"] if l["metric"] == "fnr")
    assert fnr_lift["signed_lift"] == pytest.approx(0.5)


def test_boundary_minus_005_passes_strict(monkeypatch):
    # signed_lift of -0.05 must PASS (strict < threshold, float-noise tolerant).
    # (0.95-1.0)/1.0 == -0.05000000000000004 in IEEE-754 — without the epsilon
    # tolerance this exact-boundary case would wrongly block.
    monkeypatch.setattr(crl, "_issue_is_open", lambda url: True)
    base = _report(agg_value=1.00)
    cmp = _report(agg_value=0.95)  # nominal -0.05
    result = crl.evaluate_gate(base, cmp, pr_body="")
    agg_lift = next(l for l in result["lifts"] if l["class"] == "aggregate")
    assert agg_lift["signed_lift"] == pytest.approx(-0.05)
    assert result["blocked"] is False


def test_boundary_minus_00501_blocks(monkeypatch):
    monkeypatch.setattr(crl, "_issue_is_open", lambda url: True)
    base = _report(agg_value=1.00)
    cmp = _report(agg_value=0.9499)  # -0.0501 -> blocks
    result = crl.evaluate_gate(base, cmp, pr_body="")
    assert result["blocked"] is True


def test_zero_baseline_plus_inf_passes(monkeypatch):
    # Zero baseline, improved -> +inf. Still a zero-baseline CHANGE, so it
    # requires acknowledgement (any zero-baseline change must be acked).
    monkeypatch.setattr(crl, "_issue_is_open", lambda url: True)
    base = _report(agg_value=0.0)
    cmp = _report(agg_value=0.5)
    body = ("[ranking-regression-acknowledged] "
            "https://github.com/Imbad0202/academic-research-skills/issues/999 "
            "Affected metric: citation_extraction.aggregate.accuracy")
    result = crl.evaluate_gate(base, cmp, pr_body=body)
    assert result["blocked"] is False


def test_zero_baseline_minus_inf_blocks_unless_acked(monkeypatch):
    monkeypatch.setattr(crl, "_issue_is_open", lambda url: True)
    base = _report(agg_value=0.0)
    cmp = _report(agg_value=-0.5, agg_direction="higher_is_better")
    result = crl.evaluate_gate(base, cmp, pr_body="")
    assert result["blocked"] is True


def test_acked_and_open_passes(monkeypatch):
    monkeypatch.setattr(crl, "_issue_is_open", lambda url: True)
    base = _report(agg_value=0.90)
    cmp = _report(agg_value=0.80)
    body = ("[ranking-regression-acknowledged] "
            "https://github.com/Imbad0202/academic-research-skills/issues/123 "
            "Affected metric: citation_extraction.aggregate.accuracy")
    result = crl.evaluate_gate(base, cmp, pr_body=body)
    assert result["blocked"] is False, result["reasons"]


def test_acked_but_closed_blocks(monkeypatch):
    monkeypatch.setattr(crl, "_issue_is_open", lambda url: False)  # closed/404
    base = _report(agg_value=0.90)
    cmp = _report(agg_value=0.80)
    body = ("[ranking-regression-acknowledged] "
            "https://github.com/Imbad0202/academic-research-skills/issues/123 "
            "Affected metric: citation_extraction.aggregate.accuracy")
    result = crl.evaluate_gate(base, cmp, pr_body=body)
    assert result["blocked"] is True
    assert any("OPEN same-repo" in r for r in result["reasons"])


def test_affected_metric_mismatch_blocks(monkeypatch):
    # Acked + open issue, but declared metric does not match the observed regression.
    monkeypatch.setattr(crl, "_issue_is_open", lambda url: True)
    base = _report(agg_value=0.90)
    cmp = _report(agg_value=0.80)
    body = ("[ranking-regression-acknowledged] "
            "https://github.com/Imbad0202/academic-research-skills/issues/123 "
            "Affected metric: citation_extraction.true.accuracy")  # wrong class
    result = crl.evaluate_gate(base, cmp, pr_body=body)
    assert result["blocked"] is True
    assert any("undeclared regression" in r for r in result["reasons"])


def test_no_regression_no_network(monkeypatch):
    # If nothing regresses, the gate must NOT consult _issue_is_open at all.
    def boom(url):  # pragma: no cover - must never run
        raise AssertionError("network/_issue_is_open called when no regression")
    monkeypatch.setattr(crl, "_issue_is_open", boom)
    base = _report(agg_value=0.90)
    cmp = _report(agg_value=0.92)
    result = crl.evaluate_gate(base, cmp, pr_body="")
    assert result["blocked"] is False


def test_parse_pr_body_extracts_tokens():
    body = ("intro\n[ranking-regression-acknowledged]\n"
            "Affected metric: citation_extraction.aggregate.accuracy\n"
            "https://github.com/Imbad0202/academic-research-skills/issues/42\n")
    parsed = crl.parse_pr_body(body)
    assert parsed["has_token"] is True
    assert ("citation_extraction", "aggregate", "accuracy") in parsed["affected_metrics"]
    assert parsed["issue_urls"] == ["https://github.com/Imbad0202/academic-research-skills/issues/42"]


# ---------------------------------------------------------------------------
# Fix 3 — a baseline metric DROPPED in compare is a regression-by-omission
# ---------------------------------------------------------------------------
def _report_two_metrics(agg_value=0.95):
    # baseline carries an extra per_class metric that compare will drop.
    return {
        "harness_version": "1.0.0", "run_id": "r", "gold_set_version": "1.0.0",
        "per_task": [{
            "task_name": "citation_extraction",
            "manifest_version": "1.0.0",
            "aggregate_metric": {"metric": "accuracy", "value": agg_value,
                                 "direction": "higher_is_better"},
            "per_class": [
                {"class_name": "true", "metric": "accuracy", "value": 0.90,
                 "direction": "higher_is_better"},
            ],
        }],
        "caveats": ["x"],
    }


def test_dropped_metric_is_a_violation(monkeypatch):
    monkeypatch.setattr(crl, "_issue_is_open", lambda url: True)
    base = _report_two_metrics()              # has aggregate + true.accuracy
    cmp = _report(agg_value=0.95)             # only aggregate, true.accuracy DROPPED
    lifts = crl.compute_lifts(base, cmp)
    dropped = [l for l in lifts if l.get("is_dropped")]
    assert len(dropped) == 1
    assert dropped[0]["class"] == "true"
    assert dropped[0]["is_regression"] is True


def test_dropped_metric_blocks_without_ack(monkeypatch):
    monkeypatch.setattr(crl, "_issue_is_open", lambda url: True)
    base = _report_two_metrics()
    cmp = _report(agg_value=0.95)
    result = crl.evaluate_gate(base, cmp, pr_body="")
    assert result["blocked"] is True
    assert any("true" in r for r in result["reasons"])


# ---------------------------------------------------------------------------
# Fix 4 — a cross-repo issue URL does not satisfy the ack contract
# ---------------------------------------------------------------------------
def test_cross_repo_issue_url_rejected_by_issue_is_open(monkeypatch):
    # _issue_is_open must short-circuit to False for a foreign repo BEFORE any
    # network call. Make the network path explode to prove it is never reached.
    def boom(*a, **k):  # pragma: no cover - must never run
        raise AssertionError("gh api invoked for a cross-repo URL")
    monkeypatch.setattr(crl.subprocess, "run", boom)
    assert crl._issue_is_open(
        "https://github.com/someone-else/other-repo/issues/1") is False


def test_cross_repo_open_issue_does_not_satisfy_ack(monkeypatch):
    # Even if a foreign repo's issue is "open", it must not unblock the gate.
    # Real _issue_is_open rejects cross-repo URLs without networking, so we use
    # the real function but stub subprocess to fail loudly if it is ever called.
    monkeypatch.setattr(crl.subprocess, "run",
                        lambda *a, **k: (_ for _ in ()).throw(
                            AssertionError("networked on cross-repo URL")))
    base = _report(agg_value=0.90)
    cmp = _report(agg_value=0.80)
    body = ("[ranking-regression-acknowledged] "
            "https://github.com/someone-else/other-repo/issues/1 "
            "Affected metric: citation_extraction.aggregate.accuracy")
    result = crl.evaluate_gate(base, cmp, pr_body=body)
    assert result["blocked"] is True
    assert any("OPEN same-repo" in r for r in result["reasons"])


# ---------------------------------------------------------------------------
# Fix 5 — contract is ">=1 OPEN same-repo issue", not "all OPEN"
# ---------------------------------------------------------------------------
def test_one_open_one_closed_same_repo_passes(monkeypatch):
    # First URL closed, second URL open -> >=1 open -> gate passes.
    open_urls = {"https://github.com/Imbad0202/academic-research-skills/issues/2"}
    monkeypatch.setattr(crl, "_issue_is_open", lambda url: url in open_urls)
    base = _report(agg_value=0.90)
    cmp = _report(agg_value=0.80)
    body = ("[ranking-regression-acknowledged] "
            "https://github.com/Imbad0202/academic-research-skills/issues/1 "
            "https://github.com/Imbad0202/academic-research-skills/issues/2 "
            "Affected metric: citation_extraction.aggregate.accuracy")
    result = crl.evaluate_gate(base, cmp, pr_body=body)
    assert result["blocked"] is False, result["reasons"]


def test_issue_url_regex_is_bounded(monkeypatch):
    # Precision: a glued prefix must not match, the github.com dot is literal,
    # and a trailing path segment must not smuggle extra digits (codex R2 P2).
    parsed = crl.parse_pr_body(
        "xhttps://github.com/Imbad0202/academic-research-skills/issues/12")
    assert parsed["issue_urls"] == []  # glued prefix rejected

    parsed = crl.parse_pr_body(
        "https://github.com/Imbad0202/academic-research-skills/issues/12/comments")
    # The number must be bounded — '/comments' is not absorbed into the number.
    assert parsed["issue_urls"] == [
        "https://github.com/Imbad0202/academic-research-skills/issues/12"]

    # A clean same-repo URL still matches.
    parsed = crl.parse_pr_body(
        "see https://github.com/Imbad0202/academic-research-skills/issues/7 ok")
    assert parsed["issue_urls"] == [
        "https://github.com/Imbad0202/academic-research-skills/issues/7"]


def test_all_closed_same_repo_blocks(monkeypatch):
    monkeypatch.setattr(crl, "_issue_is_open", lambda url: False)
    base = _report(agg_value=0.90)
    cmp = _report(agg_value=0.80)
    body = ("[ranking-regression-acknowledged] "
            "https://github.com/Imbad0202/academic-research-skills/issues/1 "
            "https://github.com/Imbad0202/academic-research-skills/issues/2 "
            "Affected metric: citation_extraction.aggregate.accuracy")
    result = crl.evaluate_gate(base, cmp, pr_body=body)
    assert result["blocked"] is True
    assert any("OPEN same-repo" in r for r in result["reasons"])
