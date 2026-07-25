#!/usr/bin/env python3
"""Ranking-method lift gate (#184 Delta 4 / E-V4).

Reads a baseline and a compare ``run_evals`` report (single-run shape, with
``per_task[].aggregate_metric`` + ``per_class``) and computes a polarity-corrected
signed lift per metric. The gate blocks a PR when any metric regresses past the
threshold, unless the PR body declares the regression with the acknowledgement
token AND links an OPEN GitHub issue.

Pure-function core::

    compute_signed_lift(baseline, compare, direction) -> float | "+inf" | "-inf"

* ``higher_is_better``: ``(compare - baseline) / abs(baseline)``
* ``lower_is_better`` : ``(baseline - compare) / abs(baseline)`` (numerator
  inverts so "negative lift = regression" holds for every metric)
* ``baseline == 0``   : ``"+inf"`` if improved, ``"-inf"`` if regressed,
  ``0.0`` if unchanged.

Gate semantics: block (nonzero exit) if any ``signed_lift < -0.05`` OR any
zero-baseline metric changed value, UNLESS the PR body carries
``[ranking-regression-acknowledged]`` + an OPEN issue URL AND the declared
``Affected metric: <task>.<class>.<metric>`` matches the observed regression.

The OPEN-issue check goes through ``_issue_is_open`` — a monkeypatchable seam.
Tests NEVER hit the network.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

REGRESSION_THRESHOLD = -0.05
# Float-noise tolerance so a lift of EXACTLY -0.05 (the spec's inclusive-pass
# boundary) is not flipped to "blocking" by IEEE-754 subtraction error
# (e.g. (0.95-1.0)/1.0 == -0.05000000000000004). -0.0501 still blocks.
_LIFT_EPSILON = 1e-9
ACK_TOKEN = "[ranking-regression-acknowledged]"
# Anchored on a non-URL-char boundary on the left so a glued prefix
# ("xhttps://...") does not match; \d+ is greedy so it already consumes the full
# run of digits, and the (?!\d) tail makes that explicit while still allowing a
# legitimate trailing path segment ("/issues/12/comments" -> .../issues/12).
_ISSUE_URL_RE = re.compile(
    r"(?<![\w/.-])https://github\.com/(?P<owner>[\w.-]+)/(?P<repo>[\w.-]+)"
    r"/issues/(?P<num>\d+)(?!\d)"
)
# This repo (owner/name). An ack issue URL must point HERE, not at some other
# repo's open issue — cross-repo issues must not satisfy the ack contract.
CURRENT_REPO = "Imbad0202/academic-research-skills"
_AFFECTED_METRIC_RE = re.compile(
    r"Affected metric:\s*([\w.-]+)\.([\w.-]+)\.([\w.-]+)"
)


# ---------------------------------------------------------------------------
# Pure lift math
# ---------------------------------------------------------------------------
def compute_signed_lift(
    baseline: float, compare: float, direction: str
) -> float | str:
    """Polarity-corrected signed lift. Positive = improvement, negative = regression."""
    if direction not in ("higher_is_better", "lower_is_better"):
        raise ValueError(f"unknown direction: {direction!r}")

    if baseline == 0:
        if compare == baseline:
            return 0.0
        if direction == "higher_is_better":
            improved = compare > baseline
        else:
            improved = compare < baseline
        return "+inf" if improved else "-inf"

    if direction == "higher_is_better":
        return (compare - baseline) / abs(baseline)
    return (baseline - compare) / abs(baseline)


def _is_regression(signed_lift: float | str) -> bool:
    """A signed lift is a blocking regression if it is -inf or < threshold."""
    if signed_lift == "-inf":
        return True
    if signed_lift == "+inf":
        return False
    # Strict "< -0.05" with float-noise tolerance: exactly -0.05 passes.
    return float(signed_lift) < REGRESSION_THRESHOLD - _LIFT_EPSILON


def _is_zero_baseline_change(signed_lift: float | str) -> bool:
    """Zero-baseline metric that changed value (either +inf or -inf)."""
    return signed_lift in ("+inf", "-inf")


# ---------------------------------------------------------------------------
# Report flattening
# ---------------------------------------------------------------------------
def _flatten_report(report: dict[str, Any]) -> dict[tuple[str, str, str], dict[str, Any]]:
    """Map (task, class, metric) -> {value, direction} across aggregate + per_class.

    The aggregate metric is keyed with class == "aggregate". Pending/skipped tasks
    are excluded: run_evals._pending_result emits a placeholder
    ``aggregate_metric.value: 0.0`` for a not-yet-landed task, and letting that into
    the baseline makes the real value (once the task lands) read as a zero-baseline
    change spuriously flagged as a regression to acknowledge, rather than a new
    metric with no baseline (#328 P2). A task with no ``status`` key is treated as
    measured (pre-status reports stay valid).
    """
    flat: dict[tuple[str, str, str], dict[str, Any]] = {}
    for task in report.get("per_task", []):
        # Skip-unless-measured (matches _eval_threshold_gate.failed_tasks). A
        # pending/skipped task is emitted by run_evals._pending_result with a
        # placeholder ``aggregate_metric.value: 0.0``; letting it into the baseline
        # makes the real value (once the task lands) read as a zero-baseline change
        # spuriously flagged as a regression to acknowledge, rather than a new
        # metric with no baseline (#328 P2). The positive guard (rather than a
        # ``status in {"pending","skipped"}`` blocklist) means a future non-measured
        # status is excluded too, instead of silently polluting the baseline. A task
        # with no ``status`` key is treated as measured (pre-status reports stay valid).
        if task.get("status", "measured") != "measured":
            continue
        task_name = task["task_name"]
        agg = task.get("aggregate_metric")
        if agg:
            flat[(task_name, "aggregate", agg["metric"])] = {
                "value": agg["value"],
                "direction": agg.get("direction", "higher_is_better"),
            }
        for pc in task.get("per_class", []):
            flat[(task_name, pc["class_name"], pc["metric"])] = {
                "value": pc["value"],
                "direction": pc.get("direction", "higher_is_better"),
            }
    return flat


def compute_lifts(
    baseline: dict[str, Any], compare: dict[str, Any]
) -> list[dict[str, Any]]:
    """Per-metric signed lift across baseline metrics.

    A metric present in BOTH reports gets a normal signed lift. A metric present
    in the baseline but DROPPED in compare is recorded as a regression-by-omission
    (``is_dropped``) — a metric can no longer be silently retired to dodge the
    gate. Metrics that are new in compare carry no baseline to lift against and
    are not gated here.
    """
    base_flat = _flatten_report(baseline)
    cmp_flat = _flatten_report(compare)
    results: list[dict[str, Any]] = []
    for key in sorted(base_flat):
        task, cls, metric = key
        direction = base_flat[key]["direction"]
        base_val = base_flat[key]["value"]
        if key not in cmp_flat:
            # Dropped: baseline measured this metric, compare no longer reports
            # it. Treat as a blocking regression unless explicitly acknowledged.
            results.append({
                "task": task,
                "class": cls,
                "metric": metric,
                "direction": direction,
                "baseline": base_val,
                "compare": None,
                "signed_lift": "dropped",
                "is_regression": True,
                "is_zero_baseline_change": False,
                "is_dropped": True,
            })
            continue
        cmp_val = cmp_flat[key]["value"]
        signed = compute_signed_lift(base_val, cmp_val, direction)
        results.append({
            "task": task,
            "class": cls,
            "metric": metric,
            "direction": direction,
            "baseline": base_val,
            "compare": cmp_val,
            "signed_lift": signed,
            "is_regression": _is_regression(signed),
            "is_zero_baseline_change": _is_zero_baseline_change(signed),
            "is_dropped": False,
        })
    return results


# ---------------------------------------------------------------------------
# PR-body parsing
# ---------------------------------------------------------------------------
def parse_pr_body(pr_body: str) -> dict[str, Any]:
    """Extract ack token, issue URLs, and declared affected metrics from PR body."""
    body = pr_body or ""
    return {
        "has_token": ACK_TOKEN in body,
        "issue_urls": [m.group(0) for m in _ISSUE_URL_RE.finditer(body)],
        "affected_metrics": {
            (m.group(1), m.group(2), m.group(3))
            for m in _AFFECTED_METRIC_RE.finditer(body)
        },
    }


# ---------------------------------------------------------------------------
# OPEN-issue check (monkeypatchable seam; never networks in tests)
# ---------------------------------------------------------------------------
def _issue_is_open(url: str) -> bool:
    """Return True iff ``url`` is a SAME-REPO GitHub issue that exists and is OPEN.

    An issue URL pointing at any other repo is rejected outright (returns False)
    — a foreign repo's open issue must not satisfy this repo's ack contract.
    Uses ``gh api``. Tests monkeypatch this; it is never invoked when no
    regression needs acknowledging.
    """
    m = _ISSUE_URL_RE.search(url)
    if not m:
        return False
    owner, repo, number = m.group("owner"), m.group("repo"), m.group("num")
    if f"{owner}/{repo}" != CURRENT_REPO:
        # Cross-repo issue: not a valid acknowledgement target for this repo.
        return False
    try:
        out = subprocess.run(
            ["gh", "api", f"/repos/{owner}/{repo}/issues/{number}", "--jq", ".state"],
            capture_output=True, text=True, check=True,
        )
    except (subprocess.CalledProcessError, FileNotFoundError):
        return False
    return out.stdout.strip().lower() == "open"


# ---------------------------------------------------------------------------
# Gate
# ---------------------------------------------------------------------------
def evaluate_gate(
    baseline: dict[str, Any],
    compare: dict[str, Any],
    pr_body: str = "",
) -> dict[str, Any]:
    """Run the full gate. Returns {blocked, reasons[], lifts[], regressions[]}."""
    lifts = compute_lifts(baseline, compare)
    regressions = [
        l for l in lifts
        if l["is_regression"] or l["is_zero_baseline_change"]
    ]
    parsed = parse_pr_body(pr_body)
    reasons: list[str] = []

    if not regressions:
        return {"blocked": False, "reasons": [], "lifts": lifts, "regressions": []}

    # There is at least one regression / zero-baseline change -> needs ack.
    if not parsed["has_token"]:
        reasons.append(
            f"{len(regressions)} regression(s) but PR body lacks {ACK_TOKEN}."
        )
    if not parsed["issue_urls"]:
        reasons.append("regression acknowledged but no follow-up issue URL found in PR body.")
    else:
        # Contract: >=1 OPEN tracking issue in THIS repo. A closed issue alongside
        # an open one is fine; _issue_is_open already rejects cross-repo URLs.
        if not any(_issue_is_open(url) for url in parsed["issue_urls"]):
            reasons.append(
                "no OPEN same-repo tracking issue among the declared URL(s): "
                + ", ".join(parsed["issue_urls"])
            )

    # E-V4: each observed regression must be declared via Affected metric.
    declared = parsed["affected_metrics"]
    for reg in regressions:
        key = (reg["task"], reg["class"], reg["metric"])
        if key not in declared:
            reasons.append(
                f"undeclared regression: {reg['task']}.{reg['class']}.{reg['metric']} "
                f"(signed_lift={reg['signed_lift']}); add "
                f"'Affected metric: {reg['task']}.{reg['class']}.{reg['metric']}'."
            )

    blocked = bool(reasons)
    return {
        "blocked": blocked,
        "reasons": reasons,
        "lifts": lifts,
        "regressions": regressions,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Ranking-method lift gate (#184 Delta 4).")
    parser.add_argument("--baseline", required=True, type=Path)
    parser.add_argument("--compare", required=True, type=Path)
    parser.add_argument("--pr-body", default="", help="PR description text (or @path to read from file).")
    args = parser.parse_args(argv)

    baseline = json.loads(args.baseline.read_text(encoding="utf-8"))
    compare = json.loads(args.compare.read_text(encoding="utf-8"))
    pr_body = args.pr_body
    if pr_body.startswith("@"):
        pr_body = Path(pr_body[1:]).read_text(encoding="utf-8")

    result = evaluate_gate(baseline, compare, pr_body)
    for lift in result["lifts"]:
        cmp_str = "DROPPED" if lift.get("is_dropped") else f"{lift['compare']:.4f}"
        print(
            f"{lift['task']}.{lift['class']}.{lift['metric']}: "
            f"baseline={lift['baseline']:.4f} compare={cmp_str} "
            f"signed_lift={lift['signed_lift']}"
        )
    if result["blocked"]:
        print("\nRANKING LIFT GATE: BLOCKED", file=sys.stderr)
        for reason in result["reasons"]:
            print(f"  - {reason}", file=sys.stderr)
        return 1
    print("\nRANKING LIFT GATE: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
