#!/usr/bin/env python3
"""Absolute-threshold verdict for the eval harness (#184 Delta 3 / Fix 1).

Phase 1b has no ``main`` baseline, so the CI gate is an ABSOLUTE-threshold check,
not a lift comparison. This module reads a ``run_evals`` report and returns the
list of measured tasks whose aggregate metric failed its declared threshold.

Kept out of the workflow YAML (no inline heredoc) so the gate's only load-bearing
logic is unit-testable rather than asserted via brittle YAML string matching.

CLI::

    python -m scripts._eval_threshold_gate <report.json>

prints a comma-separated list of failed threshold keys —
``<task>.aggregate.<metric>`` and ``<task>.<class>.<metric>`` (empty line if
none) — to stdout.
"""
from __future__ import annotations

import json
import sys
from typing import Any


def failed_tasks(report: dict[str, Any]) -> list[str]:
    """Return one key per measured threshold that failed — aggregate AND per-class.

    Only tasks with ``status == "measured"`` that declare a threshold (so the
    measurer set ``.passed``) are gated. ``passed is False`` is the failure signal
    — a metric without a threshold (``passed`` absent) is not gated, and a
    pending/skipped task is never gated.

    Both axes are binding: manifests declare aggregate AND per-class thresholds
    (e.g. citation_extraction: aggregate ``accuracy >= 0.90`` plus per_class
    ``accuracy >= 0.85``; rq_framing_patterns: ``balanced_accuracy >= 0.75`` plus
    ``fnr <= 0.30`` / ``fpr <= 0.20`` as per_class rows). run_evals stamps
    ``per_class[].passed`` against the per-class threshold, so the gate must honour
    it too — else a PR that regresses only a per-class metric passes the gate when
    it should block (#328). Aggregate failures use ``<task>.aggregate.<metric>``;
    per-class failures use ``<task>.<class_name>.<metric>`` (matching the lift
    gate's per-class key shape).
    """
    failures: list[str] = []
    for task in report.get("per_task", []):
        # Skip-unless-measured (symmetric with check_ranking_lift._flatten_report).
        if task.get("status", "measured") != "measured":
            continue
        agg = task.get("aggregate_metric") or {}
        if agg.get("passed") is False:
            failures.append(f"{task['task_name']}.aggregate.{agg.get('metric', '?')}")
        for pc in task.get("per_class", []):
            if pc.get("passed") is False:
                failures.append(
                    f"{task['task_name']}.{pc.get('class_name', '?')}."
                    f"{pc.get('metric', '?')}"
                )
    return failures


def main(argv: list[str] | None = None) -> int:
    args = sys.argv[1:] if argv is None else argv
    if len(args) != 1:
        print("usage: python -m scripts._eval_threshold_gate <report.json>",
              file=sys.stderr)
        return 2
    report = json.loads(open(args[0], encoding="utf-8").read())
    print(",".join(failed_tasks(report)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
