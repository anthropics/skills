#!/usr/bin/env python3
"""Render a ``run_evals`` report as the eval-harness PR comment markdown.

Display layer ONLY (#184 follow-up): the workflow used to paste the whole
``eval_report.json`` into the PR comment as one raw fenced block. This module
renders the same report as a one-line verdict + a per-task table, with the
full JSON folded into a ``<details>`` block. The threshold verdict itself is
computed by ``scripts._eval_threshold_gate`` — this renderer never gates.

Kept out of the workflow YAML (no inline heredoc) per the same house rule as
the gate module; see scripts/test_eval_harness_workflow.py.

CLI::

    python -m scripts.render_eval_comment <report.json>

prints the comment markdown to stdout.
"""
from __future__ import annotations

import json
import sys
from typing import Any

_COMPARISON_SYMBOLS = {">=": "≥", "<=": "≤", "==": "="}

_PENDING_RESULT = "⏸️ pending"


def _fmt_value(value: Any) -> str:
    if isinstance(value, (int, float)):
        return f"{value:.2f}"
    return str(value)


def _cell(text: Any) -> str:
    """Markdown-table-safe cell: report strings (task_name, metric, comparison)
    come from eval manifests, so a `|` or any line boundary (\\n, \\r, U+2028…)
    would break the table or spoof extra rows/results."""
    return " ".join(str(text).splitlines()).replace("|", "\\|")


def _task_failures(task: dict[str, Any]) -> tuple[bool, bool]:
    """(aggregate_failed, per_class_failed) — mirrors the gate's failure signal."""
    agg = task.get("aggregate_metric") or {}
    agg_failed = agg.get("passed") is False
    pc_failed = any(pc.get("passed") is False for pc in task.get("per_class", []))
    return agg_failed, pc_failed


def _table_row(task: dict[str, Any]) -> str:
    name = _cell(task.get("task_name", "?"))
    if task.get("status", "measured") != "measured":
        return f"| {name} | — | — | — | {_PENDING_RESULT} |"
    agg = task.get("aggregate_metric") or {}
    metric = _cell(agg.get("metric", "—"))
    value = _cell(_fmt_value(agg["value"])) if "value" in agg else "—"
    if "threshold_value" in agg:
        comparison = agg.get("comparison", ">=")
        symbol = _COMPARISON_SYMBOLS.get(comparison, comparison)
        threshold = _cell(f"{symbol} {_fmt_value(agg['threshold_value'])}")
    else:
        threshold = "—"
    agg_failed, pc_failed = _task_failures(task)
    if agg_failed:
        result = "❌"
    elif pc_failed:
        # Aggregate met its threshold but a per-class metric did not — the gate
        # still blocks (#328), so the row must not show a clean pass.
        result = "❌ (per-class)"
    else:
        result = "✅"
    return f"| {name} | {metric} | {value} | {threshold} | {result} |"


def render_comment(report: dict[str, Any], raw_json: str) -> str:
    tasks = report.get("per_task", [])
    measured = [t for t in tasks if t.get("status", "measured") == "measured"]
    pending = [t for t in tasks if t.get("status", "measured") != "measured"]
    passed = [t for t in measured if not any(_task_failures(t))]

    if not measured:
        verdict = "⏸️ no measured tasks"
    else:
        emoji = "✅" if len(passed) == len(measured) else "❌"
        verdict = f"{emoji} {len(passed)}/{len(measured)} measured tasks passed"
    if pending:
        verdict += f" · {len(pending)} pending (not wired)"

    lines = [
        "## Eval harness results",
        "",
        verdict,
        "",
        "| Task | Metric | Value | Threshold | Result |",
        "| --- | --- | --- | --- | --- |",
    ]
    lines.extend(_table_row(t) for t in measured + pending)
    lines.extend(
        [
            "",
            "<details>",
            "<summary>Raw JSON</summary>",
            "",
            "```json",
            raw_json.rstrip("\n"),
            "```",
            "",
            "</details>",
            "",
        ]
    )
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    args = sys.argv[1:] if argv is None else argv
    if len(args) != 1:
        print("usage: python -m scripts.render_eval_comment <report.json>",
              file=sys.stderr)
        return 2
    with open(args[0], encoding="utf-8") as fh:
        raw_json = fh.read()
    report = json.loads(raw_json)
    print(render_comment(report, raw_json))
    return 0


if __name__ == "__main__":
    sys.exit(main())
