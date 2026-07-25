"""Tests for scripts/render_eval_comment.py (eval-harness PR comment renderer).

Display layer only: these tests pin the comment SHAPE (verdict line, table
rows, folded raw JSON). The gate semantics stay pinned by
scripts/test__eval_threshold_gate.py; the renderer must agree with the gate's
failure signal (aggregate AND per-class) so the table never shows a clean pass
on a run the gate blocks.
"""
from __future__ import annotations

import json

from scripts._eval_threshold_gate import failed_tasks
from scripts.render_eval_comment import _task_failures, main, render_comment


def _measured(name, metric="accuracy", value=1.0, threshold=0.9,
              comparison=">=", passed=True, per_class=None):
    task = {
        "task_name": name,
        "status": "measured",
        "aggregate_metric": {
            "metric": metric,
            "value": value,
            "threshold_value": threshold,
            "comparison": comparison,
            "passed": passed,
        },
    }
    if per_class is not None:
        task["per_class"] = per_class
    return task


def _pending(name):
    # Shape mirrors run_evals._pending_result: a placeholder aggregate_metric
    # with no threshold — the renderer must key off status, not metric absence.
    return {
        "task_name": name,
        "status": "pending",
        "notice": "entrypoint unavailable",
        "aggregate_metric": {
            "metric": "accuracy",
            "value": 0.0,
            "direction": "higher_is_better",
        },
    }


def _render(tasks):
    report = {"per_task": tasks}
    return render_comment(report, json.dumps(report, indent=2))


def test_all_passed_verdict_line():
    out = _render([_measured("citation_extraction"),
                   _measured("rq_framing_patterns", metric="balanced_accuracy",
                             threshold=0.75),
                   _pending("field_norm_severity"),
                   _pending("surface_form_parity")])
    assert "✅ 2/2 measured tasks passed · 2 pending (not wired)" in out


def test_measured_row_renders_metric_value_threshold():
    out = _render([_measured("citation_extraction")])
    assert "| citation_extraction | accuracy | 1.00 | ≥ 0.90 | ✅ |" in out


def test_pending_row_uses_placeholder_columns():
    out = _render([_measured("citation_extraction"),
                   _pending("field_norm_severity")])
    assert "| field_norm_severity | — | — | — | ⏸️ pending |" in out


def test_aggregate_failure_marks_row_and_verdict():
    out = _render([_measured("citation_extraction", value=0.80, passed=False)])
    assert "| citation_extraction | accuracy | 0.80 | ≥ 0.90 | ❌ |" in out
    assert "❌ 0/1 measured tasks passed" in out


def test_per_class_only_failure_still_fails_row():
    # Aggregate passes but a per-class metric fails: the gate blocks (#328),
    # so the row and the verdict must not read as a clean pass.
    per_class = [{"class_name": "high", "metric": "accuracy",
                  "value": 0.70, "threshold_value": 0.85,
                  "comparison": ">=", "passed": False}]
    out = _render([_measured("citation_extraction", per_class=per_class)])
    assert "❌ (per-class)" in out
    assert "❌ 0/1 measured tasks passed" in out


def test_lower_is_better_comparison_passes_through():
    out = _render([_measured("field_norm_severity", metric="fnr", value=0.10,
                             threshold=0.30, comparison="<=")])
    assert "| field_norm_severity | fnr | 0.10 | ≤ 0.30 | ✅ |" in out


def test_measured_rows_sort_before_pending():
    out = _render([_pending("surface_form_parity"),
                   _measured("citation_extraction")])
    assert out.index("| citation_extraction |") < out.index(
        "| surface_form_parity |")


def test_no_pending_omits_pending_suffix():
    out = _render([_measured("citation_extraction")])
    assert "pending" not in out.splitlines()[2]


def test_raw_json_folded_in_details():
    report = {"per_task": [_measured("citation_extraction")]}
    raw = json.dumps(report, indent=2)
    out = render_comment(report, raw)
    assert out.index("<details>") < out.index("```json") < out.index(raw)
    assert out.index(raw) < out.index("</details>")


def test_cli_main_writes_markdown(tmp_path, capsys):
    report = {"per_task": [_measured("citation_extraction"),
                           _pending("surface_form_parity")]}
    path = tmp_path / "eval_report.json"
    path.write_text(json.dumps(report, indent=2), encoding="utf-8")
    assert main([str(path)]) == 0
    stdout = capsys.readouterr().out
    assert stdout.startswith("## Eval harness results")
    assert "✅ 1/1 measured tasks passed · 1 pending (not wired)" in stdout


def test_cli_main_usage_error():
    assert main([]) == 2


def test_failure_signal_agrees_with_threshold_gate():
    # _task_failures deliberately MIRRORS (does not import) the gate's failure
    # rule — importing would couple display to the gate's flat key format.
    # This pin makes the mirror loud instead of silent: if a future gated axis
    # lands in _eval_threshold_gate but not here, this fails in CI rather than
    # the comment rendering green on a run the gate blocks.
    report = {"per_task": [
        _measured("agg_fail", value=0.5, passed=False),
        _measured("pc_fail", per_class=[{"class_name": "high",
                                         "metric": "accuracy",
                                         "passed": False}]),
        _measured("both_fail", value=0.5, passed=False,
                  per_class=[{"class_name": "low", "metric": "accuracy",
                              "passed": False}]),
        _measured("clean"),
        _pending("pending_task"),
    ]}
    renderer_failed = {t["task_name"] for t in report["per_task"]
                       if any(_task_failures(t))}
    gate_failed = {key.split(".")[0] for key in failed_tasks(report)}
    assert renderer_failed == gate_failed == {"agg_fail", "pc_fail", "both_fail"}


def test_table_cells_escape_pipes_and_line_boundaries():
    # task_name / metric come from eval manifests; a `|` or any line boundary
    # (\n, \r, \r\n) must not break the table or spoof extra columns/rows
    # (codex review P2 + re-review \r gap).
    task = _measured("evil|name\nrow\rmore\r\nend", metric="acc|uracy")
    out = _render([task])
    assert "| evil\\|name row more end | acc\\|uracy |" in out
