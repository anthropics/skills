#!/usr/bin/env python3
"""ARS multi-task eval harness (#184 Delta 2, Phase 1b).

Discovers every ``evals/gold/<task>/manifest.yaml``, runs the measurement for
each task, and emits a report shaped by ``shared/evals_lift_report.schema.json``.

Per-task measurement dispatch:

* ``citation_extraction`` (outcome-gradable) — the harness computes the predicted
  ``lookup_verified`` 3-class enum from each tuple's ``resolver_outcomes`` via the
  shipped #182 Delta 4 reducer ``citation_verification_summary.reduce_lookup_verified``
  (the SINGLE source of truth — re-exported here for back-compat). The reducer uses
  the v3.11 narrowed-false definition (C-V6(a)): ``false`` requires an ID-keyed
  unmatched, never a title-only one.
* ``rq_framing_patterns`` (advisory-calibration) — dispatches to the existing
  ``scripts.check_rq_framing_patterns`` runner and adapts its FNR / FPR /
  balanced-accuracy output into the per-task lift-report shape.

CLI::

    python -m scripts.run_evals [--task <name>] [--baseline <path>]
                                [--compare <path>] [--output <report.json>]

* no ``--task``        — discover + run all tasks under ``evals/gold/``
* ``--baseline`` + ``--compare`` — read two prior report JSONs and emit a
  side-by-side report carrying ``lift_pre`` / ``lift_post`` per task.

A missing entrypoint module (or a missing gold set for a Phase-2 task) produces
a ``status: pending``/``skipped`` notice rather than a traceback.
"""
from __future__ import annotations

import argparse
import json
import secrets
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

import yaml

REPO_ROOT = Path(__file__).resolve().parents[1]
GOLD_ROOT = REPO_ROOT / "evals" / "gold"
HARNESS_VERSION = "1.0.0"


class TaskExecutionError(RuntimeError):
    """An IMPLEMENTED task (one with a native measurer) failed to run.

    Raised — never downgraded to ``pending`` — when a task that the harness
    knows how to measure cannot be measured because its gold artifact is
    missing/corrupt or its runner import fails. A genuinely not-yet-shipped
    Phase-2 task (no native measurer) is still a legitimate ``pending``.
    """

# Resolver-outcome status enum (mirrors #182 Delta 4 / check_evals_gold_set).
STATUS_MATCHED = "matched"
STATUS_UNMATCHED = "unmatched"
STATUS_UNREACHABLE = "unreachable"
STATUS_SKIPPED = "skipped"

CITATION_LABELS = ("true", "false", "unresolvable")


# ---------------------------------------------------------------------------
# #182 Delta 4 reducer — single source of truth lives in
# citation_verification_summary.py. Re-exported here so existing callers
# (and tests) that import run_evals.reduce_lookup_verified keep working.
# The reducer uses the v3.11 narrowed-false definition (C-V6(a)): `false`
# requires an ID-keyed unmatched (resolver_outcomes[r].queried_by == "id"),
# never a title-only unmatched.
# ---------------------------------------------------------------------------
try:
    from citation_verification_summary import reduce_lookup_verified
except ImportError:
    from scripts.citation_verification_summary import reduce_lookup_verified


# ---------------------------------------------------------------------------
# Manifest / gold-set loading
# ---------------------------------------------------------------------------
def load_manifest(task_dir: Path) -> dict[str, Any]:
    manifest_path = task_dir / "manifest.yaml"
    return yaml.safe_load(manifest_path.read_text(encoding="utf-8"))


def discover_tasks(gold_root: Path = GOLD_ROOT) -> list[str]:
    """Return sorted task names to run: every discovered ``<task>/manifest.yaml``
    UNION the implemented (native) tasks.

    Native tasks are always included even if their manifest is absent — that
    way a vanished native manifest surfaces as a ``TaskExecutionError`` in
    ``run_task`` instead of being silently dropped from the run. Phase-2 tasks
    (no native measurer) are only run when their manifest is actually present.
    """
    discovered: set[str] = set()
    if gold_root.is_dir():
        discovered = {
            p.parent.name
            for p in gold_root.glob("*/manifest.yaml")
            if p.is_file()
        }
    return sorted(discovered | set(_NATIVE_MEASURERS))


# ---------------------------------------------------------------------------
# citation_extraction measurement (self-reducer)
# ---------------------------------------------------------------------------
def _accuracy(correct: int, total: int) -> float:
    return correct / total if total else 0.0


def measure_citation_extraction(task_dir: Path, manifest: dict[str, Any]) -> dict[str, Any]:
    """Self-reduce every tuple's resolver_outcomes and score vs expected_outcomes.

    The predicted label is computed by ``reduce_lookup_verified`` directly from
    each tuple's pre-recorded ``resolver_outcomes`` (no live network in CI).
    ``verification_gate.verify_citation`` (#182 Delta 5) runs the resolvers live
    and feeds the SAME reducer, so the harness and the shipped API agree by
    construction — they share one reducer (the single source of truth).
    """
    target = manifest.get("target", {})
    expected_path = task_dir / target.get("expected_outcomes_path", "expected_outcomes.json")
    tuples_dir = task_dir / target.get("tuple_dir", "tuples")
    # Validate declared gold artifacts up front: a missing expected_outcomes.json
    # or tuples/ dir is a real defect for this implemented task, not a 0-tuple
    # "measured" run that silently scores nothing. (run_task wraps these into
    # TaskExecutionError.)
    if not expected_path.is_file():
        raise FileNotFoundError(f"expected_outcomes not found: {expected_path}")
    if not tuples_dir.is_dir():
        raise FileNotFoundError(f"tuple_dir not found: {tuples_dir}")
    expected = json.loads(expected_path.read_text(encoding="utf-8"))

    tuples_by_id: dict[str, dict] = {}
    for path in sorted(tuples_dir.glob("*.json")):
        tuples_by_id[path.stem] = json.loads(path.read_text(encoding="utf-8"))

    per_class_total: dict[str, int] = {c: 0 for c in CITATION_LABELS}
    per_class_correct: dict[str, int] = {c: 0 for c in CITATION_LABELS}
    agg_correct = 0
    agg_total = 0

    # Expert concordance: agreement of human_expert_verdict vs expected_outcomes,
    # bucketed by the expected (synthetic ground-truth) class. Advisory only.
    concordance_total: dict[str, int] = {c: 0 for c in CITATION_LABELS}
    concordance_agree: dict[str, int] = {c: 0 for c in CITATION_LABELS}

    for tid, outcome in expected.items():
        gold = outcome.get("lookup_verified")
        predicted = reduce_lookup_verified(outcome.get("resolver_outcomes", {}))
        agg_total += 1
        if gold in per_class_total:
            per_class_total[gold] += 1
        if predicted == gold:
            agg_correct += 1
            if gold in per_class_correct:
                per_class_correct[gold] += 1

        tup = tuples_by_id.get(tid, {})
        hev = tup.get("human_expert_verdict")
        if isinstance(hev, dict) and hev.get("verdict") is not None and gold in concordance_total:
            concordance_total[gold] += 1
            if hev.get("verdict") == gold:
                concordance_agree[gold] += 1

    thresholds = manifest.get("thresholds", {})
    agg_thr = thresholds.get("aggregate", {})
    per_thr = thresholds.get("per_class", {})

    agg_value = _accuracy(agg_correct, agg_total)
    aggregate_metric = {
        "metric": agg_thr.get("metric", "accuracy"),
        "value": agg_value,
        "direction": agg_thr.get("direction", "higher_is_better"),
    }
    if "threshold_value" in agg_thr:
        aggregate_metric["threshold_value"] = agg_thr["threshold_value"]
        aggregate_metric["comparison"] = agg_thr.get("comparison", ">=")
        aggregate_metric["passed"] = agg_value >= agg_thr["threshold_value"]

    per_class: list[dict[str, Any]] = []
    for cls in CITATION_LABELS:
        total = per_class_total[cls]
        value = _accuracy(per_class_correct[cls], total)
        entry = {
            "class_name": cls,
            "metric": per_thr.get("metric", "accuracy"),
            "value": value,
            "direction": per_thr.get("direction", "higher_is_better"),
            "support": total,
        }
        if "threshold_value" in per_thr:
            entry["threshold_value"] = per_thr["threshold_value"]
            entry["comparison"] = per_thr.get("comparison", ">=")
            entry["passed"] = value >= per_thr["threshold_value"]
        per_class.append(entry)

    concordance: list[dict[str, Any]] = []
    for cls in CITATION_LABELS:
        labeled = concordance_total[cls]
        if labeled == 0:
            continue
        concordance.append({
            "class_name": cls,
            "agreement_rate": concordance_agree[cls] / labeled,
            "labeled_count": labeled,
            "agreements": concordance_agree[cls],
        })

    result: dict[str, Any] = {
        "task_name": manifest.get("task_name", task_dir.name),
        "manifest_version": str(manifest.get("manifest_version", "0.0.0")),
        "status": "measured",
        "sample_n": agg_total,
        "aggregate_metric": aggregate_metric,
        "per_class": per_class,
    }
    if concordance:
        result["expert_concordance"] = concordance
    return result


# ---------------------------------------------------------------------------
# rq_framing_patterns measurement (dispatch to existing runner)
# ---------------------------------------------------------------------------
def measure_rq_framing_patterns(task_dir: Path, manifest: dict[str, Any]) -> dict[str, Any]:
    """Dispatch to scripts.check_rq_framing_patterns and adapt its output.

    The existing runner returns ``metrics: {fnr, fpr, balanced_accuracy}``. We
    map ``balanced_accuracy`` -> the per-task ``aggregate_metric`` (it is the
    single higher-is-better headline number) and emit fnr / fpr / balanced_accuracy
    as per-class entries keyed by the metric name (the advisory-calibration task
    has no class axis, so each manifest threshold metric becomes one per_class row).
    """
    from scripts import check_rq_framing_patterns as rq

    target = manifest.get("target", {})
    gold_path = task_dir / target.get("gold_set_path", "gold_set.json")
    evaluation = rq.validate_gold_set(gold_path)
    metrics = evaluation["metrics"]
    thresholds = manifest.get("thresholds", {})

    aggregate_metric = {
        "metric": "balanced_accuracy",
        "value": metrics["balanced_accuracy"],
        "direction": "higher_is_better",
    }
    ba_thr = thresholds.get("balanced_accuracy", {})
    if "threshold_value" in ba_thr:
        aggregate_metric["threshold_value"] = ba_thr["threshold_value"]
        aggregate_metric["comparison"] = ba_thr.get("comparison", ">=")
        aggregate_metric["passed"] = metrics["balanced_accuracy"] >= ba_thr["threshold_value"]

    # Direction per metric: fnr / fpr are lower-is-better; balanced_accuracy higher.
    metric_directions = {
        "fnr": "lower_is_better",
        "fpr": "lower_is_better",
        "balanced_accuracy": "higher_is_better",
    }
    per_class: list[dict[str, Any]] = []
    for name in ("fnr", "fpr", "balanced_accuracy"):
        direction = metric_directions[name]
        entry = {
            "class_name": name,
            "metric": name,
            "value": metrics[name],
            "direction": direction,
        }
        thr = thresholds.get(name, {})
        if "threshold_value" in thr:
            comparison = thr.get("comparison", "<" if direction == "lower_is_better" else ">=")
            entry["threshold_value"] = thr["threshold_value"]
            entry["comparison"] = comparison
            if comparison == "<":
                entry["passed"] = metrics[name] < thr["threshold_value"]
            elif comparison == "<=":
                entry["passed"] = metrics[name] <= thr["threshold_value"]
            else:
                entry["passed"] = metrics[name] >= thr["threshold_value"]
        per_class.append(entry)

    return {
        "task_name": manifest.get("task_name", task_dir.name),
        "manifest_version": str(manifest.get("manifest_version", "0.0.0")),
        "status": "measured",
        "sample_n": len(evaluation["item_results"]),
        "aggregate_metric": aggregate_metric,
        "per_class": per_class,
    }


# ---------------------------------------------------------------------------
# Task dispatch
# ---------------------------------------------------------------------------
def _pending_result(task_dir: Path, manifest: dict[str, Any], notice: str) -> dict[str, Any]:
    """A task whose entrypoint / gold set is unavailable: skip, never traceback."""
    return {
        "task_name": manifest.get("task_name", task_dir.name),
        "manifest_version": str(manifest.get("manifest_version", "0.0.0")),
        "status": "pending",
        "notice": notice,
        "aggregate_metric": {
            "metric": "accuracy",
            "value": 0.0,
            "direction": "higher_is_better",
        },
    }


# Tasks whose measurement is implemented natively in this harness keyed by
# task_name. Anything else falls back to entrypoint-module probing.
_NATIVE_MEASURERS = {
    "citation_extraction": measure_citation_extraction,
    "rq_framing_patterns": measure_rq_framing_patterns,
}


def run_task(task_name: str, gold_root: Path = GOLD_ROOT) -> dict[str, Any]:
    task_dir = gold_root / task_name
    manifest_path = task_dir / "manifest.yaml"
    if not manifest_path.is_file():
        # A native (implemented) task's manifest is a fixed repo asset. If it has
        # vanished, that is a real defect — raise, do not silently skip. An
        # unknown / non-native task with no manifest is a legitimate skip.
        if task_name in _NATIVE_MEASURERS:
            raise TaskExecutionError(
                f"implemented task {task_name!r} has no manifest.yaml under {task_dir}"
            )
        return {
            "task_name": task_name,
            "manifest_version": "0.0.0",
            "status": "skipped",
            "notice": f"no manifest.yaml under {task_dir}",
            "aggregate_metric": {
                "metric": "accuracy",
                "value": 0.0,
                "direction": "higher_is_better",
            },
        }
    manifest = load_manifest(task_dir)

    measurer = _NATIVE_MEASURERS.get(task_name)
    if measurer is None:
        # Phase-2 / unknown task: guard the entrypoint module so a PR that
        # touches an upstream prompt before its gold set lands is not blocked.
        return _pending_result(
            task_dir,
            manifest,
            f"no native measurer for task {task_name!r}; entrypoint not yet wired",
        )

    # An IMPLEMENTED task (native measurer present) MUST measure. If its gold
    # set is corrupt/missing or its runner import fails, that is a real defect —
    # raise rather than masquerade as a schema-valid "pending" and hide the bug.
    # (A not-yet-shipped Phase-2 task takes the measurer-is-None branch above.)
    try:
        return measurer(task_dir, manifest)
    except (ModuleNotFoundError, FileNotFoundError, json.JSONDecodeError,
            yaml.YAMLError, KeyError, ValueError) as exc:
        raise TaskExecutionError(
            f"implemented task {task_name!r} failed to measure "
            f"({type(exc).__name__}: {exc})"
        ) from exc


# ---------------------------------------------------------------------------
# Report assembly + compare mode
# ---------------------------------------------------------------------------
def _new_run_id() -> str:
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    return f"{stamp}-{secrets.token_hex(4)}"


def _gold_set_version(per_task: list[dict[str, Any]]) -> str:
    versions = sorted({t.get("manifest_version", "0.0.0") for t in per_task})
    return "+".join(versions) if versions else "none"


def _metric_entries(task_result: dict[str, Any]) -> list[dict[str, Any]]:
    """Flatten a task result into [{class_name, metric, value, direction}] entries.

    The aggregate is exposed under class_name "aggregate". Per-class metrics are
    exposed under their class_name. This is the shape the lift gate reads.
    """
    entries: list[dict[str, Any]] = []
    agg = task_result.get("aggregate_metric")
    if agg:
        entries.append({
            "class_name": "aggregate",
            "metric": agg["metric"],
            "value": agg["value"],
            "direction": agg.get("direction", "higher_is_better"),
        })
    for pc in task_result.get("per_class", []):
        entries.append({
            "class_name": pc["class_name"],
            "metric": pc["metric"],
            "value": pc["value"],
            "direction": pc.get("direction", "higher_is_better"),
        })
    return entries


def _report_task_index(report: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {t["task_name"]: t for t in report.get("per_task", [])}


def build_report(task_names: list[str], gold_root: Path = GOLD_ROOT) -> dict[str, Any]:
    per_task = [run_task(name, gold_root) for name in task_names]
    caveats = [
        "Synthetic gold set; expert_concordance is advisory and never gates (E-V3).",
        "citation_extraction predicted labels are computed by the #182 Delta 4 "
        "reducer (the single source of truth) from each tuple's pre-recorded "
        "resolver_outcomes; verification_gate.verify_citation feeds the same "
        "reducer live, so harness and API agree by construction.",
    ]
    pending = [t["task_name"] for t in per_task if t.get("status") != "measured"]
    if pending:
        caveats.append(f"Tasks not measured (entrypoint/gold-set pending): {pending}.")
    return {
        "harness_version": HARNESS_VERSION,
        "run_id": _new_run_id(),
        "gold_set_version": _gold_set_version(per_task),
        "generated_at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "mode": "single",
        "per_task": per_task,
        "caveats": caveats,
    }


def build_compare_report(baseline: dict[str, Any], compare: dict[str, Any]) -> dict[str, Any]:
    """Emit a side-by-side report carrying lift_pre / lift_post per task.

    ``baseline`` and ``compare`` are previously-emitted run_evals reports. The
    compare report's per_task list is the union of task names; each entry carries
    the compare-side metrics plus ``lift_pre`` (baseline metric values) and
    ``lift_post`` (compare metric values) for every metric present on both sides.
    """
    base_idx = _report_task_index(baseline)
    cmp_idx = _report_task_index(compare)
    task_names = sorted(set(base_idx) | set(cmp_idx))

    per_task: list[dict[str, Any]] = []
    for name in task_names:
        cmp_task = cmp_idx.get(name)
        base_task = base_idx.get(name)
        primary = cmp_task or base_task
        entry: dict[str, Any] = {
            "task_name": name,
            "manifest_version": str(primary.get("manifest_version", "0.0.0")),
            "status": primary.get("status", "measured"),
            "aggregate_metric": primary.get("aggregate_metric"),
        }
        if "per_class" in primary:
            entry["per_class"] = primary["per_class"]

        if base_task is not None:
            entry["lift_pre"] = _metric_entries(base_task)
        if cmp_task is not None:
            entry["lift_post"] = _metric_entries(cmp_task)
        per_task.append(entry)

    return {
        "harness_version": HARNESS_VERSION,
        "run_id": _new_run_id(),
        "gold_set_version": _gold_set_version(per_task),
        "generated_at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "mode": "compare",
        "per_task": per_task,
        "caveats": [
            "Compare-mode report: lift_pre is baseline, lift_post is compare. "
            "Signed lift + gate decisions are computed by scripts/check_ranking_lift.py.",
        ],
    }


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------
def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="ARS multi-task eval harness (#184).")
    parser.add_argument("--task", default=None, help="Run only this task (default: all discovered).")
    parser.add_argument("--baseline", default=None, type=Path, help="Baseline report JSON for compare mode.")
    parser.add_argument("--compare", default=None, type=Path, help="Compare report JSON for compare mode.")
    parser.add_argument("--output", default=None, type=Path, help="Write report JSON here (default: stdout).")
    args = parser.parse_args(argv)

    if bool(args.baseline) ^ bool(args.compare):
        parser.error("--baseline and --compare must be provided together.")

    if args.baseline and args.compare:
        baseline = json.loads(args.baseline.read_text(encoding="utf-8"))
        compare = json.loads(args.compare.read_text(encoding="utf-8"))
        report = build_compare_report(baseline, compare)
    else:
        if args.task:
            task_names = [args.task]
        else:
            task_names = discover_tasks()
        report = build_report(task_names)

    payload = json.dumps(report, indent=2, ensure_ascii=False)
    if args.output:
        args.output.write_text(payload + "\n", encoding="utf-8")
    else:
        print(payload)
    return 0


if __name__ == "__main__":
    sys.exit(main())
