"""Tests for scripts/run_evals.py (#184 Delta 2, Phase 1b harness)."""
from __future__ import annotations

import json
from pathlib import Path

import pytest
import yaml
from jsonschema import Draft202012Validator

from scripts import run_evals
from scripts import _eval_threshold_gate as gate

REPO_ROOT = Path(__file__).resolve().parents[1]
SCHEMA_PATH = REPO_ROOT / "shared" / "evals_lift_report.schema.json"
CITATION_DIR = REPO_ROOT / "evals" / "gold" / "citation_extraction"


@pytest.fixture(scope="module")
def schema():
    return json.loads(SCHEMA_PATH.read_text(encoding="utf-8"))


@pytest.fixture(scope="module")
def validator(schema):
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def _make_task(tmp_path: Path, *, expected: dict, manifest: dict, tuples: dict | None = None) -> Path:
    """Build a minimal gold-set task dir under a tmp gold root and return the root."""
    gold_root = tmp_path / "gold"
    task_dir = gold_root / manifest["task_name"]
    (task_dir / "tuples").mkdir(parents=True)
    (task_dir / "manifest.yaml").write_text(yaml.safe_dump(manifest), encoding="utf-8")
    (task_dir / "expected_outcomes.json").write_text(json.dumps(expected), encoding="utf-8")
    tuples = tuples or {}
    for tid in expected:
        tup = tuples.get(tid, {
            "tuple_id": tid,
            "kind": "valid_doi",
            "corpus_entry": {},
            "arxiv_id": None,
            "human_expert_verdict": None,
            "fabrication_intent": False,
        })
        (task_dir / "tuples" / f"{tid}.json").write_text(json.dumps(tup), encoding="utf-8")
    return gold_root


def _citation_manifest(task_name="citation_extraction"):
    return {
        "task_name": task_name,
        "manifest_version": "1.0.0",
        "task_type": "outcome-gradable",
        "target": {
            "predicted_field": "lookup_verified",
            "expected_outcomes_path": "expected_outcomes.json",
            "tuple_dir": "tuples",
        },
        "labels": ["true", "false", "unresolvable"],
        "thresholds": {
            "aggregate": {"metric": "accuracy", "direction": "higher_is_better",
                          "comparison": ">=", "threshold_value": 0.90},
            "per_class": {"metric": "accuracy", "direction": "higher_is_better",
                          "comparison": ">=", "threshold_value": 0.85,
                          "classes": ["true", "false", "unresolvable"]},
        },
        "tuple_distribution": [
            {"kind": "valid_doi", "n": 1, "expected_lookup_verified": "true"},
            {"kind": "fabricated", "n": 1, "expected_lookup_verified": "false"},
            {"kind": "manual_exempt", "n": 1, "expected_lookup_verified": "unresolvable"},
        ],
    }


def _ro(crossref=None, openalex=None, semantic_scholar=None, arxiv=None):
    """Build resolver_outcomes. Each arg is a status string, or a
    (status, queried_by) tuple. A bare 'unmatched' string defaults
    queried_by='id' so it stays an ID-keyed (false-producing) unmatched under
    the v3.11 narrowed-false reducer — the prior un-narrowed default semantics."""
    def cell(v):
        if isinstance(v, tuple):
            status, queried_by = v
        else:
            status = v or "skipped"
            queried_by = "id" if status == "unmatched" else None
        return {"status": status, "queried_by": queried_by, "response_summary": None}
    return {
        "crossref": cell(crossref),
        "openalex": cell(openalex),
        "semantic_scholar": cell(semantic_scholar),
        "arxiv": cell(arxiv),
    }


# ---------------------------------------------------------------------------
# Schema validation of harness output
# ---------------------------------------------------------------------------
def test_output_validates_against_schema(validator):
    report = run_evals.build_report(["citation_extraction"])
    errors = sorted(validator.iter_errors(report), key=lambda e: e.path)
    assert errors == [], [e.message for e in errors]


def test_run_id_harness_version_gold_set_version_present():
    report = run_evals.build_report(["citation_extraction"])
    assert report["harness_version"]
    assert report["run_id"]
    assert report["gold_set_version"]
    # run_id format: timestamp + hex suffix, never asserted as a relative time.
    assert "T" in report["run_id"] and "Z" in report["run_id"]


# ---------------------------------------------------------------------------
# Aggregate + per-class accuracy on a controlled stub
# ---------------------------------------------------------------------------
def test_aggregate_accuracy_on_stub(tmp_path, monkeypatch):
    expected = {
        "001-a": {"lookup_verified": "true", "resolver_outcomes": _ro(crossref="matched")},
        "002-b": {"lookup_verified": "false", "resolver_outcomes": _ro(crossref="unmatched")},
        "003-c": {"lookup_verified": "unresolvable", "resolver_outcomes": _ro()},
    }
    gold_root = _make_task(tmp_path, expected=expected, manifest=_citation_manifest())
    result = run_evals.run_task("citation_extraction", gold_root)
    assert result["status"] == "measured"
    assert result["aggregate_metric"]["value"] == pytest.approx(1.0)
    assert result["aggregate_metric"]["passed"] is True


def test_per_class_accuracy_correct(tmp_path):
    # One wrong "true" tuple (resolvers all skipped -> reducer says unresolvable).
    expected = {
        "001-a": {"lookup_verified": "true", "resolver_outcomes": _ro(crossref="matched")},
        "002-b": {"lookup_verified": "true", "resolver_outcomes": _ro()},  # predicted unresolvable -> wrong
        "003-c": {"lookup_verified": "false", "resolver_outcomes": _ro(openalex="unmatched")},
    }
    gold_root = _make_task(tmp_path, expected=expected, manifest=_citation_manifest())
    result = run_evals.run_task("citation_extraction", gold_root)
    by_class = {pc["class_name"]: pc for pc in result["per_class"]}
    assert by_class["true"]["support"] == 2
    assert by_class["true"]["value"] == pytest.approx(0.5)
    assert by_class["false"]["value"] == pytest.approx(1.0)


def test_unresolvable_not_collapsed_into_false(tmp_path):
    # A total-outage tuple labeled unresolvable must score as unresolvable,
    # never as false. If the reducer collapsed it, predicted would be wrong.
    expected = {
        "001-outage": {
            "lookup_verified": "unresolvable",
            "resolver_outcomes": _ro(
                crossref="unreachable", openalex="unreachable",
                semantic_scholar="unreachable", arxiv="unreachable",
            ),
        },
    }
    gold_root = _make_task(tmp_path, expected=expected, manifest=_citation_manifest())
    result = run_evals.run_task("citation_extraction", gold_root)
    by_class = {pc["class_name"]: pc for pc in result["per_class"]}
    assert by_class["unresolvable"]["value"] == pytest.approx(1.0)
    assert by_class["false"]["support"] == 0


# ---------------------------------------------------------------------------
# Expert concordance: only over the labeled subset; never gates
# ---------------------------------------------------------------------------
def test_expert_concordance_only_over_labeled_subset(tmp_path):
    expected = {
        "001-a": {"lookup_verified": "true", "resolver_outcomes": _ro(crossref="matched")},
        "002-b": {"lookup_verified": "true", "resolver_outcomes": _ro(crossref="matched")},
        "003-c": {"lookup_verified": "false", "resolver_outcomes": _ro(crossref="unmatched")},
    }
    tuples = {
        "001-a": {"tuple_id": "001-a", "kind": "valid_doi", "corpus_entry": {},
                  "arxiv_id": None, "fabrication_intent": False,
                  "human_expert_verdict": {"verdict": "true", "labeled_by": "x",
                                           "labeled_at": "2026-05-24T00:00:00Z", "notes": None}},
        "002-b": {"tuple_id": "002-b", "kind": "valid_doi", "corpus_entry": {},
                  "arxiv_id": None, "fabrication_intent": False,
                  "human_expert_verdict": None},
        "003-c": {"tuple_id": "003-c", "kind": "fabricated", "corpus_entry": {},
                  "arxiv_id": None, "fabrication_intent": True,
                  "human_expert_verdict": {"verdict": "false", "labeled_by": "x",
                                           "labeled_at": "2026-05-24T00:00:00Z", "notes": None}},
    }
    gold_root = _make_task(tmp_path, expected=expected, manifest=_citation_manifest(), tuples=tuples)
    result = run_evals.run_task("citation_extraction", gold_root)
    conc = {c["class_name"]: c for c in result.get("expert_concordance", [])}
    # Only 001-a (true) and 003-c (false) carry verdicts; 002-b is unlabeled.
    assert conc["true"]["labeled_count"] == 1
    assert conc["false"]["labeled_count"] == 1
    assert "unresolvable" not in conc  # no labeled tuple in that class


def test_low_concordance_does_not_gate(tmp_path):
    # Expert disagrees on the one labeled tuple -> concordance 0.0, but the run
    # still completes with measured status and aggregate computed normally.
    expected = {
        "001-a": {"lookup_verified": "true", "resolver_outcomes": _ro(crossref="matched")},
    }
    tuples = {
        "001-a": {"tuple_id": "001-a", "kind": "valid_doi", "corpus_entry": {},
                  "arxiv_id": None, "fabrication_intent": False,
                  "human_expert_verdict": {"verdict": "false", "labeled_by": "x",
                                           "labeled_at": "2026-05-24T00:00:00Z", "notes": None}},
    }
    gold_root = _make_task(tmp_path, expected=expected, manifest=_citation_manifest(), tuples=tuples)
    result = run_evals.run_task("citation_extraction", gold_root)
    conc = {c["class_name"]: c for c in result["expert_concordance"]}
    assert conc["true"]["agreement_rate"] == pytest.approx(0.0)
    assert result["status"] == "measured"  # not gated


# ---------------------------------------------------------------------------
# Discovery
# ---------------------------------------------------------------------------
def test_no_task_discovers_all_manifests():
    tasks = run_evals.discover_tasks()
    assert "citation_extraction" in tasks
    assert "rq_framing_patterns" in tasks


def test_discover_runs_all(validator):
    tasks = run_evals.discover_tasks()
    report = run_evals.build_report(tasks)
    names = {t["task_name"] for t in report["per_task"]}
    assert "citation_extraction" in names
    assert "rq_framing_patterns" in names
    assert sorted(validator.iter_errors(report), key=lambda e: e.path) == []


# ---------------------------------------------------------------------------
# rq_framing dispatch
# ---------------------------------------------------------------------------
def test_rq_framing_dispatch_shape(validator):
    result = run_evals.run_task("rq_framing_patterns")
    assert result["status"] == "measured"
    assert result["aggregate_metric"]["metric"] == "balanced_accuracy"
    per_class_metrics = {pc["metric"] for pc in result["per_class"]}
    assert {"fnr", "fpr", "balanced_accuracy"} <= per_class_metrics
    # fnr / fpr are lower_is_better in the adapted shape.
    by_metric = {pc["metric"]: pc for pc in result["per_class"]}
    assert by_metric["fnr"]["direction"] == "lower_is_better"
    assert by_metric["balanced_accuracy"]["direction"] == "higher_is_better"


# ---------------------------------------------------------------------------
# Baseline / compare populates lift_pre / lift_post
# ---------------------------------------------------------------------------
def test_baseline_compare_populates_lift(validator):
    base = run_evals.build_report(["citation_extraction"])
    cmp = run_evals.build_report(["citation_extraction"])
    report = run_evals.build_compare_report(base, cmp)
    assert report["mode"] == "compare"
    task = report["per_task"][0]
    assert "lift_pre" in task and "lift_post" in task
    assert any(e["class_name"] == "aggregate" for e in task["lift_pre"])
    assert sorted(validator.iter_errors(report), key=lambda e: e.path) == []


# ---------------------------------------------------------------------------
# Missing entrypoint skips cleanly (no traceback)
# ---------------------------------------------------------------------------
def test_missing_entrypoint_skips_cleanly(tmp_path, validator):
    manifest = {
        "task_name": "status_classification",
        "manifest_version": "0.1.0",
        "task_type": "outcome-gradable",
        "tuple_distribution": [],
        "thresholds": {},
    }
    gold_root = tmp_path / "gold"
    task_dir = gold_root / "status_classification"
    task_dir.mkdir(parents=True)
    (task_dir / "manifest.yaml").write_text(yaml.safe_dump(manifest), encoding="utf-8")
    result = run_evals.run_task("status_classification", gold_root)
    assert result["status"] in ("pending", "skipped")
    assert "notice" in result
    # The pending result must still slot into a schema-valid report.
    report = {
        "harness_version": "1.0.0", "run_id": "x", "gold_set_version": "y",
        "per_task": [result], "caveats": ["pending task present"],
    }
    assert sorted(validator.iter_errors(report), key=lambda e: e.path) == []


def test_run_task_unknown_task_does_not_raise(tmp_path):
    gold_root = tmp_path / "gold"
    gold_root.mkdir()
    result = run_evals.run_task("does_not_exist", gold_root)
    assert result["status"] == "skipped"


def test_surface_form_parity_is_pending_not_silently_passing():
    """#216 regression fixture has NO native measurer (by design — the §F.3.6 surface-form
    bias has no deterministic predictor). run_evals must surface it as `pending`, not as a
    measured pass. This pins codex's P2 concern: a regression fixture must not false-green
    through the eval gate. Its integrity is checked by scripts/check_surface_form_parity.py,
    not by an FNR/FPR measurer here."""
    assert "surface_form_parity" not in run_evals._NATIVE_MEASURERS
    result = run_evals.run_task("surface_form_parity")
    assert result["status"] == "pending", result
    assert "no native measurer" in result["notice"]


# ---------------------------------------------------------------------------
# Implemented-task failures RAISE; they do not masquerade as "pending" (Fix 2)
# ---------------------------------------------------------------------------
def test_implemented_task_corrupt_gold_raises(tmp_path):
    # citation_extraction has a native measurer -> a corrupt expected_outcomes.json
    # must raise TaskExecutionError, not silently downgrade to a "pending" result.
    gold_root = tmp_path / "gold"
    task_dir = gold_root / "citation_extraction"
    (task_dir / "tuples").mkdir(parents=True)
    (task_dir / "manifest.yaml").write_text(
        yaml.safe_dump(_citation_manifest()), encoding="utf-8"
    )
    (task_dir / "expected_outcomes.json").write_text("{ this is not valid json",
                                                     encoding="utf-8")
    with pytest.raises(run_evals.TaskExecutionError):
        run_evals.run_task("citation_extraction", gold_root)


def test_implemented_task_missing_gold_raises(tmp_path):
    # Manifest present (so it is discovered + dispatched) but the gold artifact
    # the measurer reads is absent -> raise, never pending.
    gold_root = tmp_path / "gold"
    task_dir = gold_root / "citation_extraction"
    task_dir.mkdir(parents=True)
    (task_dir / "manifest.yaml").write_text(
        yaml.safe_dump(_citation_manifest()), encoding="utf-8"
    )
    # No expected_outcomes.json, no tuples/ dir.
    with pytest.raises(run_evals.TaskExecutionError):
        run_evals.run_task("citation_extraction", gold_root)


def test_native_task_missing_manifest_raises(tmp_path):
    # A NATIVE task whose manifest.yaml has vanished must raise — a vanished
    # implemented-task asset is a real defect, not a silent skip (codex R2 P1).
    gold_root = tmp_path / "gold"
    gold_root.mkdir()
    with pytest.raises(run_evals.TaskExecutionError):
        run_evals.run_task("citation_extraction", gold_root)


def test_citation_missing_tuple_dir_raises(tmp_path):
    # expected_outcomes.json present but tuples/ dir absent must RAISE, not
    # produce a 0-tuple "measured" run that silently scores nothing (codex R2 P2).
    gold_root = tmp_path / "gold"
    task_dir = gold_root / "citation_extraction"
    task_dir.mkdir(parents=True)
    (task_dir / "manifest.yaml").write_text(
        yaml.safe_dump(_citation_manifest()), encoding="utf-8"
    )
    (task_dir / "expected_outcomes.json").write_text(
        json.dumps({"x": {"lookup_verified": "unresolvable", "resolver_outcomes": {}}}),
        encoding="utf-8",
    )
    # No tuples/ dir created.
    with pytest.raises(run_evals.TaskExecutionError):
        run_evals.run_task("citation_extraction", gold_root)


def test_discover_always_includes_native_tasks(tmp_path):
    # An empty gold root still yields the native tasks, so a vanished native
    # manifest is attempted (and raises in run_task) rather than dropped.
    gold_root = tmp_path / "gold"
    gold_root.mkdir()
    discovered = run_evals.discover_tasks(gold_root)
    assert "citation_extraction" in discovered
    assert "rq_framing_patterns" in discovered


def test_absent_phase2_task_still_pending_not_raise(tmp_path, validator):
    # A genuinely not-yet-shipped Phase-2 task (no native measurer) is a
    # legitimate pending — the raise path must NOT catch this case.
    manifest = {
        "task_name": "summarization_adequacy",
        "manifest_version": "0.1.0",
        "task_type": "outcome-gradable",
        "tuple_distribution": [],
        "thresholds": {},
    }
    gold_root = tmp_path / "gold"
    task_dir = gold_root / "summarization_adequacy"
    task_dir.mkdir(parents=True)
    (task_dir / "manifest.yaml").write_text(yaml.safe_dump(manifest), encoding="utf-8")
    result = run_evals.run_task("summarization_adequacy", gold_root)
    assert result["status"] in ("pending", "skipped")


# ---------------------------------------------------------------------------
# Absolute-threshold gate module (Fix 1 — extracted from the workflow heredoc)
# ---------------------------------------------------------------------------
def _task(name, *, status="measured", passed=None, metric="accuracy"):
    agg = {"metric": metric, "value": 0.5, "direction": "higher_is_better"}
    if passed is not None:
        agg["passed"] = passed
    return {"task_name": name, "manifest_version": "1.0.0",
            "status": status, "aggregate_metric": agg}


def test_gate_flags_below_threshold_task():
    report = {"per_task": [_task("citation_extraction", passed=False)]}
    assert gate.failed_tasks(report) == ["citation_extraction.aggregate.accuracy"]


def test_gate_passes_when_all_above_threshold():
    report = {"per_task": [_task("citation_extraction", passed=True),
                           _task("rq_framing_patterns", passed=True,
                                 metric="balanced_accuracy")]}
    assert gate.failed_tasks(report) == []


def test_gate_ignores_pending_and_thresholdless_tasks():
    report = {"per_task": [
        _task("status_classification", status="pending"),   # not measured
        _task("citation_extraction", passed=None),          # no threshold declared
        _task("rq_framing_patterns", passed=False, metric="balanced_accuracy"),
    ]}
    # Only the measured, threshold-declaring, failing task is flagged.
    assert gate.failed_tasks(report) == ["rq_framing_patterns.aggregate.balanced_accuracy"]


def test_gate_real_run_passes_threshold():
    # End-to-end: the live gold sets meet their thresholds, so the gate is empty.
    report = run_evals.build_report(run_evals.discover_tasks())
    assert gate.failed_tasks(report) == []
