"""Tests for scripts/check_pattern_eval_manifest.py.

Covers:
- Micro schema positive validation against a synthetic well-formed manifest.
- Integration schema positive validation against a synthetic well-formed manifest.
- fixture_kind discriminator: missing / unknown / wrong-arm rejection.
- Required-field rejection for both schemas.
- Pattern_id directory-name mismatch rejection.
- Path existence check.
- Coverage cross-check: missing IDs and extra unenumerated IDs.

Run with: pytest -xvs scripts/test_check_pattern_eval_manifest.py
"""

from __future__ import annotations

import json
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
SCRIPT = REPO_ROOT / "scripts" / "check_pattern_eval_manifest.py"

PATTERN_IDS = (
    "A1", "A2", "A3", "A4", "A5",
    "B1", "B2", "B3", "B4", "B5",
    "C1", "C2", "C3",
    "D1", "D2", "D3", "D4",
)


def _well_formed_micro_doc(pattern_id: str = "A1") -> dict:
    return {
        "pattern_id": pattern_id,
        "agent": "synthesis_agent",
        "pattern_scope": "agent_specific",
        "stage": 2,
        "fixture_kind": "micro",
        "upstream_context": {
            "passport_snippet_path": "upstream_context/passport_snippet.yaml",
            "prior_artifacts_dir": "upstream_context/prior_artifacts",
        },
        "bad_run": {
            "deliverable_path": "bad_run/deliverable.md",
            "expected_audit_findings_path": "bad_run/expected_audit_findings.yaml",
            "expected_orchestrator_action_path": "bad_run/expected_orchestrator_action.yaml",
        },
        "good_run": {
            "deliverable_path": "good_run/deliverable.md",
            "expected_audit_findings_path": "good_run/expected_audit_findings.yaml",
            "expected_orchestrator_action_path": "good_run/expected_orchestrator_action.yaml",
        },
    }


def _well_formed_integration_doc() -> dict:
    return {
        "fixture_kind": "integration",
        "patterns_triggered": ["A3", "C2", "D4", "C1"],
        "rounds": [
            {"round": 1, "target_rounds": 3, "expected_verdict": "MATERIAL"},
            {"round": 2, "target_rounds": 3, "expected_verdict": "MATERIAL"},
            {"round": 3, "target_rounds": 3, "expected_verdict": "MATERIAL"},
        ],
        "escalation": {
            "user_choice": "ship_with_known_residue",
            "expected_acknowledgement_finding_ids": ["A3-finding-1", "C2-finding-1"],
        },
        "rationale_doc": (
            "docs/design/2026-04-30-ars-v3.6.7-step-6-orchestrator-hooks-spec.md"
            "#73-chapter-level-integration-fixture"
        ),
    }


_BAD_VERDICT_YAML = """\
run_id: 2026-04-30T10-00-00Z-0a01
verdict_status: MATERIAL
round: 1
target_rounds: 3
finding_counts:
  p1: 1
  p2: 0
  p3: 0
findings:
  - id: F-001
    severity: P1
    dimension: "3.1"
    file: bad_run/deliverable.md
    line: 1
    description: synthetic
    suggested_fix: synthetic
generated_at: "2026-04-30T10:00:00.123Z"
generated_by: scripts/run_codex_audit.sh
generator_version: 1.0.0
"""

_GOOD_VERDICT_YAML = """\
run_id: 2026-04-30T11-00-00Z-0a02
verdict_status: PASS
round: 1
target_rounds: 3
finding_counts:
  p1: 0
  p2: 0
  p3: 0
findings: []
generated_at: "2026-04-30T11:00:00.123Z"
generated_by: scripts/run_codex_audit.sh
generator_version: 1.0.0
"""


def _materialize_micro_dir(parent: Path, doc: dict) -> Path:
    """Create one well-formed micro fixture under <parent>/<pattern_id>/."""
    fixture_dir = parent / doc["pattern_id"]
    (fixture_dir / "upstream_context" / "prior_artifacts").mkdir(parents=True)
    (fixture_dir / "bad_run").mkdir()
    (fixture_dir / "good_run").mkdir()
    (fixture_dir / "manifest.json").write_text(json.dumps(doc), encoding="utf-8")
    (fixture_dir / "upstream_context" / "passport_snippet.yaml").write_text("schema_version: 9\n")
    (fixture_dir / "bad_run" / "deliverable.md").write_text("# bad\n")
    (fixture_dir / "bad_run" / "expected_audit_findings.yaml").write_text(_BAD_VERDICT_YAML)
    (fixture_dir / "bad_run" / "expected_orchestrator_action.yaml").write_text("expected_path: B\n")
    (fixture_dir / "good_run" / "deliverable.md").write_text("# good\n")
    (fixture_dir / "good_run" / "expected_audit_findings.yaml").write_text(_GOOD_VERDICT_YAML)
    (fixture_dir / "good_run" / "expected_orchestrator_action.yaml").write_text("expected_path: B\n")
    return fixture_dir


def _materialize_integration_dir(parent: Path, doc: dict) -> Path:
    fixture_dir = parent / "integration" / "chapter_level_run"
    fixture_dir.mkdir(parents=True)
    (fixture_dir / "manifest.json").write_text(json.dumps(doc), encoding="utf-8")
    return fixture_dir


def _materialize_full_inventory(parent: Path) -> None:
    for pid in PATTERN_IDS:
        doc = _well_formed_micro_doc(pid)
        _materialize_micro_dir(parent, doc)
    _materialize_integration_dir(parent, _well_formed_integration_doc())


def _run_script(fixture_root: Path) -> subprocess.CompletedProcess:
    """Run the script with FIXTURE_ROOT pointed at a synthetic dir."""
    # The script uses a hardcoded FIXTURE_ROOT; we copy a stand-in into place
    # via a temp checkout-style trick: invoke under a temp working tree where
    # tests/fixtures/v3_6_7_pattern_eval/ is a symlink to the synthetic root.
    work = fixture_root.parent
    repo_clone = work / "repo"
    repo_clone.mkdir(exist_ok=True)
    (repo_clone / "scripts").mkdir(exist_ok=True)
    shutil.copy2(SCRIPT, repo_clone / "scripts" / SCRIPT.name)
    # Copy audit_verdict schema so the validator's verdict-YAML check can resolve it.
    schema_dir = repo_clone / "shared" / "contracts" / "audit"
    schema_dir.mkdir(parents=True, exist_ok=True)
    real_schema = REPO_ROOT / "shared" / "contracts" / "audit" / "audit_verdict.schema.json"
    shutil.copy2(real_schema, schema_dir / "audit_verdict.schema.json")
    target = repo_clone / "tests" / "fixtures" / "v3_6_7_pattern_eval"
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.exists() or target.is_symlink():
        target.unlink() if target.is_symlink() else shutil.rmtree(target)
    target.symlink_to(fixture_root, target_is_directory=True)
    return subprocess.run(
        [sys.executable, str(repo_clone / "scripts" / SCRIPT.name)],
        capture_output=True,
        text=True,
    )


# ---------------------------------------------------------------------------
# Positive cases
# ---------------------------------------------------------------------------


def test_full_inventory_passes(tmp_path):
    fixtures = tmp_path / "fixtures"
    fixtures.mkdir()
    _materialize_full_inventory(fixtures)
    result = _run_script(fixtures)
    assert result.returncode == 0, (
        f"Expected 0 exit on well-formed full inventory; got {result.returncode}\n"
        f"stdout: {result.stdout}\nstderr: {result.stderr}"
    )
    assert "OK: 17/17 micro-fixture" in result.stdout


# ---------------------------------------------------------------------------
# Coverage gaps
# ---------------------------------------------------------------------------


def test_missing_one_pattern_id_fails(tmp_path):
    fixtures = tmp_path / "fixtures"
    fixtures.mkdir()
    _materialize_full_inventory(fixtures)
    shutil.rmtree(fixtures / "A3")
    result = _run_script(fixtures)
    assert result.returncode == 1
    assert "coverage gap" in result.stderr
    assert "A3" in result.stderr


def test_extra_unenumerated_pattern_id_fails(tmp_path):
    fixtures = tmp_path / "fixtures"
    fixtures.mkdir()
    _materialize_full_inventory(fixtures)
    rogue = _well_formed_micro_doc("Z1")
    # Z1 is not in PATTERN_IDS, so schema enum will reject before coverage check.
    rogue_dir = fixtures / "Z1"
    rogue_dir.mkdir()
    (rogue_dir / "manifest.json").write_text(json.dumps(rogue), encoding="utf-8")
    result = _run_script(fixtures)
    assert result.returncode == 1


# ---------------------------------------------------------------------------
# fixture_kind discriminator
# ---------------------------------------------------------------------------


def test_missing_fixture_kind_fails(tmp_path):
    fixtures = tmp_path / "fixtures"
    fixtures.mkdir()
    _materialize_full_inventory(fixtures)
    bad_doc = _well_formed_micro_doc("A1")
    bad_doc.pop("fixture_kind")
    (fixtures / "A1" / "manifest.json").write_text(json.dumps(bad_doc), encoding="utf-8")
    result = _run_script(fixtures)
    assert result.returncode == 1
    assert "fixture_kind" in result.stderr


def test_unknown_fixture_kind_fails(tmp_path):
    fixtures = tmp_path / "fixtures"
    fixtures.mkdir()
    _materialize_full_inventory(fixtures)
    bad_doc = _well_formed_micro_doc("A1")
    bad_doc["fixture_kind"] = "unknown_kind"
    (fixtures / "A1" / "manifest.json").write_text(json.dumps(bad_doc), encoding="utf-8")
    result = _run_script(fixtures)
    assert result.returncode == 1
    assert "fixture_kind" in result.stderr


def test_integration_doc_in_micro_slot_fails(tmp_path):
    """Putting an integration manifest under a micro pattern dir is rejected."""
    fixtures = tmp_path / "fixtures"
    fixtures.mkdir()
    _materialize_full_inventory(fixtures)
    bad_doc = _well_formed_integration_doc()
    (fixtures / "A1" / "manifest.json").write_text(json.dumps(bad_doc), encoding="utf-8")
    result = _run_script(fixtures)
    assert result.returncode == 1


# ---------------------------------------------------------------------------
# Required field violations (micro)
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "missing_field",
    [
        "pattern_id",
        "agent",
        "pattern_scope",
        "stage",
        "upstream_context",
        "bad_run",
        "good_run",
    ],
)
def test_micro_missing_required_field_fails(tmp_path, missing_field):
    fixtures = tmp_path / "fixtures"
    fixtures.mkdir()
    _materialize_full_inventory(fixtures)
    bad_doc = _well_formed_micro_doc("A1")
    bad_doc.pop(missing_field)
    (fixtures / "A1" / "manifest.json").write_text(json.dumps(bad_doc), encoding="utf-8")
    result = _run_script(fixtures)
    assert result.returncode == 1


# ---------------------------------------------------------------------------
# Required field violations (integration)
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "missing_field",
    ["patterns_triggered", "rounds", "escalation", "rationale_doc"],
)
def test_integration_missing_required_field_fails(tmp_path, missing_field):
    fixtures = tmp_path / "fixtures"
    fixtures.mkdir()
    _materialize_full_inventory(fixtures)
    bad_doc = _well_formed_integration_doc()
    bad_doc.pop(missing_field)
    integration_path = fixtures / "integration" / "chapter_level_run" / "manifest.json"
    integration_path.write_text(json.dumps(bad_doc), encoding="utf-8")
    result = _run_script(fixtures)
    assert result.returncode == 1


# ---------------------------------------------------------------------------
# Cross-checks
# ---------------------------------------------------------------------------


def test_directory_pattern_id_mismatch_fails(tmp_path):
    fixtures = tmp_path / "fixtures"
    fixtures.mkdir()
    _materialize_full_inventory(fixtures)
    # Put A2 manifest content into A1's directory.
    bad_doc = _well_formed_micro_doc("A2")
    (fixtures / "A1" / "manifest.json").write_text(json.dumps(bad_doc), encoding="utf-8")
    result = _run_script(fixtures)
    assert result.returncode == 1
    assert "does not match directory name" in result.stderr


def test_missing_referenced_path_fails(tmp_path):
    fixtures = tmp_path / "fixtures"
    fixtures.mkdir()
    _materialize_full_inventory(fixtures)
    (fixtures / "A1" / "bad_run" / "deliverable.md").unlink()
    result = _run_script(fixtures)
    assert result.returncode == 1
    assert "does not exist" in result.stderr


def test_invalid_pattern_id_enum_value_fails(tmp_path):
    fixtures = tmp_path / "fixtures"
    fixtures.mkdir()
    _materialize_full_inventory(fixtures)
    bad_doc = _well_formed_micro_doc("A1")
    bad_doc["pattern_id"] = "X9"  # not in enum
    (fixtures / "A1" / "manifest.json").write_text(json.dumps(bad_doc), encoding="utf-8")
    result = _run_script(fixtures)
    assert result.returncode == 1


def test_invalid_agent_enum_value_fails(tmp_path):
    fixtures = tmp_path / "fixtures"
    fixtures.mkdir()
    _materialize_full_inventory(fixtures)
    bad_doc = _well_formed_micro_doc("A1")
    bad_doc["agent"] = "rogue_agent"
    (fixtures / "A1" / "manifest.json").write_text(json.dumps(bad_doc), encoding="utf-8")
    result = _run_script(fixtures)
    assert result.returncode == 1


def test_integration_invalid_user_choice_fails(tmp_path):
    fixtures = tmp_path / "fixtures"
    fixtures.mkdir()
    _materialize_full_inventory(fixtures)
    bad_doc = _well_formed_integration_doc()
    bad_doc["escalation"]["user_choice"] = "rogue_choice"
    integration_path = fixtures / "integration" / "chapter_level_run" / "manifest.json"
    integration_path.write_text(json.dumps(bad_doc), encoding="utf-8")
    result = _run_script(fixtures)
    assert result.returncode == 1


def test_integration_round_below_one_fails(tmp_path):
    fixtures = tmp_path / "fixtures"
    fixtures.mkdir()
    _materialize_full_inventory(fixtures)
    bad_doc = _well_formed_integration_doc()
    bad_doc["rounds"][0]["round"] = 0
    integration_path = fixtures / "integration" / "chapter_level_run" / "manifest.json"
    integration_path.write_text(json.dumps(bad_doc), encoding="utf-8")
    result = _run_script(fixtures)
    assert result.returncode == 1
