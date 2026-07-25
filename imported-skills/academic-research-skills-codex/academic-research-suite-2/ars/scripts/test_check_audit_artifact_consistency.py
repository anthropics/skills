"""Phase 6.3 acceptance tests for ARS v3.6.7 §3.7 invariant lint.

Every row in spec §3.7 families A-F gets at least one positive (valid
fixture passes) and one negative (deliberately-broken fixture fails)
test. The aggregator (run_checks) is also smoke-tested on a fully-
valid synthetic proposal + persisted bundle.

Per the user's iron law: positive + negative tests for every rule.
"""
from __future__ import annotations

import copy
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest

from scripts.check_audit_artifact_consistency import (
    LintContext,
    LintError,
    check_a1,
    check_a2,
    check_a3,
    check_a4,
    check_a5,
    check_a6,
    check_a7,
    check_b1,
    check_b2,
    check_b3,
    check_b4,
    check_b5,
    check_b6,
    check_b7,
    check_b8,
    check_b9,
    check_b10,
    check_c1,
    check_c2,
    check_c3,
    check_c4,
    check_d1,
    check_d2,
    check_d3,
    check_d4,
    check_e1_e2_e6,
    check_e3_e4,
    check_e5,
    check_e7,
    check_f1,
    check_f2,
    check_f3,
    compute_bundle_manifest,
    main,
    run_checks,
    run_example_harness,
)

REPO = Path(__file__).resolve().parent.parent


# ---------------------------------------------------------------------------
# Synthetic fixtures (kept in-memory; written to tmp_path when files needed)
# ---------------------------------------------------------------------------

VALID_RUN_ID = "2026-04-30T15-22-04Z-d8f3"
VALID_THREAD_ID = "019de371-4c13-7521-8af7-fccf6bd23279"


def make_valid_verdict_file_minor() -> dict[str, Any]:
    return {
        "run_id": VALID_RUN_ID,
        "verdict_status": "MINOR",
        "round": 2,
        "target_rounds": 3,
        "finding_counts": {"p1": 0, "p2": 0, "p3": 1},
        "findings": [
            {"id": "F-007", "severity": "P3", "dimension": "3.7",
             "file": "chapter_4/synthesis.md", "line": 482,
             "description": "deictic temporal phrase",
             "suggested_fix": "replace with explicit date"},
        ],
        "generated_at": "2026-04-30T15:22:58.471Z",
        "generated_by": "scripts/run_codex_audit.sh",
        "generator_version": "1.0.0",
    }


def make_valid_verdict_file_pass() -> dict[str, Any]:
    return {
        "run_id": VALID_RUN_ID,
        "verdict_status": "PASS",
        "round": 1,
        "target_rounds": 3,
        "finding_counts": {"p1": 0, "p2": 0, "p3": 0},
        "findings": [],
        "generated_at": "2026-04-30T15:22:58.471Z",
        "generated_by": "scripts/run_codex_audit.sh",
        "generator_version": "1.0.0",
    }


def make_valid_verdict_file_audit_failed() -> dict[str, Any]:
    return {
        "run_id": VALID_RUN_ID,
        "verdict_status": "AUDIT_FAILED",
        "round": 1,
        "target_rounds": 3,
        "finding_counts": {"p1": 0, "p2": 0, "p3": 0},
        "findings": [],
        "failure_reason": "codex exit 70: network timeout",
        "generated_at": "2026-04-30T15:22:58.471Z",
        "generated_by": "scripts/run_codex_audit.sh",
        "generator_version": "1.0.0",
    }


def make_valid_persisted_entry_minor() -> dict[str, Any]:
    return {
        "stage": 2,
        "agent": "synthesis_agent",
        "deliverable_path": "chapter_4/synthesis.md",
        "deliverable_sha": "a" * 64,
        "run_id": VALID_RUN_ID,
        "bundle_id": "phase2-chapter4-2026-04-30",
        "bundle_manifest_sha": "9" * 64,
        "artifact_paths": {
            "jsonl": f"{VALID_RUN_ID}.jsonl",
            "sidecar": f"{VALID_RUN_ID}.meta.json",
            "verdict": f"{VALID_RUN_ID}.verdict.yaml",
        },
        "verdict": {
            "status": "MINOR",
            "round": 2,
            "target_rounds": 3,
            "finding_counts": {"p1": 0, "p2": 0, "p3": 1},
            "verified_at": "2026-04-30T15:23:11.847Z",
            "verified_by": "pipeline_orchestrator_agent",
        },
    }


def make_valid_proposal_entry_pass() -> dict[str, Any]:
    return {
        "stage": 2,
        "agent": "synthesis_agent",
        "deliverable_path": "chapter_4/synthesis.md",
        "deliverable_sha": "a" * 64,
        "run_id": VALID_RUN_ID,
        "bundle_id": "phase2-chapter4-2026-04-30",
        "bundle_manifest_sha": "9" * 64,
        "artifact_paths": {
            "jsonl": f"{VALID_RUN_ID}.jsonl",
            "sidecar": f"{VALID_RUN_ID}.meta.json",
            "verdict": f"{VALID_RUN_ID}.verdict.yaml",
        },
        "verdict": {
            "status": "PASS",
            "round": 1,
            "target_rounds": 3,
            "finding_counts": {"p1": 0, "p2": 0, "p3": 0},
        },
    }


def make_valid_sidecar(template_sha: str = "1" * 64) -> dict[str, Any]:
    primary = [{"path": "chapter_4/synthesis.md", "sha": "a" * 64}]
    supporting = [{"path": "chapter_4/bibliography.json", "sha": "b" * 64}]
    _, manifest_sha = compute_bundle_manifest(
        primary, supporting, "shared/templates/codex_audit_multifile_template.md", template_sha
    )
    return {
        "run_id": VALID_RUN_ID,
        "codex_cli_version": "0.128.0",
        "runner": {
            "hostname": "runner.example.local",
            "cwd": "/path/to/academic-research-skills",
            "git_sha": "b4fbffd",
            "git_dirty": False,
        },
        "timing": {
            "started_at": "2026-04-30T15:22:04.123Z",
            "ended_at": "2026-04-30T15:22:58.471Z",
            "duration_seconds": 54.348,
        },
        "process": {
            "exit_code": 0,
            "stdout_path": f"audit_artifacts/{VALID_RUN_ID}.stdout",
            "stderr_path": f"audit_artifacts/{VALID_RUN_ID}.stderr",
        },
        "stream": {"jsonl_thread_id": VALID_THREAD_ID},
        "prompt": {
            "audit_template_path": "shared/templates/codex_audit_multifile_template.md",
            "audit_template_sha": template_sha,
            "bundle": {
                "bundle_id": "phase2-chapter4-2026-04-30",
                "bundle_manifest_sha": manifest_sha,
                "primary_deliverables": primary,
                "supporting_context": supporting,
            },
        },
    }


def make_valid_jsonl_events_no_tool() -> list[dict[str, Any]]:
    return [
        {"type": "thread.started", "thread_id": VALID_THREAD_ID},
        {"type": "turn.started"},
        {"type": "item.completed",
         "item": {"id": "item_0", "type": "agent_message",
                  "text": "## Section 6 — Verdict\n\nRound 1: 0 findings of any severity. Convergence reached.\n"}},
        {"type": "turn.completed",
         "usage": {"input_tokens": 100, "cached_input_tokens": 0,
                   "output_tokens": 50, "reasoning_output_tokens": 25}},
    ]


def make_valid_jsonl_events_tool_using() -> list[dict[str, Any]]:
    return [
        {"type": "thread.started", "thread_id": VALID_THREAD_ID},
        {"type": "turn.started"},
        {"type": "item.started", "item": {"id": "item_1", "type": "command_execution"}},
        {"type": "item.completed", "item": {"id": "item_1", "type": "command_execution"}},
        {"type": "item.completed",
         "item": {"id": "item_2", "type": "agent_message",
                  "text": "## Section 6 — Verdict\n\nRound 1: 0 findings of any severity. Convergence reached.\n"}},
        {"type": "turn.completed",
         "usage": {"input_tokens": 100, "cached_input_tokens": 0,
                   "output_tokens": 50, "reasoning_output_tokens": 25}},
    ]


# ---------------------------------------------------------------------------
# Family A
# ---------------------------------------------------------------------------


class TestA1:
    """A1 — verdict.status agrees with finding_counts and failure_reason."""

    def test_pass_with_zero_counts_passes(self):
        v = make_valid_verdict_file_pass()
        assert check_a1(None, v) == []

    def test_pass_with_nonzero_p1_fails(self):
        v = make_valid_verdict_file_pass()
        v["finding_counts"]["p1"] = 1
        findings = check_a1(None, v)
        assert any(f.rule_id == "A1" and "PASS" in f.message for f in findings)

    def test_minor_with_p3_le_3_passes(self):
        v = make_valid_verdict_file_minor()
        assert check_a1(None, v) == []

    def test_minor_with_p3_4_fails(self):
        v = make_valid_verdict_file_minor()
        v["finding_counts"]["p3"] = 4
        findings = check_a1(None, v)
        assert any("MINOR" in f.message for f in findings)

    def test_minor_with_zero_counts_fails(self):
        # Codex round 10 P2: MINOR with p1=p2=p3=0 is malformed because the
        # wrapper classifies zero findings as PASS, not MINOR. A hand-edited
        # verdict file claiming zero-count MINOR would otherwise pass A1
        # and send the orchestrator down the MINOR escalation path with
        # no findings to act on.
        v = make_valid_verdict_file_minor()
        v["finding_counts"] = {"p1": 0, "p2": 0, "p3": 0}
        findings = check_a1(None, v)
        assert any(f.rule_id == "A1" and "MINOR" in f.message for f in findings), [
            f.render() for f in findings
        ]

    def test_material_with_p1_gt_0_passes(self):
        v = {**make_valid_verdict_file_pass(),
             "verdict_status": "MATERIAL",
             "finding_counts": {"p1": 1, "p2": 0, "p3": 0}}
        assert check_a1(None, v) == []

    def test_material_all_zero_fails(self):
        v = {**make_valid_verdict_file_pass(), "verdict_status": "MATERIAL"}
        findings = check_a1(None, v)
        assert any("MATERIAL" in f.message for f in findings)

    def test_audit_failed_with_failure_reason_passes(self):
        v = make_valid_verdict_file_audit_failed()
        assert check_a1(None, v) == []

    def test_audit_failed_missing_failure_reason_fails(self):
        v = make_valid_verdict_file_audit_failed()
        del v["failure_reason"]
        findings = check_a1(None, v)
        assert any("AUDIT_FAILED" in f.message for f in findings)

    def test_pass_with_failure_reason_fails(self):
        v = make_valid_verdict_file_pass()
        v["failure_reason"] = "should not be here"
        findings = check_a1(None, v)
        assert any("PASS forbids failure_reason" in f.message for f in findings)


class TestA2:
    """A2 — failure_reason iff status == AUDIT_FAILED."""

    def test_audit_failed_with_reason_passes(self):
        v = make_valid_verdict_file_audit_failed()
        assert check_a2(None, v) == []

    def test_audit_failed_without_reason_fails(self):
        v = make_valid_verdict_file_audit_failed()
        del v["failure_reason"]
        findings = check_a2(None, v)
        assert any(f.rule_id == "A2" for f in findings)

    def test_minor_with_reason_fails(self):
        v = make_valid_verdict_file_minor()
        v["failure_reason"] = "leftover"
        findings = check_a2(None, v)
        assert any(f.rule_id == "A2" and "forbidden" in f.message for f in findings)


class TestA3:
    """A3 — round <= target_rounds."""

    def test_round_le_target_passes(self):
        v = make_valid_verdict_file_minor()  # round=2 target=3
        assert check_a3(None, v) == []

    def test_round_gt_target_fails(self):
        v = make_valid_verdict_file_minor()
        v["round"] = 5
        findings = check_a3(None, v)
        assert any(f.rule_id == "A3" for f in findings)


class TestA4:
    """A4 — acknowledgement only on persisted MATERIAL."""

    def test_persisted_material_with_ack_passes(self):
        e = make_valid_persisted_entry_minor()
        e["verdict"]["status"] = "MATERIAL"
        e["verdict"]["finding_counts"] = {"p1": 1, "p2": 0, "p3": 0}
        e["acknowledgement"] = {
            "finding_ids": ["F-001"],
            "acknowledged_at": e["verdict"]["verified_at"],
            "acknowledged_by": "user",
        }
        assert check_a4(e, "persisted") == []

    def test_proposal_with_ack_fails(self):
        e = make_valid_proposal_entry_pass()
        e["acknowledgement"] = {"finding_ids": ["F-001"],
                                 "acknowledged_at": "2026-04-30T15:23:11.847Z",
                                 "acknowledged_by": "user"}
        findings = check_a4(e, "proposal")
        assert any(f.rule_id == "A4" for f in findings)

    def test_persisted_pass_with_ack_fails(self):
        e = make_valid_persisted_entry_minor()
        e["verdict"]["status"] = "PASS"
        e["verdict"]["finding_counts"] = {"p1": 0, "p2": 0, "p3": 0}
        e["acknowledgement"] = {"finding_ids": ["F-001"],
                                 "acknowledged_at": e["verdict"]["verified_at"],
                                 "acknowledged_by": "user"}
        findings = check_a4(e, "persisted")
        assert any(f.rule_id == "A4" and "MATERIAL" in f.message for f in findings)


class TestA5:
    """A5 — finding_counts.pN == count(findings[severity==PN])."""

    def test_counts_agree_passes(self):
        v = make_valid_verdict_file_minor()
        assert check_a5(v) == []

    def test_count_disagrees_fails(self):
        v = make_valid_verdict_file_minor()
        v["finding_counts"]["p3"] = 5  # but findings only has 1 P3
        findings = check_a5(v)
        assert any(f.rule_id == "A5" and "p3" in f.message for f in findings)


class TestA6:
    """A6 — AUDIT_FAILED requires findings == []."""

    def test_audit_failed_empty_findings_passes(self):
        v = make_valid_verdict_file_audit_failed()
        assert check_a6(v) == []

    def test_audit_failed_with_findings_fails(self):
        v = make_valid_verdict_file_audit_failed()
        v["findings"] = [{"id": "F-001", "severity": "P3", "dimension": "3.7",
                          "file": "x.md", "line": 1, "description": "x", "suggested_fix": "y"}]
        findings = check_a6(v)
        assert any(f.rule_id == "A6" for f in findings)


class TestA7:
    """A7 — JSONL stream tool-event pairing."""

    def test_no_tool_events_passes(self):
        events = make_valid_jsonl_events_no_tool()
        assert check_a7(events) == []

    def test_tool_using_events_pass(self):
        events = make_valid_jsonl_events_tool_using()
        assert check_a7(events) == []

    def test_orphan_tool_completion_fails(self):
        events = [
            {"type": "thread.started", "thread_id": VALID_THREAD_ID},
            {"type": "turn.started"},
            {"type": "item.completed",
             "item": {"id": "item_orphan", "type": "command_execution"}},
            {"type": "turn.completed",
             "usage": {"input_tokens": 1, "cached_input_tokens": 0,
                       "output_tokens": 1, "reasoning_output_tokens": 0}},
        ]
        findings = check_a7(events)
        assert any(f.rule_id == "A7" and "orphan" in f.message for f in findings)

    def test_unmatched_tool_start_fails(self):
        events = [
            {"type": "thread.started", "thread_id": VALID_THREAD_ID},
            {"type": "item.started", "item": {"id": "item_unmatched", "type": "command_execution"}},
            {"type": "turn.completed",
             "usage": {"input_tokens": 1, "cached_input_tokens": 0,
                       "output_tokens": 1, "reasoning_output_tokens": 0}},
        ]
        findings = check_a7(events)
        assert any(f.rule_id == "A7" and "unmatched" in f.message for f in findings)

    def test_duplicate_started_fails(self):
        events = [
            {"type": "thread.started", "thread_id": VALID_THREAD_ID},
            {"type": "item.started", "item": {"id": "item_x", "type": "command_execution"}},
            {"type": "item.started", "item": {"id": "item_x", "type": "command_execution"}},
            {"type": "item.completed", "item": {"id": "item_x", "type": "command_execution"}},
            {"type": "turn.completed",
             "usage": {"input_tokens": 1, "cached_input_tokens": 0,
                       "output_tokens": 1, "reasoning_output_tokens": 0}},
        ]
        findings = check_a7(events)
        assert any(f.rule_id == "A7" and "duplicate item.started" in f.message for f in findings)

    def test_completed_before_started_fails(self):
        # An item.completed appearing before its item.started would be classified
        # as orphan because we scan top-down. Either error covers the violation.
        events = [
            {"type": "thread.started", "thread_id": VALID_THREAD_ID},
            {"type": "item.completed", "item": {"id": "item_z", "type": "command_execution"}},
            {"type": "item.started", "item": {"id": "item_z", "type": "command_execution"}},
            {"type": "turn.completed",
             "usage": {"input_tokens": 1, "cached_input_tokens": 0,
                       "output_tokens": 1, "reasoning_output_tokens": 0}},
        ]
        findings = check_a7(events)
        # We expect at least one A7 finding (orphan or ordering)
        assert any(f.rule_id == "A7" for f in findings)


# ---------------------------------------------------------------------------
# Family B
# ---------------------------------------------------------------------------


class TestB1:
    """B1 — sidecar.stream.jsonl_thread_id matches JSONL.thread.started.thread_id."""

    def test_matching_thread_id_passes(self):
        s = make_valid_sidecar()
        events = make_valid_jsonl_events_no_tool()
        v = make_valid_verdict_file_minor()
        assert check_b1(s, events, v) == []

    def test_mismatched_thread_id_fails(self):
        s = make_valid_sidecar()
        s["stream"]["jsonl_thread_id"] = "11111111-1111-1111-1111-111111111111"
        events = make_valid_jsonl_events_no_tool()
        v = make_valid_verdict_file_minor()
        findings = check_b1(s, events, v)
        assert any(f.rule_id == "B1" for f in findings)

    def test_audit_failed_suspends_b1(self):
        s = make_valid_sidecar()
        s["stream"]["jsonl_thread_id"] = ""  # AUDIT_FAILED permits empty
        v = make_valid_verdict_file_audit_failed()
        # JSONL may be malformed/missing on AUDIT_FAILED; but B1 is suspended
        assert check_b1(s, [], v) == []


class TestB2:
    """B2 — entry.deliverable_sha == sidecar.primary_sha == disk SHA."""

    def test_matching_shas_passes(self, tmp_path: Path):
        e = make_valid_persisted_entry_minor()
        s = make_valid_sidecar()
        # repo_root is tmp_path with no deliverable file — disk verify skipped
        assert check_b2(e, s, tmp_path) == []

    def test_entry_sidecar_sha_disagree_fails(self):
        e = make_valid_persisted_entry_minor()
        s = make_valid_sidecar()
        s["prompt"]["bundle"]["primary_deliverables"][0]["sha"] = "f" * 64
        findings = check_b2(e, s, REPO)
        assert any(f.rule_id == "B2" for f in findings)

    def test_disk_sha_mismatch_fails(self, tmp_path: Path):
        e = make_valid_persisted_entry_minor()
        e["deliverable_path"] = "deliverable.md"
        s = make_valid_sidecar()
        s["prompt"]["bundle"]["primary_deliverables"] = [
            {"path": "deliverable.md", "sha": "a" * 64}
        ]
        # Write a real file but with content whose SHA is NOT all-a's
        (tmp_path / "deliverable.md").write_text("totally different content\n")
        findings = check_b2(e, s, tmp_path)
        assert any(f.rule_id == "B2" and "current_file" in f.message for f in findings)


class TestB3:
    """B3 — bundle_manifest_sha agrees with recomputed manifest."""

    def test_matching_manifest_passes(self):
        s = make_valid_sidecar()
        # repo_root REPO doesn't have these files; but declared SHAs will recompute
        # consistently because the helper used the same SHAs.
        assert check_b3(s, REPO / "nonexistent_subtree") == []

    def test_mismatched_manifest_fails(self):
        s = make_valid_sidecar()
        s["prompt"]["bundle"]["bundle_manifest_sha"] = "0" * 64
        findings = check_b3(s, REPO / "nonexistent_subtree")
        assert any(f.rule_id == "B3" for f in findings)

    def test_missing_bundle_file_fails(self, tmp_path: Path):
        # Codex round 2 P2: when a bundle file is missing on disk, B3 must
        # NOT fall back to the sidecar-declared SHA — that would let a
        # deleted/moved file silently pass. With a real .git/ marker, B3
        # Step 2 is required to flag the missing file as stale/unverifiable.
        # Synthesize a tmp repo with a real .git marker but missing bundle
        # files; the sidecar's declared paths are intentionally absent.
        (tmp_path / ".git").mkdir()  # marker only; B3 doesn't run git commands
        s = make_valid_sidecar()  # references deliverable.md / bibliography.json / verification.md / template
        findings = check_b3(s, tmp_path)
        assert any(
            f.rule_id == "B3" and "missing on disk" in f.message
            for f in findings
        ), [f.render() for f in findings]


class TestB4:
    """B4 — runner.git_sha resolves to a real commit."""

    def test_real_git_sha_passes(self):
        # Use the actual repo HEAD
        result = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            capture_output=True, text=True, cwd=REPO,
        )
        head = result.stdout.strip()
        s = make_valid_sidecar()
        s["runner"]["git_sha"] = head[:12]
        assert check_b4(s, REPO) == []

    def test_fake_git_sha_fails(self):
        s = make_valid_sidecar()
        s["runner"]["git_sha"] = "deadbeefdeadbeef"
        findings = check_b4(s, REPO)
        assert any(f.rule_id == "B4" for f in findings)

    def test_outside_git_repo_skipped(self, tmp_path: Path):
        # tmp_path has no .git/, so B4 is skipped (no false positive on synthetic fixtures)
        s = make_valid_sidecar()
        s["runner"]["git_sha"] = "deadbeef"
        assert check_b4(s, tmp_path) == []


class TestB5:
    """B5 — ended_at - started_at == duration_seconds (±1s)."""

    def test_consistent_timing_passes(self):
        s = make_valid_sidecar()
        assert check_b5(s) == []

    def test_inconsistent_timing_fails(self):
        s = make_valid_sidecar()
        s["timing"]["duration_seconds"] = 999.0
        findings = check_b5(s)
        assert any(f.rule_id == "B5" for f in findings)


class TestB6:
    """B6 — exit_code == 0 for non-AUDIT_FAILED."""

    def test_zero_exit_minor_passes(self):
        s = make_valid_sidecar()
        v = make_valid_verdict_file_minor()
        assert check_b6(s, v) == []

    def test_nonzero_exit_minor_fails(self):
        s = make_valid_sidecar()
        s["process"]["exit_code"] = 70
        v = make_valid_verdict_file_minor()
        findings = check_b6(s, v)
        assert any(f.rule_id == "B6" for f in findings)

    def test_nonzero_exit_audit_failed_passes(self):
        s = make_valid_sidecar()
        s["process"]["exit_code"] = 70
        v = make_valid_verdict_file_audit_failed()
        assert check_b6(s, v) == []


class TestB7:
    """B7 — entry.run_id == sidecar.run_id == bare basename of every co-located file."""

    def test_matching_run_ids_pass(self, tmp_path: Path):
        e = make_valid_persisted_entry_minor()
        s = make_valid_sidecar()
        sidecar_path = tmp_path / f"{VALID_RUN_ID}.meta.json"
        jsonl_path = tmp_path / f"{VALID_RUN_ID}.jsonl"
        verdict_path = tmp_path / f"{VALID_RUN_ID}.verdict.yaml"
        # Don't actually need to write the files for B7
        assert check_b7(e, s, None, sidecar_path, jsonl_path, verdict_path, "persisted") == []

    def test_entry_sidecar_run_id_mismatch_fails(self, tmp_path: Path):
        e = make_valid_persisted_entry_minor()
        s = make_valid_sidecar()
        s["run_id"] = "2026-04-30T15-22-04Z-aaaa"
        findings = check_b7(e, s, None, tmp_path / f"{VALID_RUN_ID}.meta.json",
                             tmp_path / f"{VALID_RUN_ID}.jsonl",
                             tmp_path / f"{VALID_RUN_ID}.verdict.yaml", "persisted")
        assert any(f.rule_id == "B7" and "entry.run_id" in f.message for f in findings)

    def test_basename_mismatch_fails(self, tmp_path: Path):
        e = make_valid_persisted_entry_minor()
        s = make_valid_sidecar()
        # sidecar path basename doesn't match run_id
        wrong_path = tmp_path / "totally-wrong-stem.meta.json"
        findings = check_b7(e, s, None, wrong_path, None, None, "persisted")
        assert any(f.rule_id == "B7" and "basename" in f.message for f in findings)


class TestB8:
    """B8 — verified_at == acknowledged_at on ack entries."""

    def test_matching_timestamps_pass(self):
        e = make_valid_persisted_entry_minor()
        e["verdict"]["status"] = "MATERIAL"
        e["verdict"]["finding_counts"] = {"p1": 1, "p2": 0, "p3": 0}
        e["acknowledgement"] = {
            "finding_ids": ["F-001"],
            "acknowledged_at": e["verdict"]["verified_at"],
            "acknowledged_by": "user",
        }
        assert check_b8(e, "persisted") == []

    def test_mismatched_timestamps_fail(self):
        e = make_valid_persisted_entry_minor()
        e["verdict"]["status"] = "MATERIAL"
        e["verdict"]["finding_counts"] = {"p1": 1, "p2": 0, "p3": 0}
        e["acknowledgement"] = {
            "finding_ids": ["F-001"],
            "acknowledged_at": "2026-04-30T16:00:00.000Z",
            "acknowledged_by": "user",
        }
        findings = check_b8(e, "persisted")
        assert any(f.rule_id == "B8" for f in findings)


class TestB9:
    """B9 — entry.bundle_id == sidecar.prompt.bundle.bundle_id (when present)."""

    def test_matching_bundle_id_passes(self):
        e = make_valid_persisted_entry_minor()
        s = make_valid_sidecar()
        assert check_b9(e, s) == []

    def test_no_bundle_id_skipped(self):
        e = make_valid_persisted_entry_minor()
        del e["bundle_id"]
        s = make_valid_sidecar()
        assert check_b9(e, s) == []

    def test_mismatched_bundle_id_fails(self):
        e = make_valid_persisted_entry_minor()
        s = make_valid_sidecar()
        s["prompt"]["bundle"]["bundle_id"] = "different-bundle"
        findings = check_b9(e, s)
        assert any(f.rule_id == "B9" for f in findings)


class TestB10:
    """B10 — ack finding_ids: non-empty + all exist + full coverage."""

    def test_full_coverage_passes(self):
        e = make_valid_persisted_entry_minor()
        e["verdict"]["status"] = "MATERIAL"
        e["verdict"]["finding_counts"] = {"p1": 1, "p2": 0, "p3": 0}
        e["acknowledgement"] = {
            "finding_ids": ["F-001"],
            "acknowledged_at": e["verdict"]["verified_at"],
            "acknowledged_by": "user",
        }
        v = make_valid_verdict_file_minor()
        v["verdict_status"] = "MATERIAL"
        v["finding_counts"] = {"p1": 1, "p2": 0, "p3": 0}
        v["findings"] = [{"id": "F-001", "severity": "P1", "dimension": "3.7",
                          "file": "x.md", "line": 1, "description": "x",
                          "suggested_fix": "y"}]
        assert check_b10(e, v, "persisted") == []

    def test_unknown_finding_id_fails(self):
        e = make_valid_persisted_entry_minor()
        e["verdict"]["status"] = "MATERIAL"
        e["verdict"]["finding_counts"] = {"p1": 1, "p2": 0, "p3": 0}
        e["acknowledgement"] = {
            "finding_ids": ["F-999"],
            "acknowledged_at": e["verdict"]["verified_at"],
            "acknowledged_by": "user",
        }
        v = make_valid_verdict_file_minor()
        v["verdict_status"] = "MATERIAL"
        v["finding_counts"] = {"p1": 1, "p2": 0, "p3": 0}
        v["findings"] = [{"id": "F-001", "severity": "P1", "dimension": "3.7",
                          "file": "x.md", "line": 1, "description": "x",
                          "suggested_fix": "y"}]
        findings = check_b10(e, v, "persisted")
        assert any(f.rule_id == "B10" and "unknown" in f.message for f in findings)

    def test_partial_coverage_fails(self):
        e = make_valid_persisted_entry_minor()
        e["verdict"]["status"] = "MATERIAL"
        e["verdict"]["finding_counts"] = {"p1": 2, "p2": 0, "p3": 0}
        e["acknowledgement"] = {
            "finding_ids": ["F-001"],
            "acknowledged_at": e["verdict"]["verified_at"],
            "acknowledged_by": "user",
        }
        v = make_valid_verdict_file_minor()
        v["verdict_status"] = "MATERIAL"
        v["finding_counts"] = {"p1": 2, "p2": 0, "p3": 0}
        v["findings"] = [
            {"id": "F-001", "severity": "P1", "dimension": "3.7",
             "file": "x.md", "line": 1, "description": "x", "suggested_fix": "y"},
            {"id": "F-002", "severity": "P1", "dimension": "3.7",
             "file": "x.md", "line": 2, "description": "y", "suggested_fix": "z"},
        ]
        findings = check_b10(e, v, "persisted")
        assert any(f.rule_id == "B10" and "coverage" in f.message for f in findings)

    def test_empty_finding_ids_fails(self):
        e = make_valid_persisted_entry_minor()
        e["verdict"]["status"] = "MATERIAL"
        e["verdict"]["finding_counts"] = {"p1": 1, "p2": 0, "p3": 0}
        e["acknowledgement"] = {
            "finding_ids": [],
            "acknowledged_at": e["verdict"]["verified_at"],
            "acknowledged_by": "user",
        }
        v = make_valid_verdict_file_minor()
        findings = check_b10(e, v, "persisted")
        assert any(f.rule_id == "B10" and "non-empty" in f.message for f in findings)


# ---------------------------------------------------------------------------
# Family C
# ---------------------------------------------------------------------------


class TestC1:
    """C1 — entry.verdict mirrors verdict file."""

    def test_matching_mirror_passes(self):
        e = make_valid_persisted_entry_minor()
        v = make_valid_verdict_file_minor()
        assert check_c1(e, v) == []

    def test_status_drift_fails(self):
        e = make_valid_persisted_entry_minor()
        v = make_valid_verdict_file_minor()
        v["verdict_status"] = "PASS"
        findings = check_c1(e, v)
        assert any(f.rule_id == "C1" and "status" in f.message for f in findings)

    def test_finding_counts_drift_fails(self):
        e = make_valid_persisted_entry_minor()
        v = make_valid_verdict_file_minor()
        v["finding_counts"] = {"p1": 0, "p2": 0, "p3": 5}
        findings = check_c1(e, v)
        assert any(f.rule_id == "C1" and "finding_counts" in f.message for f in findings)


class TestC2:
    """C2 — entry.bundle_manifest_sha == sidecar.bundle_manifest_sha."""

    def test_matching_sha_passes(self):
        e = make_valid_persisted_entry_minor()
        s = make_valid_sidecar()
        e["bundle_manifest_sha"] = s["prompt"]["bundle"]["bundle_manifest_sha"]
        assert check_c2(e, s) == []

    def test_drift_fails(self):
        e = make_valid_persisted_entry_minor()
        s = make_valid_sidecar()
        e["bundle_manifest_sha"] = "0" * 64
        findings = check_c2(e, s)
        assert any(f.rule_id == "C2" for f in findings)


class TestC3:
    """C3 — ack append copies prior entry byte-for-byte except verified_at/by."""

    def test_byte_for_byte_copy_passes(self):
        prior = make_valid_persisted_entry_minor()
        prior["verdict"]["status"] = "MATERIAL"
        prior["verdict"]["finding_counts"] = {"p1": 1, "p2": 0, "p3": 0}
        new = copy.deepcopy(prior)
        new["verdict"]["verified_at"] = "2026-04-30T15:24:00.000Z"  # bumped
        new["acknowledgement"] = {
            "finding_ids": ["F-001"],
            "acknowledged_at": new["verdict"]["verified_at"],
            "acknowledged_by": "user",
        }
        assert check_c3(new, prior) == []

    def test_drift_in_copied_field_fails(self):
        prior = make_valid_persisted_entry_minor()
        new = copy.deepcopy(prior)
        new["deliverable_sha"] = "f" * 64  # diverged
        new["verdict"]["verified_at"] = "2026-04-30T15:24:00.000Z"
        findings = check_c3(new, prior)
        assert any(f.rule_id == "C3" and "deliverable_sha" in f.message for f in findings)

    def test_same_verified_at_fails(self):
        prior = make_valid_persisted_entry_minor()
        new = copy.deepcopy(prior)  # same verified_at
        findings = check_c3(new, prior)
        assert any(f.rule_id == "C3" and "freshly set" in f.message for f in findings)


class TestC4:
    """C4 — entry.deliverable_sha == sidecar.primary[].sha (entry-side half of B2)."""

    def test_matching_passes(self):
        e = make_valid_persisted_entry_minor()
        s = make_valid_sidecar()
        assert check_c4(e, s) == []

    def test_drift_fails(self):
        e = make_valid_persisted_entry_minor()
        s = make_valid_sidecar()
        s["prompt"]["bundle"]["primary_deliverables"][0]["sha"] = "f" * 64
        findings = check_c4(e, s)
        assert any(f.rule_id == "C4" for f in findings)


# ---------------------------------------------------------------------------
# Family D
# ---------------------------------------------------------------------------


class TestD1:
    """D1 — duplicate verified_at within (stage,agent,sha,run_id) group."""

    def test_unique_verified_at_passes(self):
        e1 = make_valid_persisted_entry_minor()
        e2 = make_valid_persisted_entry_minor()
        e2["verdict"]["verified_at"] = "2026-04-30T15:23:12.847Z"
        e2["run_id"] = "2026-04-30T15-22-04Z-d8f4"  # different run
        assert check_d1([e1, e2]) == []

    def test_duplicate_verified_at_fails(self):
        e1 = make_valid_persisted_entry_minor()
        e2 = copy.deepcopy(e1)
        # same key + same verified_at → duplicate
        findings = check_d1([e1, e2])
        assert any(f.rule_id == "D1" for f in findings)


class TestD2:
    """D2 — proposals sharing started_at."""

    def test_distinct_started_at_passes(self):
        proposals = [
            {"sidecar": {"timing": {"started_at": "2026-04-30T15:22:04.123Z"}},
             "entry": {"run_id": "2026-04-30T15-22-04Z-aaaa"}},
            {"sidecar": {"timing": {"started_at": "2026-04-30T15:22:05.123Z"}},
             "entry": {"run_id": "2026-04-30T15-22-05Z-bbbb"}},
        ]
        assert check_d2(proposals) == []

    def test_shared_started_at_warns(self):
        proposals = [
            {"sidecar": {"timing": {"started_at": "2026-04-30T15:22:04.123Z"}},
             "entry": {"run_id": "2026-04-30T15-22-04Z-aaaa"}},
            {"sidecar": {"timing": {"started_at": "2026-04-30T15:22:04.123Z"}},
             "entry": {"run_id": "2026-04-30T15-22-04Z-bbbb"}},
        ]
        findings = check_d2(proposals)
        assert any(f.rule_id == "D2" for f in findings)


class TestD3:
    """D3 — verified_at strictly monotonic."""

    def test_monotonic_ledger_passes(self):
        e1 = make_valid_persisted_entry_minor()
        e2 = copy.deepcopy(e1)
        e2["verdict"]["verified_at"] = "2026-04-30T15:23:12.847Z"
        e2["run_id"] = "2026-04-30T15-22-04Z-d8f4"
        assert check_d3([e1, e2]) == []

    def test_non_monotonic_fails(self):
        e1 = make_valid_persisted_entry_minor()
        e2 = copy.deepcopy(e1)
        e2["verdict"]["verified_at"] = "2026-04-30T15:00:00.000Z"  # earlier than e1
        e2["run_id"] = "2026-04-30T15-22-04Z-d8f4"
        findings = check_d3([e1, e2])
        assert any(f.rule_id == "D3" for f in findings)


class TestD4:
    """D4 — surface the supersession requirement when proposal round is
    higher than persisted round (spec §3.7 family D + §5.6 A1.5)."""

    def test_higher_round_fires_supersession(self):
        # The lint should SURFACE the supersession (proposal preempts
        # persisted Path A) so the caller sees it before the orchestrator
        # processes the artifacts.
        findings = check_d4(persisted_round=2, proposal_round=3)
        assert any(f.rule_id == "D4" for f in findings)
        assert any("supersedes" in f.message for f in findings)

    def test_equal_round_no_supersession(self):
        # Same round — no supersession required; D4 is silent.
        assert check_d4(persisted_round=3, proposal_round=3) == []

    def test_lower_round_no_supersession(self):
        # Lower-round proposal — D4 silent (orchestrator should reject the
        # proposal at B1a as a stale leftover, but that's not D4's surface).
        assert check_d4(persisted_round=3, proposal_round=1) == []


# ---------------------------------------------------------------------------
# Family E
# ---------------------------------------------------------------------------


class TestE1E2E6:
    """E1/E2/E6 — passport-shape post-hoc detection."""

    def test_orchestrator_emitted_passes(self):
        e = make_valid_persisted_entry_minor()
        assert check_e1_e2_e6([e]) == []

    def test_missing_verified_by_fails(self):
        e = make_valid_persisted_entry_minor()
        del e["verdict"]["verified_by"]
        findings = check_e1_e2_e6([e])
        assert any(f.rule_id == "E1/E2/E6" for f in findings)

    def test_wrong_verified_by_fails(self):
        e = make_valid_persisted_entry_minor()
        e["verdict"]["verified_by"] = "totally_different_agent"
        findings = check_e1_e2_e6([e])
        assert any(f.rule_id == "E1/E2/E6" and "verified_by" in f.message for f in findings)


class TestE3E4:
    """E3/E4 — proposals carrying verified_at/verified_by are rejected."""

    def test_clean_proposal_passes(self):
        e = make_valid_proposal_entry_pass()
        assert check_e3_e4(e, "proposal") == []

    def test_proposal_with_verified_at_fails(self):
        e = make_valid_proposal_entry_pass()
        e["verdict"]["verified_at"] = "2026-04-30T15:23:11.847Z"
        findings = check_e3_e4(e, "proposal")
        assert any(f.rule_id == "E3/E4" and "verified_at" in f.message for f in findings)

    def test_proposal_with_verified_by_fails(self):
        e = make_valid_proposal_entry_pass()
        e["verdict"]["verified_by"] = "pipeline_orchestrator_agent"
        findings = check_e3_e4(e, "proposal")
        assert any(f.rule_id == "E3/E4" and "verified_by" in f.message for f in findings)


class TestE5:
    """E5 — persisted mode rejects AUDIT_FAILED."""

    def test_minor_persisted_passes(self):
        e = make_valid_persisted_entry_minor()
        assert check_e5(e, "persisted") == []

    def test_audit_failed_persisted_fails(self):
        e = make_valid_persisted_entry_minor()
        e["verdict"]["status"] = "AUDIT_FAILED"
        findings = check_e5(e, "persisted")
        assert any(f.rule_id == "E5" for f in findings)


class TestE7:
    """E7 — ack entry's status remains MATERIAL."""

    def test_material_with_ack_passes(self):
        e = make_valid_persisted_entry_minor()
        e["verdict"]["status"] = "MATERIAL"
        e["acknowledgement"] = {
            "finding_ids": ["F-001"],
            "acknowledged_at": e["verdict"]["verified_at"],
            "acknowledged_by": "user",
        }
        assert check_e7(e) == []

    def test_synthetic_status_with_ack_fails(self):
        e = make_valid_persisted_entry_minor()
        e["verdict"]["status"] = "MATERIAL_ACKNOWLEDGED"
        e["acknowledgement"] = {
            "finding_ids": ["F-001"],
            "acknowledged_at": e["verdict"]["verified_at"],
            "acknowledged_by": "user",
        }
        findings = check_e7(e)
        assert any(f.rule_id == "E7" for f in findings)


# ---------------------------------------------------------------------------
# Family F
# ---------------------------------------------------------------------------


class TestF1:
    """F1 — run_id format."""

    def test_canonical_run_id_passes(self):
        assert check_f1(VALID_RUN_ID) == []

    def test_wrong_format_fails(self):
        findings = check_f1("not-a-run-id")
        assert any(f.rule_id == "F1" for f in findings)

    def test_missing_run_id_fails(self):
        findings = check_f1(None)
        assert any(f.rule_id == "F1" for f in findings)


class TestF2:
    """F2 — bare-run_id basename + extensions."""

    def test_canonical_filenames_pass(self, tmp_path: Path):
        jsonl = tmp_path / f"{VALID_RUN_ID}.jsonl"
        sidecar = tmp_path / f"{VALID_RUN_ID}.meta.json"
        verdict = tmp_path / f"{VALID_RUN_ID}.verdict.yaml"
        entry = tmp_path / f"{VALID_RUN_ID}.audit_artifact_entry.json"
        assert check_f2(jsonl, sidecar, verdict, entry, "proposal") == []

    def test_stage_prefix_fails(self, tmp_path: Path):
        sidecar = tmp_path / f"stage2-synthesis-{VALID_RUN_ID}.meta.json"
        findings = check_f2(None, sidecar, None, None, "persisted")
        assert any(f.rule_id == "F2" for f in findings)

    def test_wrong_extension_fails(self, tmp_path: Path):
        sidecar = tmp_path / f"{VALID_RUN_ID}.json"  # missing .meta
        findings = check_f2(None, sidecar, None, None, "persisted")
        assert any(f.rule_id == "F2" for f in findings)


class TestF3:
    """F3 — sidecar.run_id == basename stem."""

    def test_matching_passes(self, tmp_path: Path):
        s = make_valid_sidecar()
        sidecar_path = tmp_path / f"{VALID_RUN_ID}.meta.json"
        assert check_f3(s, sidecar_path) == []

    def test_drift_fails(self, tmp_path: Path):
        s = make_valid_sidecar()
        s["run_id"] = "2026-04-30T15-22-04Z-aaaa"
        sidecar_path = tmp_path / f"{VALID_RUN_ID}.meta.json"
        findings = check_f3(s, sidecar_path)
        assert any(f.rule_id == "F3" for f in findings)


# ---------------------------------------------------------------------------
# Schema self-validation (verification gate item #1)
# ---------------------------------------------------------------------------


class TestSchemaSelfValidation:
    """Verification gate: each Phase 6.2 schema validates as Draft 2020-12."""

    @pytest.mark.parametrize("schema_name", [
        "audit_artifact_entry.schema.json",
        "audit_jsonl.schema.json",
        "audit_sidecar.schema.json",
        "audit_verdict.schema.json",
    ])
    def test_schema_meta_valid(self, schema_name):
        from tests.test_helpers import load_json_schema
        if "audit_jsonl" in schema_name or "audit_sidecar" in schema_name or "audit_verdict" in schema_name:
            path = REPO / "shared/contracts/audit" / schema_name
        else:
            path = REPO / "shared/contracts/passport" / schema_name
        schema = load_json_schema(path)
        assert "$schema" in schema


# ---------------------------------------------------------------------------
# Aggregator + CLI smoke tests
# ---------------------------------------------------------------------------


class TestAggregator:
    """run_checks should emit zero findings on a fully-valid synthetic bundle."""

    def test_clean_persisted_bundle_zero_findings(self, tmp_path: Path):
        sidecar = make_valid_sidecar()
        entry = make_valid_persisted_entry_minor()
        # align entry's bundle_manifest_sha with the sidecar's computed value
        entry["bundle_manifest_sha"] = sidecar["prompt"]["bundle"]["bundle_manifest_sha"]
        # Codex round 8 P2 closure: B7 now resolves entry.artifact_paths
        # against repo_root and verifies disk existence + samefile match
        # against CLI-loaded paths. Aggregator test writes placeholder
        # files at the recorded basename so the resolution succeeds.
        for ext in (".jsonl", ".meta.json", ".verdict.yaml",
                    ".audit_artifact_entry.json"):
            (tmp_path / f"{VALID_RUN_ID}{ext}").write_text("placeholder")
        ctx = LintContext(
            mode="persisted",
            entry=entry,
            entry_path=tmp_path / f"{VALID_RUN_ID}.audit_artifact_entry.json",
            sidecar=sidecar,
            sidecar_path=tmp_path / f"{VALID_RUN_ID}.meta.json",
            verdict=make_valid_verdict_file_minor(),
            verdict_path=tmp_path / f"{VALID_RUN_ID}.verdict.yaml",
            jsonl_events=make_valid_jsonl_events_no_tool(),
            jsonl_path=tmp_path / f"{VALID_RUN_ID}.jsonl",
            repo_root=tmp_path,  # no .git, no deliverable file: B4 skipped, B2 disk skipped
        )
        findings = run_checks(ctx)
        assert findings == [], "\n".join(f.render() for f in findings)

    def test_clean_proposal_bundle_zero_findings(self, tmp_path: Path):
        sidecar = make_valid_sidecar()
        entry = make_valid_proposal_entry_pass()
        entry["bundle_manifest_sha"] = sidecar["prompt"]["bundle"]["bundle_manifest_sha"]
        for ext in (".jsonl", ".meta.json", ".verdict.yaml",
                    ".audit_artifact_entry.json"):
            (tmp_path / f"{VALID_RUN_ID}{ext}").write_text("placeholder")
        ctx = LintContext(
            mode="proposal",
            entry=entry,
            entry_path=tmp_path / f"{VALID_RUN_ID}.audit_artifact_entry.json",
            sidecar=sidecar,
            sidecar_path=tmp_path / f"{VALID_RUN_ID}.meta.json",
            verdict=make_valid_verdict_file_pass(),
            verdict_path=tmp_path / f"{VALID_RUN_ID}.verdict.yaml",
            jsonl_events=make_valid_jsonl_events_no_tool(),
            jsonl_path=tmp_path / f"{VALID_RUN_ID}.jsonl",
            repo_root=tmp_path,
        )
        findings = run_checks(ctx)
        assert findings == [], "\n".join(f.render() for f in findings)

    def test_jsonl_stream_mode_clean(self, tmp_path: Path):
        ctx = LintContext(
            mode="jsonl-stream",
            jsonl_events=make_valid_jsonl_events_tool_using(),
            jsonl_path=tmp_path / f"{VALID_RUN_ID}.jsonl",
            repo_root=tmp_path,
        )
        assert run_checks(ctx) == []

    def test_jsonl_stream_mode_orphan_fails(self, tmp_path: Path):
        events = [
            {"type": "thread.started", "thread_id": VALID_THREAD_ID},
            {"type": "item.completed",
             "item": {"id": "orphan", "type": "command_execution"}},
        ]
        ctx = LintContext(
            mode="jsonl-stream",
            jsonl_events=events,
            jsonl_path=tmp_path / f"{VALID_RUN_ID}.jsonl",
            repo_root=tmp_path,
        )
        findings = run_checks(ctx)
        assert any(f.rule_id == "A7" for f in findings)


class TestCLI:
    """End-to-end CLI smoke tests using subprocess-style invocation through main()."""

    def test_jsonl_stream_clean_returns_0(self, tmp_path: Path, capsys):
        jsonl = tmp_path / f"{VALID_RUN_ID}.jsonl"
        events = make_valid_jsonl_events_tool_using()
        jsonl.write_text("\n".join(json.dumps(e) for e in events) + "\n")
        rc = main(["--mode", "jsonl-stream", "--jsonl", str(jsonl)])
        assert rc == 0

    def test_jsonl_stream_orphan_returns_1(self, tmp_path: Path):
        jsonl = tmp_path / f"{VALID_RUN_ID}.jsonl"
        events = [
            {"type": "thread.started", "thread_id": VALID_THREAD_ID},
            {"type": "item.completed",
             "item": {"id": "orphan", "type": "command_execution"}},
        ]
        jsonl.write_text("\n".join(json.dumps(e) for e in events) + "\n")
        rc = main(["--mode", "jsonl-stream", "--jsonl", str(jsonl)])
        assert rc == 1

    def test_persisted_clean_via_files(self, tmp_path: Path):
        # Write all four artifact files
        run_id = VALID_RUN_ID
        sidecar = make_valid_sidecar()
        entry = make_valid_persisted_entry_minor()
        entry["bundle_manifest_sha"] = sidecar["prompt"]["bundle"]["bundle_manifest_sha"]
        verdict = make_valid_verdict_file_minor()
        events = make_valid_jsonl_events_no_tool()
        (tmp_path / f"{run_id}.audit_artifact_entry.json").write_text(json.dumps(entry))
        (tmp_path / f"{run_id}.meta.json").write_text(json.dumps(sidecar))
        # verdict as YAML
        import yaml as _yaml
        (tmp_path / f"{run_id}.verdict.yaml").write_text(_yaml.safe_dump(verdict))
        (tmp_path / f"{run_id}.jsonl").write_text(
            "\n".join(json.dumps(e) for e in events) + "\n")
        rc = main([
            "--mode", "persisted",
            "--output-dir", str(tmp_path),
            "--run-id", run_id,
            "--repo-root", str(tmp_path),
        ])
        # zero findings -> rc == 0
        assert rc == 0

    def test_persisted_missing_sidecar_returns_1(self, tmp_path: Path, capsys):
        # Codex round 1 P1: missing companion artifacts must be rejected, not
        # silently ignored. Write entry + verdict + jsonl but NOT sidecar.
        run_id = VALID_RUN_ID
        entry = make_valid_persisted_entry_minor()
        verdict = make_valid_verdict_file_minor()
        events = make_valid_jsonl_events_no_tool()
        (tmp_path / f"{run_id}.audit_artifact_entry.json").write_text(json.dumps(entry))
        import yaml as _yaml
        (tmp_path / f"{run_id}.verdict.yaml").write_text(_yaml.safe_dump(verdict))
        (tmp_path / f"{run_id}.jsonl").write_text(
            "\n".join(json.dumps(e) for e in events) + "\n")
        rc = main([
            "--mode", "persisted",
            "--output-dir", str(tmp_path),
            "--run-id", run_id,
            "--repo-root", str(tmp_path),
        ])
        captured = capsys.readouterr()
        assert rc == 1, captured.out
        assert "B7" in captured.out
        assert "sidecar" in captured.out

    def test_persisted_mode_rejects_proposal_shape(self, tmp_path: Path, capsys):
        # Codex round 2 P1: --mode persisted must enforce persisted arm. A
        # proposal-shaped entry (no verified_at/verified_by) was silently
        # passing oneOf validation as the proposal arm.
        run_id = VALID_RUN_ID
        sidecar = make_valid_sidecar()
        # Build a proposal-shaped entry (no verified_at, no verified_by)
        entry = make_valid_persisted_entry_minor()
        entry["bundle_manifest_sha"] = sidecar["prompt"]["bundle"]["bundle_manifest_sha"]
        entry["verdict"].pop("verified_at", None)
        entry["verdict"].pop("verified_by", None)
        verdict = make_valid_verdict_file_minor()
        events = make_valid_jsonl_events_no_tool()
        (tmp_path / f"{run_id}.audit_artifact_entry.json").write_text(json.dumps(entry))
        (tmp_path / f"{run_id}.meta.json").write_text(json.dumps(sidecar))
        import yaml as _yaml
        (tmp_path / f"{run_id}.verdict.yaml").write_text(_yaml.safe_dump(verdict))
        (tmp_path / f"{run_id}.jsonl").write_text(
            "\n".join(json.dumps(e) for e in events) + "\n")
        rc = main([
            "--mode", "persisted",
            "--output-dir", str(tmp_path),
            "--run-id", run_id,
            "--repo-root", str(tmp_path),
        ])
        captured = capsys.readouterr()
        assert rc == 1, captured.out
        assert "E3" in captured.out
        assert "verified_at" in captured.out

    def test_persisted_mode_rejects_audit_failed(self, tmp_path: Path, capsys):
        # AUDIT_FAILED is proposal-only per §3.2 lifecycle-conditional table.
        run_id = VALID_RUN_ID
        sidecar = make_valid_sidecar()
        entry = make_valid_persisted_entry_minor()
        entry["bundle_manifest_sha"] = sidecar["prompt"]["bundle"]["bundle_manifest_sha"]
        entry["verdict"]["status"] = "AUDIT_FAILED"
        entry["verdict"]["failure_reason"] = "synthetic test"
        entry["verdict"]["finding_counts"] = {"p1": 0, "p2": 0, "p3": 0}
        verdict = make_valid_verdict_file_minor()
        events = make_valid_jsonl_events_no_tool()
        (tmp_path / f"{run_id}.audit_artifact_entry.json").write_text(json.dumps(entry))
        (tmp_path / f"{run_id}.meta.json").write_text(json.dumps(sidecar))
        import yaml as _yaml
        (tmp_path / f"{run_id}.verdict.yaml").write_text(_yaml.safe_dump(verdict))
        (tmp_path / f"{run_id}.jsonl").write_text(
            "\n".join(json.dumps(e) for e in events) + "\n")
        rc = main([
            "--mode", "persisted",
            "--output-dir", str(tmp_path),
            "--run-id", run_id,
            "--repo-root", str(tmp_path),
        ])
        captured = capsys.readouterr()
        assert rc == 1, captured.out
        assert "E5" in captured.out
        assert "AUDIT_FAILED" in captured.out

    def test_persisted_truncated_jsonl_rejected(self, tmp_path: Path, capsys):
        # Codex round 3 P1: JSONL with only thread.started + turn.started
        # has no A7 pairing violation but is incomplete evidence. Phase 6.1's
        # parse_audit_verdict.validate_stream_shape must run before A7 in
        # full mode (non-AUDIT_FAILED bundles).
        run_id = VALID_RUN_ID
        sidecar = make_valid_sidecar()
        entry = make_valid_persisted_entry_minor()
        entry["bundle_manifest_sha"] = sidecar["prompt"]["bundle"]["bundle_manifest_sha"]
        verdict = make_valid_verdict_file_minor()  # MINOR — non-AUDIT_FAILED
        # Truncated stream: opens correctly, never closes
        truncated_events = [
            {"type": "thread.started", "thread_id": VALID_THREAD_ID},
            {"type": "turn.started"},
        ]
        (tmp_path / f"{run_id}.audit_artifact_entry.json").write_text(json.dumps(entry))
        (tmp_path / f"{run_id}.meta.json").write_text(json.dumps(sidecar))
        import yaml as _yaml
        (tmp_path / f"{run_id}.verdict.yaml").write_text(_yaml.safe_dump(verdict))
        (tmp_path / f"{run_id}.jsonl").write_text(
            "\n".join(json.dumps(e) for e in truncated_events) + "\n")
        rc = main([
            "--mode", "persisted",
            "--output-dir", str(tmp_path),
            "--run-id", run_id,
            "--repo-root", str(tmp_path),
        ])
        captured = capsys.readouterr()
        assert rc == 1, captured.out
        assert "L2-3/L2-4" in captured.out or "stream-shape" in captured.out, captured.out

    def test_passport_scan_rejects_audit_failed(self, tmp_path: Path, capsys):
        # Codex round 3 P2: hand-edited passport entry with AUDIT_FAILED status
        # plus valid verified_at + verified_by must be flagged as forbidden.
        run_id = VALID_RUN_ID
        sidecar = make_valid_sidecar()
        entry = make_valid_persisted_entry_minor()
        entry["bundle_manifest_sha"] = sidecar["prompt"]["bundle"]["bundle_manifest_sha"]
        verdict = make_valid_verdict_file_minor()
        events = make_valid_jsonl_events_no_tool()
        (tmp_path / f"{run_id}.audit_artifact_entry.json").write_text(json.dumps(entry))
        (tmp_path / f"{run_id}.meta.json").write_text(json.dumps(sidecar))
        import yaml as _yaml
        (tmp_path / f"{run_id}.verdict.yaml").write_text(_yaml.safe_dump(verdict))
        (tmp_path / f"{run_id}.jsonl").write_text(
            "\n".join(json.dumps(e) for e in events) + "\n")
        # Passport with hand-edited AUDIT_FAILED entry that passes E1/E2/E6
        # presence checks (verified_at + verified_by both set, verified_by
        # is the canonical orchestrator value).
        passport = {
            "audit_artifact": [
                {
                    "stage": 2,
                    "agent": "synthesis_agent",
                    "deliverable_path": "chapter_4/synthesis.md",
                    "deliverable_sha": "a1b2c3d4e5f6a7b8c9d0e1f2a3b4c5d6e7f8a9b0c1d2e3f4a5b6c7d8e9f0a1b2",
                    "run_id": "2026-04-30T15-22-04Z-aaaa",
                    "bundle_manifest_sha": "9a8b7c6d5e4f3b2a1c0d9e8f7a6b5c4d3e2f1a0b9c8d7e6f5a4b3c2d1e0f9876",
                    "artifact_paths": {
                        "jsonl": "audit_artifacts/2026-04-30T15-22-04Z-aaaa.jsonl",
                        "sidecar": "audit_artifacts/2026-04-30T15-22-04Z-aaaa.meta.json",
                        "verdict": "audit_artifacts/2026-04-30T15-22-04Z-aaaa.verdict.yaml",
                    },
                    "verdict": {
                        "status": "AUDIT_FAILED",
                        "round": 1,
                        "target_rounds": 3,
                        "finding_counts": {"p1": 0, "p2": 0, "p3": 0},
                        "failure_reason": "hand-edited forgery",
                        "verified_at": "2026-04-30T15:23:11.847Z",
                        "verified_by": "pipeline_orchestrator_agent",
                    },
                }
            ]
        }
        passport_path = tmp_path / "passport.yaml"
        passport_path.write_text(_yaml.safe_dump(passport))
        rc = main([
            "--mode", "persisted",
            "--output-dir", str(tmp_path),
            "--run-id", run_id,
            "--passport-path", str(passport_path),
            "--repo-root", str(tmp_path),
        ])
        captured = capsys.readouterr()
        assert rc == 1, captured.out
        assert "E5" in captured.out
        assert "AUDIT_FAILED" in captured.out

    def test_persisted_forged_artifact_paths_in_entry(self, tmp_path: Path, capsys):
        # Codex round 4 P2: hand-edited entry.artifact_paths pointing at a
        # different run_id must be flagged as forgery seam, even when the
        # CLI is invoked with canonical --output-dir + --run-id and the
        # actual on-disk files have the canonical basename.
        run_id = VALID_RUN_ID
        sidecar = make_valid_sidecar()
        entry = make_valid_persisted_entry_minor()
        entry["bundle_manifest_sha"] = sidecar["prompt"]["bundle"]["bundle_manifest_sha"]
        # Forged: artifact_paths point at a DIFFERENT run_id's files
        entry["artifact_paths"] = {
            "jsonl": "audit_artifacts/2026-04-30T15-22-04Z-ffff.jsonl",
            "sidecar": "audit_artifacts/2026-04-30T15-22-04Z-ffff.meta.json",
            "verdict": "audit_artifacts/2026-04-30T15-22-04Z-ffff.verdict.yaml",
        }
        verdict = make_valid_verdict_file_minor()
        events = make_valid_jsonl_events_no_tool()
        (tmp_path / f"{run_id}.audit_artifact_entry.json").write_text(json.dumps(entry))
        (tmp_path / f"{run_id}.meta.json").write_text(json.dumps(sidecar))
        import yaml as _yaml
        (tmp_path / f"{run_id}.verdict.yaml").write_text(_yaml.safe_dump(verdict))
        (tmp_path / f"{run_id}.jsonl").write_text(
            "\n".join(json.dumps(e) for e in events) + "\n")
        rc = main([
            "--mode", "persisted",
            "--output-dir", str(tmp_path),
            "--run-id", run_id,
            "--repo-root", str(tmp_path),
        ])
        captured = capsys.readouterr()
        assert rc == 1, captured.out
        assert "B7" in captured.out
        assert "artifact-paths forgery seam" in captured.out

    def test_argparse_invalid_mode_returns_64(self):
        # Codex round 4 P3: argparse-level failures must exit 64, not 2.
        result = subprocess.run(
            [sys.executable, str(REPO / "scripts/check_audit_artifact_consistency.py"),
             "--mode", "definitely_not_a_mode"],
            capture_output=True, text=True,
        )
        assert result.returncode == 64, (
            f"argparse usage error returned {result.returncode}, expected 64\n"
            f"stderr: {result.stderr}"
        )

    def test_argparse_unknown_flag_returns_64(self):
        result = subprocess.run(
            [sys.executable, str(REPO / "scripts/check_audit_artifact_consistency.py"),
             "--bogus-flag"],
            capture_output=True, text=True,
        )
        assert result.returncode == 64, (
            f"unknown flag returned {result.returncode}, expected 64\n"
            f"stderr: {result.stderr}"
        )

    def test_persisted_ack_without_prior_rejected(self, tmp_path: Path, capsys):
        # Codex round 5 P1: a persisted ack entry whose copied fields don't
        # match any prior MATERIAL entry must be rejected, not silently
        # skipped. Previously `prior is None` skipped check_c3 entirely.
        run_id = VALID_RUN_ID
        sidecar = make_valid_sidecar()
        # Build a MATERIAL ack entry with NO matching prior in the passport.
        entry = make_valid_persisted_entry_minor()
        entry["bundle_manifest_sha"] = sidecar["prompt"]["bundle"]["bundle_manifest_sha"]
        entry["verdict"]["status"] = "MATERIAL"
        entry["verdict"]["finding_counts"] = {"p1": 1, "p2": 0, "p3": 0}
        entry["acknowledgement"] = {
            "finding_ids": ["F-001"],
            "acknowledged_at": entry["verdict"]["verified_at"],
            "acknowledged_by": "user",
        }
        verdict = make_valid_verdict_file_minor()
        verdict["verdict_status"] = "MATERIAL"
        verdict["finding_counts"] = {"p1": 1, "p2": 0, "p3": 0}
        verdict["findings"] = [{
            "id": "F-001", "severity": "P1", "dimension": "3.1",
            "file": "x.md", "line": 1,
            "description": "x", "suggested_fix": "y",
        }]
        events = make_valid_jsonl_events_no_tool()
        (tmp_path / f"{run_id}.audit_artifact_entry.json").write_text(json.dumps(entry))
        (tmp_path / f"{run_id}.meta.json").write_text(json.dumps(sidecar))
        import yaml as _yaml
        (tmp_path / f"{run_id}.verdict.yaml").write_text(_yaml.safe_dump(verdict))
        (tmp_path / f"{run_id}.jsonl").write_text(
            "\n".join(json.dumps(e) for e in events) + "\n")
        # Empty passport — no prior MATERIAL entry to copy from
        passport_path = tmp_path / "passport.yaml"
        passport_path.write_text(_yaml.safe_dump({"audit_artifact": []}))
        rc = main([
            "--mode", "persisted",
            "--output-dir", str(tmp_path),
            "--run-id", run_id,
            "--passport-path", str(passport_path),
            "--repo-root", str(tmp_path),
        ])
        captured = capsys.readouterr()
        assert rc == 1, captured.out
        assert "C3" in captured.out
        assert "no prior MATERIAL entry" in captured.out

    def test_non_dict_entry_returns_2(self, tmp_path: Path, capsys):
        # Codex round 5 traceback closure: a non-object entry payload (e.g., `[]`)
        # must surface as a clean error, not an AttributeError traceback.
        entry_path = tmp_path / "entry.json"
        entry_path.write_text("[]")
        rc = main([
            "--mode", "proposal",
            "--entry", str(entry_path),
            "--sidecar", str(tmp_path / "no.meta.json"),
            "--verdict", str(tmp_path / "no.verdict.yaml"),
            "--jsonl", str(tmp_path / "no.jsonl"),
            "--repo-root", str(tmp_path),
        ])
        captured = capsys.readouterr()
        assert rc == 2
        assert "is not a JSON object" in captured.err

    def test_stream_shape_runs_via_importlib(self, tmp_path: Path, capsys):
        # Codex round 5 P2: stream-shape gate must work via importlib, not
        # depend on scripts/ being on sys.path. Import this module under a
        # fresh `scripts` package qualifier and run main from there.
        run_id = VALID_RUN_ID
        sidecar = make_valid_sidecar()
        entry = make_valid_persisted_entry_minor()
        entry["bundle_manifest_sha"] = sidecar["prompt"]["bundle"]["bundle_manifest_sha"]
        verdict = make_valid_verdict_file_minor()  # MINOR — non-AUDIT_FAILED
        truncated_events = [
            {"type": "thread.started", "thread_id": VALID_THREAD_ID},
            {"type": "turn.started"},
        ]
        (tmp_path / f"{run_id}.audit_artifact_entry.json").write_text(json.dumps(entry))
        (tmp_path / f"{run_id}.meta.json").write_text(json.dumps(sidecar))
        import yaml as _yaml
        (tmp_path / f"{run_id}.verdict.yaml").write_text(_yaml.safe_dump(truncated_events[0]))  # placeholder
        (tmp_path / f"{run_id}.verdict.yaml").write_text(_yaml.safe_dump(verdict))
        (tmp_path / f"{run_id}.jsonl").write_text(
            "\n".join(json.dumps(e) for e in truncated_events) + "\n")
        # Run via subprocess so we exercise the actual import path the gate
        # uses (importlib loads parse_audit_verdict by file path).
        result = subprocess.run(
            [sys.executable, str(REPO / "scripts/check_audit_artifact_consistency.py"),
             "--mode", "persisted",
             "--output-dir", str(tmp_path),
             "--run-id", run_id,
             "--repo-root", str(tmp_path)],
            capture_output=True, text=True,
        )
        assert result.returncode == 1, result.stdout + result.stderr
        assert "L2-3/L2-4" in result.stdout or "stream-shape" in result.stdout, result.stdout

    def test_audit_failed_skips_a7_pairing(self, tmp_path: Path, capsys):
        # Codex round 6 P2: AUDIT_FAILED bundles legitimately have truncated
        # streams. A7 pairing must be suspended for them, mirroring the
        # round-3 stream-shape suspension and §3.4 Layer 3 suspension.
        run_id = VALID_RUN_ID
        sidecar = make_valid_sidecar()
        # AUDIT_FAILED jsonl_thread_id is allowed to be empty per §3.4
        sidecar["stream"]["jsonl_thread_id"] = ""
        entry = make_valid_persisted_entry_minor()
        entry["bundle_manifest_sha"] = sidecar["prompt"]["bundle"]["bundle_manifest_sha"]
        # Entry needs to be a proposal (AUDIT_FAILED is proposal-only)
        # — switch CLI mode to proposal for this test.
        entry["verdict"].pop("verified_at", None)
        entry["verdict"].pop("verified_by", None)
        entry["verdict"]["status"] = "AUDIT_FAILED"
        entry["verdict"]["finding_counts"] = {"p1": 0, "p2": 0, "p3": 0}
        entry["verdict"]["failure_reason"] = "synthetic — codex killed"
        verdict = make_valid_verdict_file_minor()
        verdict["verdict_status"] = "AUDIT_FAILED"
        verdict["finding_counts"] = {"p1": 0, "p2": 0, "p3": 0}
        verdict["findings"] = []
        verdict["failure_reason"] = "synthetic — codex killed"
        # Truncated stream with unmatched item.started — would fail A7 if
        # pairing weren't suspended for AUDIT_FAILED
        truncated_events = [
            {"type": "thread.started", "thread_id": VALID_THREAD_ID},
            {"type": "turn.started"},
            {"type": "item.started",
             "item": {"id": "killed_tool", "type": "command_execution"}},
        ]
        (tmp_path / f"{run_id}.audit_artifact_entry.json").write_text(json.dumps(entry))
        (tmp_path / f"{run_id}.meta.json").write_text(json.dumps(sidecar))
        import yaml as _yaml
        (tmp_path / f"{run_id}.verdict.yaml").write_text(_yaml.safe_dump(verdict))
        (tmp_path / f"{run_id}.jsonl").write_text(
            "\n".join(json.dumps(e) for e in truncated_events) + "\n")
        rc = main([
            "--mode", "proposal",
            "--output-dir", str(tmp_path),
            "--run-id", run_id,
            "--repo-root", str(tmp_path),
        ])
        captured = capsys.readouterr()
        # No A7 finding should appear — AUDIT_FAILED suspends pairing
        assert "A7" not in captured.out, (
            f"AUDIT_FAILED bundle should not produce A7 findings — got: {captured.out}"
        )

    def test_non_object_sidecar_no_traceback(self, tmp_path: Path, capsys):
        # Codex round 6 P2: a non-object sidecar must surface as SCHEMA
        # finding without crashing cross-field checks.
        run_id = VALID_RUN_ID
        entry = make_valid_persisted_entry_minor()
        verdict = make_valid_verdict_file_minor()
        events = make_valid_jsonl_events_no_tool()
        (tmp_path / f"{run_id}.audit_artifact_entry.json").write_text(json.dumps(entry))
        (tmp_path / f"{run_id}.meta.json").write_text("[]")  # non-object
        import yaml as _yaml
        (tmp_path / f"{run_id}.verdict.yaml").write_text(_yaml.safe_dump(verdict))
        (tmp_path / f"{run_id}.jsonl").write_text(
            "\n".join(json.dumps(e) for e in events) + "\n")
        rc = main([
            "--mode", "persisted",
            "--output-dir", str(tmp_path),
            "--run-id", run_id,
            "--repo-root", str(tmp_path),
        ])
        captured = capsys.readouterr()
        assert rc == 1, captured.out
        assert "SCHEMA" in captured.out, captured.out
        # No traceback in stderr
        assert "AttributeError" not in captured.err
        assert "Traceback" not in captured.err

    def test_non_object_verdict_no_traceback(self, tmp_path: Path, capsys):
        run_id = VALID_RUN_ID
        sidecar = make_valid_sidecar()
        entry = make_valid_persisted_entry_minor()
        entry["bundle_manifest_sha"] = sidecar["prompt"]["bundle"]["bundle_manifest_sha"]
        events = make_valid_jsonl_events_no_tool()
        (tmp_path / f"{run_id}.audit_artifact_entry.json").write_text(json.dumps(entry))
        (tmp_path / f"{run_id}.meta.json").write_text(json.dumps(sidecar))
        (tmp_path / f"{run_id}.verdict.yaml").write_text("[]")  # non-object
        (tmp_path / f"{run_id}.jsonl").write_text(
            "\n".join(json.dumps(e) for e in events) + "\n")
        rc = main([
            "--mode", "persisted",
            "--output-dir", str(tmp_path),
            "--run-id", run_id,
            "--repo-root", str(tmp_path),
        ])
        captured = capsys.readouterr()
        assert rc == 1, captured.out
        assert "SCHEMA" in captured.out, captured.out
        assert "AttributeError" not in captured.err
        assert "Traceback" not in captured.err

    def test_jsonl_lacks_section6_verdict_text_rejected(self, tmp_path: Path, capsys):
        # Codex round 8 P1: stream-shape passes but verdict text is not a
        # parseable Section 6 → must be rejected as L2-4 finding.
        run_id = VALID_RUN_ID
        sidecar = make_valid_sidecar()
        entry = make_valid_persisted_entry_minor()
        entry["bundle_manifest_sha"] = sidecar["prompt"]["bundle"]["bundle_manifest_sha"]
        verdict = make_valid_verdict_file_minor()
        # Stream-shape valid but agent_message has no Section 6 summary
        events = [
            {"type": "thread.started", "thread_id": VALID_THREAD_ID},
            {"type": "turn.started"},
            {"type": "item.completed",
             "item": {"id": "item_0", "type": "agent_message",
                      "text": "I considered the bundle and decided everything looks fine."}},
            {"type": "turn.completed",
             "usage": {"input_tokens": 100, "cached_input_tokens": 0,
                       "output_tokens": 50, "reasoning_output_tokens": 25}},
        ]
        (tmp_path / f"{run_id}.audit_artifact_entry.json").write_text(json.dumps(entry))
        (tmp_path / f"{run_id}.meta.json").write_text(json.dumps(sidecar))
        import yaml as _yaml
        (tmp_path / f"{run_id}.verdict.yaml").write_text(_yaml.safe_dump(verdict))
        (tmp_path / f"{run_id}.jsonl").write_text(
            "\n".join(json.dumps(e) for e in events) + "\n")
        rc = main([
            "--mode", "persisted",
            "--output-dir", str(tmp_path),
            "--run-id", run_id,
            "--repo-root", str(tmp_path),
        ])
        captured = capsys.readouterr()
        assert rc == 1, captured.out
        assert "L2-4" in captured.out, captured.out
        assert "Section 6" in captured.out, captured.out

    def test_artifact_path_resolves_to_missing_file_rejected(self, tmp_path: Path, capsys):
        # Codex round 8 P2: entry.artifact_paths recording a path that
        # resolves under repo_root to a missing file must be flagged.
        run_id = VALID_RUN_ID
        sidecar = make_valid_sidecar()
        entry = make_valid_persisted_entry_minor()
        entry["bundle_manifest_sha"] = sidecar["prompt"]["bundle"]["bundle_manifest_sha"]
        # Recorded paths point at a sibling subdir that doesn't exist
        entry["artifact_paths"] = {
            "jsonl": f"missing_subdir/{run_id}.jsonl",
            "sidecar": f"missing_subdir/{run_id}.meta.json",
            "verdict": f"missing_subdir/{run_id}.verdict.yaml",
        }
        verdict = make_valid_verdict_file_minor()
        events = make_valid_jsonl_events_no_tool()
        (tmp_path / f"{run_id}.audit_artifact_entry.json").write_text(json.dumps(entry))
        (tmp_path / f"{run_id}.meta.json").write_text(json.dumps(sidecar))
        import yaml as _yaml
        (tmp_path / f"{run_id}.verdict.yaml").write_text(_yaml.safe_dump(verdict))
        (tmp_path / f"{run_id}.jsonl").write_text(
            "\n".join(json.dumps(e) for e in events) + "\n")
        rc = main([
            "--mode", "persisted",
            "--output-dir", str(tmp_path),
            "--run-id", run_id,
            "--repo-root", str(tmp_path),
        ])
        captured = capsys.readouterr()
        assert rc == 1, captured.out
        assert "B7" in captured.out
        assert "does not exist on disk" in captured.out

    def test_audit_failed_skips_layer_3_b2_b3_b4_b5_b7(self, tmp_path: Path, capsys):
        # Codex round 9 P2: Layer 3 cross-file rules (B2/B3/B4/B5/B7) are
        # suspended for AUDIT_FAILED bundles per §3.4 + §5.6 Path B5. A
        # failed audit caused by bundle mutation legitimately has live
        # deliverable SHA != recorded SHA; treating that as B2 violation
        # would reject the failure-signaling artifact.
        run_id = VALID_RUN_ID
        sidecar = make_valid_sidecar()
        sidecar["stream"]["jsonl_thread_id"] = ""  # AUDIT_FAILED suspension
        # Forensic exit_code per §3.4 rule 6 — non-zero allowed for AUDIT_FAILED
        sidecar["process"]["exit_code"] = 70
        # Drift the bundle SHA in sidecar so live recompute would mismatch (if
        # B3 ran). With AUDIT_FAILED suspension, B3 must NOT fire.
        sidecar["prompt"]["bundle"]["primary_deliverables"][0]["sha"] = "f" * 64
        # Drift git_sha to a bogus hex that fails B4 git cat-file (if it ran).
        sidecar["runner"]["git_sha"] = "deadbee"
        # Drift duration vs end-start by >>1s so B5 would fire (if it ran).
        sidecar["timing"]["duration_seconds"] = 9999.0
        entry = make_valid_persisted_entry_minor()
        entry["bundle_manifest_sha"] = sidecar["prompt"]["bundle"]["bundle_manifest_sha"]
        entry["verdict"].pop("verified_at", None)
        entry["verdict"].pop("verified_by", None)
        entry["verdict"]["status"] = "AUDIT_FAILED"
        entry["verdict"]["finding_counts"] = {"p1": 0, "p2": 0, "p3": 0}
        entry["verdict"]["failure_reason"] = "synthetic — codex killed"
        # Drift entry.deliverable_sha so B2 entry-vs-sidecar would fire (if
        # it ran) — entry side not suspended internally, only Layer 3 is.
        entry["deliverable_sha"] = "c" * 64
        verdict = make_valid_verdict_file_minor()
        verdict["verdict_status"] = "AUDIT_FAILED"
        verdict["finding_counts"] = {"p1": 0, "p2": 0, "p3": 0}
        verdict["findings"] = []
        verdict["failure_reason"] = "synthetic — codex killed"
        # Truncated stream — AUDIT_FAILED expected
        events = [
            {"type": "thread.started", "thread_id": VALID_THREAD_ID},
            {"type": "turn.started"},
            # codex was killed before final agent_message + turn.completed
        ]
        (tmp_path / f"{run_id}.audit_artifact_entry.json").write_text(json.dumps(entry))
        (tmp_path / f"{run_id}.meta.json").write_text(json.dumps(sidecar))
        import yaml as _yaml
        (tmp_path / f"{run_id}.verdict.yaml").write_text(_yaml.safe_dump(verdict))
        (tmp_path / f"{run_id}.jsonl").write_text(
            "\n".join(json.dumps(e) for e in events) + "\n")
        rc = main([
            "--mode", "proposal",
            "--output-dir", str(tmp_path),
            "--run-id", run_id,
            "--repo-root", str(tmp_path),
        ])
        captured = capsys.readouterr()
        # B2/B3/B4/B5/B7 must not fire — AUDIT_FAILED suspends Layer 3
        for rule in ("B2", "B3", "B4", "B5", "B7"):
            assert f"[{rule}]" not in captured.out, (
                f"{rule} fired on AUDIT_FAILED bundle but Layer 3 should be "
                f"suspended per §3.4: {captured.out}"
            )

    def test_audit_failed_with_partial_jsonl_no_internal_error(self, tmp_path: Path, capsys):
        # Codex round 11 P2: AUDIT_FAILED bundle with partial/non-JSON last
        # line (codex SIGKILL'd mid-write) must NOT exit 2 internal error.
        # Round 9 suspended schema validation but _load_jsonl() still raised
        # before reaching that suspension.
        run_id = VALID_RUN_ID
        sidecar = make_valid_sidecar()
        sidecar["stream"]["jsonl_thread_id"] = ""
        sidecar["process"]["exit_code"] = 137  # 128 + SIGKILL
        entry = make_valid_persisted_entry_minor()
        entry["bundle_manifest_sha"] = sidecar["prompt"]["bundle"]["bundle_manifest_sha"]
        entry["verdict"].pop("verified_at", None)
        entry["verdict"].pop("verified_by", None)
        entry["verdict"]["status"] = "AUDIT_FAILED"
        entry["verdict"]["finding_counts"] = {"p1": 0, "p2": 0, "p3": 0}
        entry["verdict"]["failure_reason"] = "synthetic — codex SIGKILL"
        verdict = make_valid_verdict_file_minor()
        verdict["verdict_status"] = "AUDIT_FAILED"
        verdict["finding_counts"] = {"p1": 0, "p2": 0, "p3": 0}
        verdict["findings"] = []
        verdict["failure_reason"] = "synthetic — codex SIGKILL"
        # Partial JSON on the last line — would raise ValueError in
        # _load_jsonl and previously caused exit 2.
        partial_jsonl = (
            json.dumps({"type": "thread.started", "thread_id": VALID_THREAD_ID}) + "\n"
            + json.dumps({"type": "turn.started"}) + "\n"
            + '{"type":"item.start'  # truncated mid-write, no closing quote/brace
        )
        (tmp_path / f"{run_id}.audit_artifact_entry.json").write_text(json.dumps(entry))
        (tmp_path / f"{run_id}.meta.json").write_text(json.dumps(sidecar))
        import yaml as _yaml
        (tmp_path / f"{run_id}.verdict.yaml").write_text(_yaml.safe_dump(verdict))
        (tmp_path / f"{run_id}.jsonl").write_text(partial_jsonl)
        rc = main([
            "--mode", "proposal",
            "--output-dir", str(tmp_path),
            "--run-id", run_id,
            "--repo-root", str(tmp_path),
        ])
        captured = capsys.readouterr()
        # Must NOT be rc=2 (internal error). Forensic-only bundle is allowed.
        assert rc != 2, (
            f"AUDIT_FAILED with partial JSONL returned rc=2 internal error; "
            f"should be handled as forensic-only bundle\nstdout: {captured.out}\n"
            f"stderr: {captured.err}"
        )

    def test_schema_error_short_circuits_no_traceback(self, tmp_path: Path, capsys):
        # Codex round 12 P2: schema-valid-as-dict but with a nested field of
        # the wrong shape (timing: [1] passes top-level isinstance(dict) but
        # timing.get() crashes in check_b5). Short-circuit on SCHEMA error
        # so cross-field rules don't crash on input violating their type
        # presuppositions.
        run_id = VALID_RUN_ID
        sidecar = make_valid_sidecar()
        # Inject malformed nested field that schema rejects but isinstance
        # at the top level still passes:
        sidecar["timing"] = [1, 2, 3]  # list instead of dict
        entry = make_valid_persisted_entry_minor()
        entry["bundle_manifest_sha"] = sidecar["prompt"]["bundle"]["bundle_manifest_sha"]
        verdict = make_valid_verdict_file_minor()
        events = make_valid_jsonl_events_no_tool()
        (tmp_path / f"{run_id}.audit_artifact_entry.json").write_text(json.dumps(entry))
        (tmp_path / f"{run_id}.meta.json").write_text(json.dumps(sidecar))
        import yaml as _yaml
        (tmp_path / f"{run_id}.verdict.yaml").write_text(_yaml.safe_dump(verdict))
        (tmp_path / f"{run_id}.jsonl").write_text(
            "\n".join(json.dumps(e) for e in events) + "\n")
        rc = main([
            "--mode", "persisted",
            "--output-dir", str(tmp_path),
            "--run-id", run_id,
            "--repo-root", str(tmp_path),
        ])
        captured = capsys.readouterr()
        assert rc == 1, captured.out
        assert "SCHEMA" in captured.out, captured.out
        # Critical: no traceback must reach stderr
        assert "Traceback" not in captured.err, captured.err
        assert "AttributeError" not in captured.err, captured.err

    def test_persisted_with_higher_round_proposal_fires_d4(self, tmp_path: Path, capsys):
        # Codex round 13 P2: when --mode persisted runs and --output-dir
        # contains a higher-round unmerged proposal for the same (stage,
        # agent, deliverable_sha) tuple, D4 must fire (the persisted
        # entry's Path A is supposed to be preempted).
        run_id = VALID_RUN_ID
        # Persisted entry at round 1
        sidecar = make_valid_sidecar()
        entry = make_valid_persisted_entry_minor()
        entry["verdict"]["round"] = 1
        entry["bundle_manifest_sha"] = sidecar["prompt"]["bundle"]["bundle_manifest_sha"]
        verdict = make_valid_verdict_file_minor()
        verdict["round"] = 1  # match entry round
        events = make_valid_jsonl_events_no_tool()
        # Move persisted into a consumed/ subdir so the scan doesn't see
        # it as an unmerged proposal (matches §4.9 step 9 convention).
        consumed = tmp_path / "consumed"
        consumed.mkdir()
        (consumed / f"{run_id}.audit_artifact_entry.json").write_text(json.dumps(entry))
        # Companion files in output_dir (where the lint expects them)
        (tmp_path / f"{run_id}.meta.json").write_text(json.dumps(sidecar))
        import yaml as _yaml
        (tmp_path / f"{run_id}.verdict.yaml").write_text(_yaml.safe_dump(verdict))
        (tmp_path / f"{run_id}.jsonl").write_text(
            "\n".join(json.dumps(e) for e in events) + "\n")

        # Higher-round proposal in output_dir (round 2 > persisted round 1)
        proposal_run_id = "2026-04-30T15-30-00Z-eeee"
        proposal_entry = make_valid_persisted_entry_minor()
        proposal_entry["verdict"]["round"] = 2  # higher than persisted round=1
        proposal_entry["verdict"]["status"] = "PASS"
        proposal_entry["verdict"]["finding_counts"] = {"p1": 0, "p2": 0, "p3": 0}
        proposal_entry["verdict"].pop("verified_at", None)  # proposal arm
        proposal_entry["verdict"].pop("verified_by", None)
        proposal_entry["run_id"] = proposal_run_id
        proposal_entry["artifact_paths"] = {
            "jsonl": f"{proposal_run_id}.jsonl",
            "sidecar": f"{proposal_run_id}.meta.json",
            "verdict": f"{proposal_run_id}.verdict.yaml",
        }
        (tmp_path / f"{proposal_run_id}.audit_artifact_entry.json").write_text(
            json.dumps(proposal_entry))

        rc = main([
            "--mode", "persisted",
            "--entry", str(consumed / f"{run_id}.audit_artifact_entry.json"),
            "--output-dir", str(tmp_path),
            "--run-id", run_id,
            "--repo-root", str(tmp_path),
        ])
        captured = capsys.readouterr()
        assert rc == 1, captured.out
        assert "D4" in captured.out, captured.out
        assert "round=2" in captured.out and "round=1" in captured.out, captured.out

    def test_script_is_executable(self):
        # Codex round 14 P1: spec §5.2 L2-5 invokes the lint as
        # `scripts/check_audit_artifact_consistency.py --mode jsonl-stream …`
        # without a `python` prefix. The file must carry the executable
        # bit (100755) like Phase 6.1's audit_snapshot.py / parse_audit_
        # verdict.py / run_codex_audit.sh — direct exec failing with
        # permission denied (exit 126) would block the orchestrator gate.
        import os
        script_path = REPO / "scripts/check_audit_artifact_consistency.py"
        assert os.access(script_path, os.X_OK), (
            f"{script_path} must be executable for orchestrator §5.2 L2-5 "
            f"direct invocation. Run `chmod +x` and `git update-index --chmod=+x`."
        )

    def test_script_runs_via_direct_exec(self):
        # End-to-end smoke: invoke the script directly (no `python` prefix)
        # and confirm it produces the documented harness exit code. Belt
        # and braces against future `chmod 644` regressions.
        script_path = REPO / "scripts/check_audit_artifact_consistency.py"
        result = subprocess.run(
            [str(script_path), "--example-validation-harness"],
            capture_output=True, text=True,
        )
        assert result.returncode == 0, (
            f"direct exec returned {result.returncode} (expected 0)\n"
            f"stdout: {result.stdout}\nstderr: {result.stderr}"
        )

    def test_swap_verdict_file_with_different_run_id_rejected(self, tmp_path: Path, capsys):
        # Codex round 15 P1: swap-one-verdict-file forgery — a verdict.yaml
        # with all valid schema/cross-field but internal run_id pointing at
        # a different run, renamed into the canonical <run_id>.verdict.yaml
        # slot. C1 mirrors only the nested verdict block; B7 (pre-round-15)
        # checked sidecar.run_id but not verdict.run_id.
        run_id = VALID_RUN_ID
        sidecar = make_valid_sidecar()
        entry = make_valid_persisted_entry_minor()
        entry["bundle_manifest_sha"] = sidecar["prompt"]["bundle"]["bundle_manifest_sha"]
        verdict = make_valid_verdict_file_minor()
        verdict["run_id"] = "2026-04-30T15-30-00Z-ffff"  # different run!
        events = make_valid_jsonl_events_no_tool()
        (tmp_path / f"{run_id}.audit_artifact_entry.json").write_text(json.dumps(entry))
        (tmp_path / f"{run_id}.meta.json").write_text(json.dumps(sidecar))
        import yaml as _yaml
        (tmp_path / f"{run_id}.verdict.yaml").write_text(_yaml.safe_dump(verdict))
        (tmp_path / f"{run_id}.jsonl").write_text(
            "\n".join(json.dumps(e) for e in events) + "\n")
        rc = main([
            "--mode", "persisted",
            "--output-dir", str(tmp_path),
            "--run-id", run_id,
            "--repo-root", str(tmp_path),
        ])
        captured = capsys.readouterr()
        assert rc == 1, captured.out
        assert "B7" in captured.out
        assert "verdict.run_id" in captured.out
        assert "swap-one-verdict-file forgery" in captured.out

    def test_only_entry_flag_resolves_companions_from_artifact_paths(self, tmp_path: Path, capsys):
        # Codex round 16 P2: caller passes only --entry + --repo-root; the
        # lint must resolve sidecar/verdict/jsonl from
        # entry.artifact_paths instead of demanding redundant flags.
        run_id = VALID_RUN_ID
        sidecar = make_valid_sidecar()
        entry = make_valid_persisted_entry_minor()
        entry["bundle_manifest_sha"] = sidecar["prompt"]["bundle"]["bundle_manifest_sha"]
        verdict = make_valid_verdict_file_minor()
        events = make_valid_jsonl_events_no_tool()
        # Companion files in tmp_path; entry.artifact_paths records them
        # as repo-relative basenames (matching the round-7+8 fixture
        # convention).
        (tmp_path / f"{run_id}.audit_artifact_entry.json").write_text(json.dumps(entry))
        (tmp_path / f"{run_id}.meta.json").write_text(json.dumps(sidecar))
        import yaml as _yaml
        (tmp_path / f"{run_id}.verdict.yaml").write_text(_yaml.safe_dump(verdict))
        (tmp_path / f"{run_id}.jsonl").write_text(
            "\n".join(json.dumps(e) for e in events) + "\n")
        # ONLY --entry + --repo-root, no --output-dir, no --sidecar/verdict/jsonl
        rc = main([
            "--mode", "persisted",
            "--entry", str(tmp_path / f"{run_id}.audit_artifact_entry.json"),
            "--repo-root", str(tmp_path),
        ])
        captured = capsys.readouterr()
        assert rc == 0, captured.out

    def test_persisted_schema_invalid_sidecar_returns_1(self, tmp_path: Path, capsys):
        # Codex round 1 P2: schema-invalid sidecar must be rejected even when
        # cross-field rules don't cover the malformed field.
        run_id = VALID_RUN_ID
        sidecar = make_valid_sidecar()
        # Inject a malformed bare extra field (additionalProperties: false on
        # sidecar root → schema rejects unknown top-level key).
        sidecar["definitely_not_in_schema"] = "drift"
        entry = make_valid_persisted_entry_minor()
        entry["bundle_manifest_sha"] = sidecar["prompt"]["bundle"]["bundle_manifest_sha"]
        verdict = make_valid_verdict_file_minor()
        events = make_valid_jsonl_events_no_tool()
        (tmp_path / f"{run_id}.audit_artifact_entry.json").write_text(json.dumps(entry))
        (tmp_path / f"{run_id}.meta.json").write_text(json.dumps(sidecar))
        import yaml as _yaml
        (tmp_path / f"{run_id}.verdict.yaml").write_text(_yaml.safe_dump(verdict))
        (tmp_path / f"{run_id}.jsonl").write_text(
            "\n".join(json.dumps(e) for e in events) + "\n")
        rc = main([
            "--mode", "persisted",
            "--output-dir", str(tmp_path),
            "--run-id", run_id,
            "--repo-root", str(tmp_path),
        ])
        captured = capsys.readouterr()
        assert rc == 1, captured.out
        assert "SCHEMA" in captured.out
        assert "definitely_not_in_schema" in captured.out


# ---------------------------------------------------------------------------
# Example validation harness (F4) — smoke test it runs without crash
# ---------------------------------------------------------------------------


class TestExampleHarness:
    """F4 — example-validation-harness runs end-to-end on the real spec dir."""

    def test_harness_runs(self):
        # Should not raise; may produce findings (known §3.4 hyphen drift)
        findings = run_example_harness(REPO)
        # We don't assert zero findings — the spec is known to have drift the
        # harness should surface. We only assert the harness ran and any
        # findings it produces are well-formed LintErrors.
        assert all(isinstance(f, LintError) for f in findings)
        # And every finding's rule_id is "F4" or "SCHEMA"-prefixed
        for f in findings:
            assert f.rule_id in ("F4", "SCHEMA"), f.render()


# ---------------------------------------------------------------------------
# Fixture smoke tests — codex round 7 P2 closure
# ---------------------------------------------------------------------------


FIXTURE_ROOT = REPO / "scripts/fixtures/audit_artifact_consistency"


class TestFixtureSmoke:
    """Verify scripts/fixtures/audit_artifact_consistency/ README invocation
    examples actually produce the documented exit codes.

    Codex round 7 P2: positive fixtures only pass when --repo-root points
    at the fixture directory itself (so B3's live-disk gate hits the
    synthetic-fixture safe-skip via missing .git/ marker). Without this
    test, README drift could leave positive fixtures silently broken
    against the documented invocation.
    """

    def test_positive_persisted_minor(self):
        bundle = FIXTURE_ROOT / "positive/persisted_minor"
        result = subprocess.run(
            [sys.executable, str(REPO / "scripts/check_audit_artifact_consistency.py"),
             "--mode", "persisted",
             "--output-dir", str(bundle),
             "--run-id", "2026-04-30T15-22-04Z-d8f3",
             "--repo-root", str(bundle)],
            capture_output=True, text=True,
        )
        assert result.returncode == 0, (
            f"positive fixture persisted_minor returned {result.returncode}\n"
            f"stdout: {result.stdout}\nstderr: {result.stderr}"
        )

    def test_positive_proposal_pass(self):
        bundle = FIXTURE_ROOT / "positive/proposal_pass"
        result = subprocess.run(
            [sys.executable, str(REPO / "scripts/check_audit_artifact_consistency.py"),
             "--mode", "proposal",
             "--output-dir", str(bundle),
             "--run-id", "2026-04-30T15-22-04Z-d8f3",
             "--repo-root", str(bundle)],
            capture_output=True, text=True,
        )
        assert result.returncode == 0, (
            f"positive fixture proposal_pass returned {result.returncode}\n"
            f"stdout: {result.stdout}\nstderr: {result.stderr}"
        )

    def test_negative_a1_pass_with_p1(self):
        bundle = FIXTURE_ROOT / "negative/a1_pass_with_p1"
        result = subprocess.run(
            [sys.executable, str(REPO / "scripts/check_audit_artifact_consistency.py"),
             "--mode", "proposal",
             "--output-dir", str(bundle),
             "--run-id", "2026-04-30T15-22-04Z-d8f3",
             "--repo-root", str(bundle)],
            capture_output=True, text=True,
        )
        assert result.returncode == 1, result.stdout
        assert "A1" in result.stdout, result.stdout

    def test_negative_a7_orphan_completion(self):
        jsonl = FIXTURE_ROOT / "negative/a7_orphan_completion/2026-04-30T15-22-04Z-d8f3.jsonl"
        result = subprocess.run(
            [sys.executable, str(REPO / "scripts/check_audit_artifact_consistency.py"),
             "--mode", "jsonl-stream",
             "--jsonl", str(jsonl)],
            capture_output=True, text=True,
        )
        assert result.returncode == 1, result.stdout
        assert "A7" in result.stdout, result.stdout
