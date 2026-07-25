"""Phase 6.2 acceptance tests for the four v3.6.7 Step 6 audit schemas.

Per spec §10 verification gate:
  1. All four schemas parse as valid JSON Schema 2020-12.
  2. Example payloads in §3.1 / §3.3 / §3.4 / §3.5 validate against their
     respective schemas (positive cases).
  3. Deliberately-malformed counter-examples fail (negative cases).

This is the schema-shape acceptance test. Cross-artifact invariants
(§3.7 family A-F rows, --mode {proposal,persisted} arms, mirror rules,
ordering rules) ship in scripts/check_audit_artifact_consistency.py +
scripts/test_check_audit_artifact_consistency.py at Phase 6.3.

Run:
    python -m unittest scripts.test_audit_schemas -v
"""
from __future__ import annotations

import unittest
from pathlib import Path
from typing import Any

from tests.test_helpers import build_schema_validator, load_json_schema

REPO = Path(__file__).resolve().parent.parent
PASSPORT = REPO / "shared/contracts/passport"
AUDIT = REPO / "shared/contracts/audit"

SCHEMA_PATHS: dict[str, Path] = {
    "entry": PASSPORT / "audit_artifact_entry.schema.json",
    "jsonl": AUDIT / "audit_jsonl.schema.json",
    "sidecar": AUDIT / "audit_sidecar.schema.json",
    "verdict": AUDIT / "audit_verdict.schema.json",
}


# ---------------------------------------------------------------------------
# Positive examples — drawn directly from spec §3.1 / §3.3 / §3.4 / §3.5.
# ---------------------------------------------------------------------------

# §3.1 / §3.2 — persisted entry (verified_at + verified_by present, MINOR)
ENTRY_PERSISTED_MINOR: dict[str, Any] = {
    "stage": 2,
    "agent": "synthesis_agent",
    "deliverable_path": "chapter_4/synthesis.md",
    "deliverable_sha": "a" * 64,
    "run_id": "2026-04-30T15-22-04Z-d8f3",
    "bundle_id": "phase2-chapter4-2026-04-30",
    "bundle_manifest_sha": "9" * 64,
    "artifact_paths": {
        "jsonl": "audit_artifacts/2026-04-30T15-22-04Z-d8f3.jsonl",
        "sidecar": "audit_artifacts/2026-04-30T15-22-04Z-d8f3.meta.json",
        "verdict": "audit_artifacts/2026-04-30T15-22-04Z-d8f3.verdict.yaml",
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

# §3.2 — proposal entry (verified_at + verified_by absent)
ENTRY_PROPOSAL_PASS: dict[str, Any] = {
    "stage": 2,
    "agent": "synthesis_agent",
    "deliverable_path": "chapter_4/synthesis.md",
    "deliverable_sha": "b" * 64,
    "run_id": "2026-04-30T15-22-04Z-d8f3",
    "bundle_manifest_sha": "9" * 64,
    "artifact_paths": {
        "jsonl": "audit_artifacts/2026-04-30T15-22-04Z-d8f3.jsonl",
        "sidecar": "audit_artifacts/2026-04-30T15-22-04Z-d8f3.meta.json",
        "verdict": "audit_artifacts/2026-04-30T15-22-04Z-d8f3.verdict.yaml",
    },
    "verdict": {
        "status": "PASS",
        "round": 1,
        "target_rounds": 3,
        "finding_counts": {"p1": 0, "p2": 0, "p3": 0},
    },
}

# §3.2 — proposal AUDIT_FAILED (proposal-arm only, persisted excludes per §3.2)
ENTRY_PROPOSAL_AUDIT_FAILED: dict[str, Any] = {
    "stage": 2,
    "agent": "synthesis_agent",
    "deliverable_path": "chapter_4/synthesis.md",
    "deliverable_sha": "c" * 64,
    "run_id": "2026-04-30T15-22-04Z-d8f3",
    "bundle_manifest_sha": "9" * 64,
    "artifact_paths": {
        "jsonl": "audit_artifacts/2026-04-30T15-22-04Z-d8f3.jsonl",
        "sidecar": "audit_artifacts/2026-04-30T15-22-04Z-d8f3.meta.json",
        "verdict": "audit_artifacts/2026-04-30T15-22-04Z-d8f3.verdict.yaml",
    },
    "verdict": {
        "status": "AUDIT_FAILED",
        "failure_reason": "codex exit 70: network timeout after 600s",
        "round": 2,
        "target_rounds": 3,
        "finding_counts": {"p1": 0, "p2": 0, "p3": 0},
    },
}

# §3.3 — canonical four-event JSONL run (one validate per event row)
JSONL_THREAD_STARTED: dict[str, Any] = {
    "type": "thread.started",
    "thread_id": "019de371-4c13-7521-8af7-fccf6bd23279",
}
JSONL_TURN_STARTED: dict[str, Any] = {"type": "turn.started"}
# Empirically confirmed against codex 0.125 in tool-using runs: item.started
# precedes the matching item.completed for command_execution etc. Spec §3.3
# table didn't list it but the wire format requires it; Layer 2 schema accepts.
JSONL_ITEM_STARTED_TOOL: dict[str, Any] = {
    "type": "item.started",
    "item": {"id": "item_1", "type": "command_execution"},
}
JSONL_ITEM_COMPLETED: dict[str, Any] = {
    "type": "item.completed",
    "item": {"id": "item_0", "type": "agent_message", "text": "verdict text"},
}
JSONL_ITEM_COMPLETED_TOOL: dict[str, Any] = {
    "type": "item.completed",
    "item": {"id": "item_1", "type": "command_execution"},
}
JSONL_TURN_COMPLETED: dict[str, Any] = {
    "type": "turn.completed",
    "usage": {
        "input_tokens": 12345,
        "cached_input_tokens": 0,
        "output_tokens": 678,
        "reasoning_output_tokens": 90,
    },
}

# §3.4 — sidecar example (clean run)
SIDECAR_CLEAN: dict[str, Any] = {
    "run_id": "2026-04-30T15-22-04Z-d8f3",
    "codex_cli_version": "0.125.0",
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
        "stdout_path": "audit_artifacts/2026-04-30T15-22-04Z-d8f3.stdout",
        "stderr_path": "audit_artifacts/2026-04-30T15-22-04Z-d8f3.stderr",
    },
    "stream": {"jsonl_thread_id": "019de371-4c13-7521-8af7-fccf6bd23279"},
    "prompt": {
        "audit_template_path": "shared/templates/codex_audit_multifile_template.md",
        "audit_template_sha": "f" * 64,
        "bundle": {
            "bundle_id": "phase2-chapter4-2026-04-30",
            "bundle_manifest_sha": "9" * 64,
            "primary_deliverables": [
                {"path": "chapter_4/synthesis.md", "sha": "a" * 64},
            ],
            "supporting_context": [
                {"path": "chapter_4/bibliography.json", "sha": "e" * 64},
                {"path": "chapter_4/verification.md", "sha": "c" * 64},
            ],
        },
    },
}

# §3.4 — AUDIT_FAILED sidecar (jsonl_thread_id may be empty string)
SIDECAR_AUDIT_FAILED: dict[str, Any] = {
    **SIDECAR_CLEAN,
    "process": {**SIDECAR_CLEAN["process"], "exit_code": 70},
    "stream": {"jsonl_thread_id": ""},
}

# §3.5 — verdict file (clean MINOR)
VERDICT_MINOR: dict[str, Any] = {
    "run_id": "2026-04-30T15-22-04Z-d8f3",
    "verdict_status": "MINOR",
    "round": 2,
    "target_rounds": 3,
    "finding_counts": {"p1": 0, "p2": 0, "p3": 1},
    "findings": [
        {
            "id": "F-007",
            "severity": "P3",
            "dimension": "3.7",
            "file": "chapter_4/synthesis.md",
            "line": 482,
            "description": "deictic temporal phrase 'currently' on reflexivity disclosure",
            "suggested_fix": "replace with 'as of 2026-04-30' or 'former director'",
        }
    ],
    "generated_at": "2026-04-30T15:22:58.471Z",
    "generated_by": "scripts/run_codex_audit.sh",
    "generator_version": "1.0.0",
}

# §3.5 — verdict file (AUDIT_FAILED variant)
VERDICT_AUDIT_FAILED: dict[str, Any] = {
    "run_id": "2026-04-30T15-22-04Z-d8f3",
    "verdict_status": "AUDIT_FAILED",
    "round": 2,
    "target_rounds": 3,
    "finding_counts": {"p1": 0, "p2": 0, "p3": 0},
    "failure_reason": "codex exit 70: network timeout after 600s",
    "findings": [],
    "generated_at": "2026-04-30T15:22:58.471Z",
    "generated_by": "scripts/run_codex_audit.sh",
    "generator_version": "1.0.0",
}


# ---------------------------------------------------------------------------
# Negative examples — schema MUST reject each.
# ---------------------------------------------------------------------------

# Persisted-shape entry whose verdict.status is not in the persisted enum.
# (Removing verified_at alone falls into the proposal arm — that's a lint-side
# rule, not schema-side. See Phase 6.3 lint for --mode persisted enforcement.)
NEG_ENTRY_PERSISTED_BAD_STATUS: dict[str, Any] = {
    **{k: v for k, v in ENTRY_PERSISTED_MINOR.items() if k != "verdict"},
    "verdict": {
        "status": "INVALID",
        "round": 2,
        "target_rounds": 3,
        "finding_counts": {"p1": 0, "p2": 0, "p3": 1},
        "verified_at": "2026-04-30T15:23:11.847Z",
        "verified_by": "pipeline_orchestrator_agent",
    },
}

# §3.7 A2 — AUDIT_FAILED proposal without failure_reason must reject so that
# Path B5 short-circuit always has a reason string to surface in the BLOCK
# message (mirrors the verdict-file rule).
NEG_ENTRY_PROPOSAL_AUDIT_FAILED_NO_REASON = {
    **{k: v for k, v in ENTRY_PROPOSAL_AUDIT_FAILED.items() if k != "verdict"},
    "verdict": {
        k: v
        for k, v in ENTRY_PROPOSAL_AUDIT_FAILED["verdict"].items()
        if k != "failure_reason"
    },
}
# §3.7 A2 inverse — non-AUDIT_FAILED proposal carrying failure_reason must reject.
NEG_ENTRY_PROPOSAL_PASS_WITH_FAILURE_REASON = {
    **ENTRY_PROPOSAL_PASS,
    "verdict": {
        **ENTRY_PROPOSAL_PASS["verdict"],
        "failure_reason": "should not be here",
    },
}

NEG_ENTRY_BAD_AGENT = {**ENTRY_PERSISTED_MINOR, "agent": "rogue_agent"}
NEG_ENTRY_BAD_RUN_ID = {**ENTRY_PERSISTED_MINOR, "run_id": "not-an-iso-id"}
NEG_ENTRY_BAD_SHA = {**ENTRY_PERSISTED_MINOR, "deliverable_sha": "tooshort"}
# Path safety on artifact_paths: jsonl/sidecar/verdict MUST be repo-relative.
# Path B reads these to locate evidence; absolute or escaping paths would let a
# forged proposal point verification outside the repo.
NEG_ENTRY_ARTIFACT_PATH_ABSOLUTE = {
    **ENTRY_PERSISTED_MINOR,
    "artifact_paths": {
        **ENTRY_PERSISTED_MINOR["artifact_paths"],
        "jsonl": "/tmp/forged.jsonl",
    },
}
NEG_ENTRY_ARTIFACT_PATH_DOTDOT = {
    **ENTRY_PERSISTED_MINOR,
    "artifact_paths": {
        **ENTRY_PERSISTED_MINOR["artifact_paths"],
        "verdict": "../../forged.verdict.yaml",
    },
}
# Path safety on deliverable_path:
NEG_ENTRY_DELIVERABLE_PATH_ABSOLUTE = {**ENTRY_PERSISTED_MINOR, "deliverable_path": "/etc/passwd"}
NEG_ENTRY_DELIVERABLE_PATH_DOTDOT = {**ENTRY_PERSISTED_MINOR, "deliverable_path": "../../secret.md"}

# §3.7 A4 — acknowledgement requires verdict.status == MATERIAL.
# Schema-level if/then guard blocks the hand-edit attack where someone
# adds acknowledgement to a PASS / MINOR persisted entry.
_VALID_ACK = {
    "finding_ids": ["F-001"],
    "acknowledged_at": "2026-04-30T15:23:11.847Z",
    "acknowledged_by": "user",
}
NEG_ENTRY_PERSISTED_MINOR_WITH_ACK = {**ENTRY_PERSISTED_MINOR, "acknowledgement": _VALID_ACK}
_PASS_ENTRY = {
    **{k: v for k, v in ENTRY_PERSISTED_MINOR.items() if k != "verdict"},
    "verdict": {
        "status": "PASS",
        "round": 1,
        "target_rounds": 3,
        "finding_counts": {"p1": 0, "p2": 0, "p3": 0},
        "verified_at": "2026-04-30T15:23:11.847Z",
        "verified_by": "pipeline_orchestrator_agent",
    },
}
NEG_ENTRY_PERSISTED_PASS_WITH_ACK = {**_PASS_ENTRY, "acknowledgement": _VALID_ACK}

# Positive: MATERIAL persisted entry with acknowledgement is the canonical
# §5.4 ship_with_known_residue shape — must validate.
ENTRY_PERSISTED_MATERIAL_WITH_ACK = {
    **{k: v for k, v in ENTRY_PERSISTED_MINOR.items() if k != "verdict"},
    "verdict": {
        "status": "MATERIAL",
        "round": 3,
        "target_rounds": 3,
        "finding_counts": {"p1": 1, "p2": 0, "p3": 0},
        "verified_at": "2026-04-30T15:23:11.847Z",
        "verified_by": "pipeline_orchestrator_agent",
    },
    "acknowledgement": _VALID_ACK,
}

NEG_JSONL_THREAD_STARTED_NO_ID = {"type": "thread.started"}
NEG_JSONL_UNKNOWN_TYPE = {"type": "totally.fake", "thread_id": "abc"}
NEG_JSONL_TURN_COMPLETED_NO_USAGE = {"type": "turn.completed"}
# 36-char garbage (all dashes / all hex without separators) must NOT pass —
# canonical UUID 8-4-4-4-12 layout closes the Layer 2 forgery seam.
NEG_JSONL_THREAD_ID_ALL_DASHES = {
    "type": "thread.started",
    "thread_id": "------------------------------------",
}
NEG_JSONL_THREAD_ID_NO_SEPARATORS = {
    "type": "thread.started",
    "thread_id": "0123456789abcdef0123456789abcdef0123",  # 36 hex, no dashes
}
# item.started must reject extra top-level fields (consistency with other arms).
NEG_JSONL_ITEM_STARTED_EXTRA_TOP_FIELD = {
    "type": "item.started",
    "item": {"id": "item_1", "type": "command_execution"},
    "rogue": "should not validate",
}

NEG_SIDECAR_BAD_VERSION = {**SIDECAR_CLEAN, "codex_cli_version": "0.125"}
NEG_SIDECAR_NO_STREAM = {**SIDECAR_CLEAN, "stream": {}}
NEG_SIDECAR_WRONG_TEMPLATE = {
    **SIDECAR_CLEAN,
    "prompt": {**SIDECAR_CLEAN["prompt"], "audit_template_path": "wrong/path.md"},
}
# Path safety: bundle file_ref / process paths MUST be repo-relative POSIX.
# Layer 3 lint hashes these for SHA-256 / freshness checks; an absolute or
# escaping path would let a forged sidecar drive the verifier into arbitrary
# files outside the repo.
NEG_SIDECAR_BUNDLE_ESCAPING_PATH = {
    **SIDECAR_CLEAN,
    "prompt": {
        **SIDECAR_CLEAN["prompt"],
        "bundle": {
            **SIDECAR_CLEAN["prompt"]["bundle"],
            "primary_deliverables": [{"path": "../../secret.md", "sha": "a" * 64}],
        },
    },
}
NEG_SIDECAR_BUNDLE_ABSOLUTE_PATH = {
    **SIDECAR_CLEAN,
    "prompt": {
        **SIDECAR_CLEAN["prompt"],
        "bundle": {
            **SIDECAR_CLEAN["prompt"]["bundle"],
            "primary_deliverables": [{"path": "/etc/passwd", "sha": "a" * 64}],
        },
    },
}
NEG_SIDECAR_PROCESS_ESCAPING_STDOUT = {
    **SIDECAR_CLEAN,
    "process": {**SIDECAR_CLEAN["process"], "stdout_path": "../../oops.txt"},
}

NEG_VERDICT_BAD_STATUS = {**VERDICT_MINOR, "verdict_status": "WHATEVER"}
NEG_VERDICT_AUDIT_FAILED_NO_REASON = {
    k: v for k, v in VERDICT_AUDIT_FAILED.items() if k != "failure_reason"
}


class TestSchemasParseAsDraft202012(unittest.TestCase):
    """Verification gate 1: every schema is valid JSON Schema 2020-12."""

    def test_every_schema_file_exists_and_parses(self) -> None:
        for name, path in SCHEMA_PATHS.items():
            with self.subTest(schema=name):
                self.assertTrue(path.exists(), f"missing schema: {path.relative_to(REPO)}")
                # load_json_schema raises if the schema isn't valid 2020-12
                load_json_schema(path)


class _SchemaTestBase(unittest.TestCase):
    """Subclasses set `schema_key`; setUp loads the validator once per class."""

    schema_key: str = ""

    @classmethod
    def setUpClass(cls) -> None:
        super().setUpClass()
        if not cls.schema_key:
            return
        cls._validator = build_schema_validator(load_json_schema(SCHEMA_PATHS[cls.schema_key]))

    def assertValid(self, doc: dict[str, Any]) -> None:
        errors = list(self._validator.iter_errors(doc))
        if errors:
            msg = "; ".join(f"{list(e.absolute_path) or '<root>'}: {e.message}" for e in errors)
            self.fail(f"expected valid, got: {msg}")

    def assertInvalid(self, doc: dict[str, Any]) -> None:
        errors = list(self._validator.iter_errors(doc))
        self.assertGreater(len(errors), 0, "expected schema rejection, got pass")


class TestEntrySchema(_SchemaTestBase):
    schema_key = "entry"

    def test_persisted_minor(self) -> None:
        self.assertValid(ENTRY_PERSISTED_MINOR)

    def test_proposal_pass(self) -> None:
        self.assertValid(ENTRY_PROPOSAL_PASS)

    def test_proposal_audit_failed(self) -> None:
        self.assertValid(ENTRY_PROPOSAL_AUDIT_FAILED)

    def test_persisted_material_with_acknowledgement(self) -> None:
        self.assertValid(ENTRY_PERSISTED_MATERIAL_WITH_ACK)

    def test_rejects_persisted_with_bad_status(self) -> None:
        self.assertInvalid(NEG_ENTRY_PERSISTED_BAD_STATUS)

    def test_rejects_persisted_minor_with_acknowledgement(self) -> None:
        # A4 hand-edit attack: someone adds acknowledgement to a MINOR entry
        # to claim residue acknowledgement that the §5.4 prompt never solicited.
        self.assertInvalid(NEG_ENTRY_PERSISTED_MINOR_WITH_ACK)

    def test_rejects_persisted_pass_with_acknowledgement(self) -> None:
        self.assertInvalid(NEG_ENTRY_PERSISTED_PASS_WITH_ACK)

    def test_rejects_audit_failed_proposal_without_failure_reason(self) -> None:
        self.assertInvalid(NEG_ENTRY_PROPOSAL_AUDIT_FAILED_NO_REASON)

    def test_rejects_pass_proposal_with_failure_reason(self) -> None:
        self.assertInvalid(NEG_ENTRY_PROPOSAL_PASS_WITH_FAILURE_REASON)

    def test_rejects_artifact_path_absolute(self) -> None:
        self.assertInvalid(NEG_ENTRY_ARTIFACT_PATH_ABSOLUTE)

    def test_rejects_artifact_path_dotdot(self) -> None:
        self.assertInvalid(NEG_ENTRY_ARTIFACT_PATH_DOTDOT)

    def test_rejects_deliverable_path_absolute(self) -> None:
        self.assertInvalid(NEG_ENTRY_DELIVERABLE_PATH_ABSOLUTE)

    def test_rejects_deliverable_path_dotdot(self) -> None:
        self.assertInvalid(NEG_ENTRY_DELIVERABLE_PATH_DOTDOT)

    def test_rejects_unknown_agent(self) -> None:
        self.assertInvalid(NEG_ENTRY_BAD_AGENT)

    def test_rejects_malformed_run_id(self) -> None:
        self.assertInvalid(NEG_ENTRY_BAD_RUN_ID)

    def test_rejects_short_deliverable_sha(self) -> None:
        self.assertInvalid(NEG_ENTRY_BAD_SHA)


class TestJsonlSchema(_SchemaTestBase):
    schema_key = "jsonl"

    def test_thread_started(self) -> None:
        self.assertValid(JSONL_THREAD_STARTED)

    def test_turn_started(self) -> None:
        self.assertValid(JSONL_TURN_STARTED)

    def test_item_completed_agent_message(self) -> None:
        self.assertValid(JSONL_ITEM_COMPLETED)

    def test_item_completed_tool_execution(self) -> None:
        # tool-using runs emit completed events for non-agent_message item types
        # (no text field expected).
        self.assertValid(JSONL_ITEM_COMPLETED_TOOL)

    def test_item_started_tool_execution(self) -> None:
        # codex 0.125 emits item.started before matching item.completed for
        # tool calls (command_execution, file_change, etc.).
        self.assertValid(JSONL_ITEM_STARTED_TOOL)

    def test_turn_completed(self) -> None:
        self.assertValid(JSONL_TURN_COMPLETED)

    def test_rejects_thread_started_without_id(self) -> None:
        self.assertInvalid(NEG_JSONL_THREAD_STARTED_NO_ID)

    def test_rejects_unknown_event_type(self) -> None:
        self.assertInvalid(NEG_JSONL_UNKNOWN_TYPE)

    def test_rejects_turn_completed_without_usage(self) -> None:
        self.assertInvalid(NEG_JSONL_TURN_COMPLETED_NO_USAGE)

    def test_rejects_thread_id_all_dashes(self) -> None:
        self.assertInvalid(NEG_JSONL_THREAD_ID_ALL_DASHES)

    def test_rejects_thread_id_without_separators(self) -> None:
        self.assertInvalid(NEG_JSONL_THREAD_ID_NO_SEPARATORS)

    def test_rejects_item_started_with_extra_top_field(self) -> None:
        self.assertInvalid(NEG_JSONL_ITEM_STARTED_EXTRA_TOP_FIELD)


class TestSidecarSchema(_SchemaTestBase):
    schema_key = "sidecar"

    def test_clean_run(self) -> None:
        self.assertValid(SIDECAR_CLEAN)

    def test_audit_failed_run_with_empty_thread_id(self) -> None:
        self.assertValid(SIDECAR_AUDIT_FAILED)

    def test_rejects_non_semver_codex_version(self) -> None:
        self.assertInvalid(NEG_SIDECAR_BAD_VERSION)

    def test_rejects_missing_jsonl_thread_id(self) -> None:
        self.assertInvalid(NEG_SIDECAR_NO_STREAM)

    def test_rejects_non_canonical_template_path(self) -> None:
        self.assertInvalid(NEG_SIDECAR_WRONG_TEMPLATE)

    def test_rejects_bundle_path_with_dotdot(self) -> None:
        self.assertInvalid(NEG_SIDECAR_BUNDLE_ESCAPING_PATH)

    def test_rejects_bundle_absolute_path(self) -> None:
        self.assertInvalid(NEG_SIDECAR_BUNDLE_ABSOLUTE_PATH)

    def test_rejects_process_stdout_path_escaping(self) -> None:
        self.assertInvalid(NEG_SIDECAR_PROCESS_ESCAPING_STDOUT)


class TestVerdictSchema(_SchemaTestBase):
    schema_key = "verdict"

    def test_clean_minor(self) -> None:
        self.assertValid(VERDICT_MINOR)

    def test_audit_failed(self) -> None:
        self.assertValid(VERDICT_AUDIT_FAILED)

    def test_rejects_unknown_status(self) -> None:
        self.assertInvalid(NEG_VERDICT_BAD_STATUS)

    def test_rejects_audit_failed_without_failure_reason(self) -> None:
        self.assertInvalid(NEG_VERDICT_AUDIT_FAILED_NO_REASON)


if __name__ == "__main__":
    unittest.main()
