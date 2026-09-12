#!/usr/bin/env python3
"""TC Record Validator — Schema validation + state machine enforcement.

Validates TC records against the canonical schema, enforces state machine
transitions, and provides utilities for TC ID generation.

Usage:
    python validate_tc.py <path_to_tc_record.json>
    python validate_tc.py --registry <path_to_tc_registry.json>

Exit codes:
    0 = VALID
    1 = VALIDATION ERRORS (printed to stdout)
    2 = FILE NOT FOUND or JSON PARSE ERROR
"""

from __future__ import annotations

import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

VALID_STATUSES = ("planned", "in_progress", "blocked", "implemented", "tested", "deployed")

VALID_TRANSITIONS: dict[str, list[str]] = {
    "planned":      ["in_progress", "blocked"],
    "in_progress":  ["blocked", "implemented"],
    "blocked":      ["in_progress", "planned"],
    "implemented":  ["tested", "in_progress"],
    "tested":       ["deployed", "in_progress"],
    "deployed":     ["in_progress"],
}

VALID_SCOPES = ("feature", "bugfix", "refactor", "infrastructure", "documentation", "hotfix", "enhancement")
VALID_PRIORITIES = ("critical", "high", "medium", "low")
VALID_FILE_ACTIONS = ("created", "modified", "deleted", "renamed")
VALID_TEST_STATUSES = ("pending", "pass", "fail", "skip", "blocked")
VALID_EVIDENCE_TYPES = ("log_snippet", "screenshot", "file_reference", "command_output")
VALID_FIELD_CHANGE_ACTIONS = ("set", "changed", "added", "removed")
VALID_PLATFORMS = ("claude_code", "claude_web", "api", "other")
VALID_EFFORTS = ("trivial", "small", "medium", "large", "epic", None)
VALID_COVERAGE = ("none", "partial", "full")
VALID_FILE_IN_PROGRESS_STATES = ("editing", "needs_review", "partially_done", "ready")

TC_ID_PATTERN = re.compile(r"^TC-\d{3}-\d{2}-\d{2}-\d{2}-[a-z0-9]+(-[a-z0-9]+)*$")
SUB_TC_PATTERN = re.compile(r"^TC-\d{3}\.[A-Z](\.\d+)?$")
REVISION_ID_PATTERN = re.compile(r"^R(\d+)$")
TEST_ID_PATTERN = re.compile(r"^T(\d+)$")


# ---------------------------------------------------------------------------
# Validation Functions
# ---------------------------------------------------------------------------

def validate_tc_id(tc_id: str) -> list[str]:
    """Validate a TC identifier against the naming convention.

    Returns empty list if valid, list of error strings otherwise.
    """
    errors: list[str] = []
    if not isinstance(tc_id, str):
        errors.append(f"tc_id must be a string, got {type(tc_id).__name__}")
        return errors
    if not TC_ID_PATTERN.match(tc_id):
        errors.append(
            f"tc_id '{tc_id}' does not match pattern TC-NNN-MM-DD-YY-slug "
            f"(e.g., TC-001-04-03-26-user-authentication)"
        )
    return errors


def validate_sub_tc_id(sub_id: str) -> list[str]:
    """Validate a sub-TC identifier."""
    errors: list[str] = []
    if not isinstance(sub_id, str):
        errors.append(f"sub_id must be a string, got {type(sub_id).__name__}")
        return errors
    if not SUB_TC_PATTERN.match(sub_id):
        errors.append(
            f"sub_id '{sub_id}' does not match pattern TC-NNN.A or TC-NNN.A.N "
            f"(e.g., TC-001.A or TC-001.A.1)"
        )
    return errors


def validate_state_transition(current_status: str, new_status: str) -> list[str]:
    """Validate a state machine transition.

    Same-status transitions (no-ops) are allowed.
    Returns empty list if valid, list of error strings otherwise.
    """
    errors: list[str] = []
    if current_status not in VALID_STATUSES:
        errors.append(f"Current status '{current_status}' is not valid. Must be one of: {', '.join(VALID_STATUSES)}")
    if new_status not in VALID_STATUSES:
        errors.append(f"New status '{new_status}' is not valid. Must be one of: {', '.join(VALID_STATUSES)}")
    if errors:
        return errors

    # Same-status is a no-op, always valid
    if current_status == new_status:
        return []

    allowed = VALID_TRANSITIONS.get(current_status, [])
    if new_status not in allowed:
        errors.append(
            f"Invalid state transition: '{current_status}' -> '{new_status}'. "
            f"Allowed transitions from '{current_status}': {', '.join(allowed) if allowed else 'none'}"
        )
    return errors


def _check_required_fields(record: dict, required: list[str], prefix: str = "") -> list[str]:
    """Check that all required fields are present in a dict."""
    errors: list[str] = []
    for field in required:
        if field not in record:
            path = f"{prefix}.{field}" if prefix else field
            errors.append(f"Missing required field: '{path}'")
    return errors


def _check_enum(value, valid_values: tuple, field_name: str) -> list[str]:
    """Check that a value is one of the valid enum values."""
    if value not in valid_values:
        return [f"Field '{field_name}' has invalid value '{value}'. Must be one of: {', '.join(str(v) for v in valid_values)}"]
    return []


def _check_string(value, field_name: str, min_length: int = 0, max_length: int | None = None) -> list[str]:
    """Check that a value is a string with optional length constraints."""
    errors: list[str] = []
    if not isinstance(value, str):
        errors.append(f"Field '{field_name}' must be a string, got {type(value).__name__}")
        return errors
    if len(value) < min_length:
        errors.append(f"Field '{field_name}' must be at least {min_length} characters, got {len(value)}")
    if max_length is not None and len(value) > max_length:
        errors.append(f"Field '{field_name}' must be at most {max_length} characters, got {len(value)}")
    return errors


def _check_iso_datetime(value, field_name: str) -> list[str]:
    """Check that a value is a valid ISO 8601 datetime string."""
    if value is None:
        return []
    if not isinstance(value, str):
        return [f"Field '{field_name}' must be an ISO 8601 datetime string, got {type(value).__name__}"]
    try:
        datetime.fromisoformat(value)
    except ValueError:
        return [f"Field '{field_name}' is not a valid ISO 8601 datetime: '{value}'"]
    return []


def _check_array(value, field_name: str) -> list[str]:
    """Check that a value is a list."""
    if not isinstance(value, list):
        return [f"Field '{field_name}' must be an array, got {type(value).__name__}"]
    return []


def validate_tc_record(record: dict) -> list[str]:
    """Full validation of a TC record against the schema.

    Returns empty list if valid, list of error strings otherwise.
    """
    errors: list[str] = []

    if not isinstance(record, dict):
        return [f"TC record must be a JSON object, got {type(record).__name__}"]

    # --- Top-level required fields ---
    top_required = [
        "tc_id", "title", "status", "priority", "created", "updated",
        "created_by", "project", "description", "files_affected",
        "revision_history", "test_cases", "approval", "session_context",
        "tags", "related_tcs", "notes", "metadata"
    ]
    errors.extend(_check_required_fields(record, top_required))

    # If critical fields are missing, we can't validate further
    if any(f"Missing required field: '{f}'" in e for e in errors for f in ["tc_id", "status"]):
        return errors

    # --- tc_id ---
    if "tc_id" in record:
        errors.extend(validate_tc_id(record["tc_id"]))

    # --- title ---
    if "title" in record:
        errors.extend(_check_string(record["title"], "title", min_length=5, max_length=120))

    # --- status ---
    if "status" in record:
        errors.extend(_check_enum(record["status"], VALID_STATUSES, "status"))

    # --- priority ---
    if "priority" in record:
        errors.extend(_check_enum(record["priority"], VALID_PRIORITIES, "priority"))

    # --- timestamps ---
    for ts_field in ("created", "updated"):
        if ts_field in record:
            errors.extend(_check_iso_datetime(record[ts_field], ts_field))

    # --- created_by ---
    if "created_by" in record:
        errors.extend(_check_string(record["created_by"], "created_by", min_length=1))

    # --- project ---
    if "project" in record:
        errors.extend(_check_string(record["project"], "project", min_length=1))

    # --- description ---
    if "description" in record:
        desc = record["description"]
        if not isinstance(desc, dict):
            errors.append("Field 'description' must be an object")
        else:
            errors.extend(_check_required_fields(desc, ["summary", "motivation", "scope"], "description"))
            if "summary" in desc:
                errors.extend(_check_string(desc["summary"], "description.summary", min_length=10))
            if "motivation" in desc:
                errors.extend(_check_string(desc["motivation"], "description.motivation", min_length=1))
            if "scope" in desc:
                errors.extend(_check_enum(desc["scope"], VALID_SCOPES, "description.scope"))
            if "breaking_changes" in desc:
                errors.extend(_check_array(desc["breaking_changes"], "description.breaking_changes"))
            if "dependencies" in desc:
                errors.extend(_check_array(desc["dependencies"], "description.dependencies"))

    # --- files_affected ---
    if "files_affected" in record:
        files = record["files_affected"]
        errors.extend(_check_array(files, "files_affected"))
        if isinstance(files, list):
            for i, f in enumerate(files):
                prefix = f"files_affected[{i}]"
                if not isinstance(f, dict):
                    errors.append(f"{prefix} must be an object")
                    continue
                errors.extend(_check_required_fields(f, ["path", "action"], prefix))
                if "path" in f:
                    errors.extend(_check_string(f["path"], f"{prefix}.path", min_length=1))
                if "action" in f:
                    errors.extend(_check_enum(f["action"], VALID_FILE_ACTIONS, f"{prefix}.action"))

    # --- revision_history ---
    if "revision_history" in record:
        revs = record["revision_history"]
        errors.extend(_check_array(revs, "revision_history"))
        if isinstance(revs, list):
            if len(revs) < 1:
                errors.append("revision_history must have at least 1 entry (the creation event)")
            for i, rev in enumerate(revs):
                prefix = f"revision_history[{i}]"
                if not isinstance(rev, dict):
                    errors.append(f"{prefix} must be an object")
                    continue
                errors.extend(_check_required_fields(rev, ["revision_id", "timestamp", "author", "summary"], prefix))

                # Check sequential IDs
                if "revision_id" in rev:
                    rid = rev["revision_id"]
                    match = REVISION_ID_PATTERN.match(rid) if isinstance(rid, str) else None
                    if not match:
                        errors.append(f"{prefix}.revision_id '{rid}' must match pattern R1, R2, R3...")
                    elif int(match.group(1)) != i + 1:
                        errors.append(
                            f"{prefix}.revision_id is '{rid}' but expected 'R{i + 1}' "
                            f"(revision IDs must be sequential)"
                        )

                if "timestamp" in rev:
                    errors.extend(_check_iso_datetime(rev["timestamp"], f"{prefix}.timestamp"))

                # Validate field_changes if present
                if "field_changes" in rev and isinstance(rev["field_changes"], list):
                    for j, fc in enumerate(rev["field_changes"]):
                        fc_prefix = f"{prefix}.field_changes[{j}]"
                        if not isinstance(fc, dict):
                            errors.append(f"{fc_prefix} must be an object")
                            continue
                        errors.extend(_check_required_fields(fc, ["field", "action"], fc_prefix))
                        if "action" in fc:
                            errors.extend(_check_enum(fc["action"], VALID_FIELD_CHANGE_ACTIONS, f"{fc_prefix}.action"))

    # --- sub_tcs ---
    if "sub_tcs" in record:
        subs = record["sub_tcs"]
        if isinstance(subs, list):
            for i, sub in enumerate(subs):
                prefix = f"sub_tcs[{i}]"
                if not isinstance(sub, dict):
                    errors.append(f"{prefix} must be an object")
                    continue
                errors.extend(_check_required_fields(sub, ["sub_id", "title", "status"], prefix))
                if "sub_id" in sub:
                    errors.extend(validate_sub_tc_id(sub["sub_id"]))
                if "status" in sub:
                    errors.extend(_check_enum(sub["status"], VALID_STATUSES, f"{prefix}.status"))

    # --- test_cases ---
    if "test_cases" in record:
        tests = record["test_cases"]
        errors.extend(_check_array(tests, "test_cases"))
        if isinstance(tests, list):
            for i, tc in enumerate(tests):
                prefix = f"test_cases[{i}]"
                if not isinstance(tc, dict):
                    errors.append(f"{prefix} must be an object")
                    continue
                errors.extend(_check_required_fields(tc, ["test_id", "title", "procedure", "expected_result", "status"], prefix))

                # Check sequential test IDs
                if "test_id" in tc:
                    tid = tc["test_id"]
                    match = TEST_ID_PATTERN.match(tid) if isinstance(tid, str) else None
                    if not match:
                        errors.append(f"{prefix}.test_id '{tid}' must match pattern T1, T2, T3...")
                    elif int(match.group(1)) != i + 1:
                        errors.append(
                            f"{prefix}.test_id is '{tid}' but expected 'T{i + 1}' "
                            f"(test IDs must be sequential)"
                        )

                if "status" in tc:
                    errors.extend(_check_enum(tc["status"], VALID_TEST_STATUSES, f"{prefix}.status"))

                if "procedure" in tc:
                    proc = tc["procedure"]
                    errors.extend(_check_array(proc, f"{prefix}.procedure"))
                    if isinstance(proc, list) and len(proc) < 1:
                        errors.append(f"{prefix}.procedure must have at least 1 step")

                # Validate evidence
                if "evidence" in tc and isinstance(tc["evidence"], list):
                    for j, ev in enumerate(tc["evidence"]):
                        ev_prefix = f"{prefix}.evidence[{j}]"
                        if not isinstance(ev, dict):
                            errors.append(f"{ev_prefix} must be an object")
                            continue
                        errors.extend(_check_required_fields(ev, ["type", "description"], ev_prefix))
                        if "type" in ev:
                            errors.extend(_check_enum(ev["type"], VALID_EVIDENCE_TYPES, f"{ev_prefix}.type"))

    # --- approval ---
    if "approval" in record:
        appr = record["approval"]
        if not isinstance(appr, dict):
            errors.append("Field 'approval' must be an object")
        else:
            errors.extend(_check_required_fields(appr, ["approved", "test_coverage_status"], "approval"))
            if "approved" in appr and appr["approved"] is True:
                if not appr.get("approved_by"):
                    errors.append("approval.approved_by is required when approval.approved is true")
                if not appr.get("approved_date"):
                    errors.append("approval.approved_date is required when approval.approved is true")
            if "test_coverage_status" in appr:
                errors.extend(_check_enum(appr["test_coverage_status"], VALID_COVERAGE, "approval.test_coverage_status"))

    # --- session_context ---
    if "session_context" in record:
        ctx = record["session_context"]
        if not isinstance(ctx, dict):
            errors.append("Field 'session_context' must be an object")
        else:
            errors.extend(_check_required_fields(ctx, ["current_session"], "session_context"))
            if "current_session" in ctx:
                cs = ctx["current_session"]
                if not isinstance(cs, dict):
                    errors.append("session_context.current_session must be an object")
                else:
                    errors.extend(_check_required_fields(
                        cs, ["session_id", "platform", "model", "started"],
                        "session_context.current_session"
                    ))
                    if "platform" in cs:
                        errors.extend(_check_enum(cs["platform"], VALID_PLATFORMS, "session_context.current_session.platform"))
                    if "started" in cs:
                        errors.extend(_check_iso_datetime(cs["started"], "session_context.current_session.started"))

            # Validate handoff
            if "handoff" in ctx and isinstance(ctx["handoff"], dict):
                handoff = ctx["handoff"]
                if "files_in_progress" in handoff and isinstance(handoff["files_in_progress"], list):
                    for i, fip in enumerate(handoff["files_in_progress"]):
                        fip_prefix = f"session_context.handoff.files_in_progress[{i}]"
                        if isinstance(fip, dict):
                            errors.extend(_check_required_fields(fip, ["path", "state"], fip_prefix))
                            if "state" in fip:
                                errors.extend(_check_enum(fip["state"], VALID_FILE_IN_PROGRESS_STATES, f"{fip_prefix}.state"))

    # --- metadata ---
    if "metadata" in record:
        meta = record["metadata"]
        if not isinstance(meta, dict):
            errors.append("Field 'metadata' must be an object")
        else:
            errors.extend(_check_required_fields(
                meta, ["project", "created_by", "last_modified_by", "last_modified"],
                "metadata"
            ))
            if "last_modified" in meta:
                errors.extend(_check_iso_datetime(meta["last_modified"], "metadata.last_modified"))
            if "estimated_effort" in meta:
                errors.extend(_check_enum(meta["estimated_effort"], VALID_EFFORTS, "metadata.estimated_effort"))

    return errors


def validate_registry(registry: dict) -> list[str]:
    """Validate a TC registry against its schema."""
    errors: list[str] = []

    if not isinstance(registry, dict):
        return [f"TC registry must be a JSON object, got {type(registry).__name__}"]

    required = ["project_name", "created", "updated", "next_tc_number", "records", "statistics"]
    errors.extend(_check_required_fields(registry, required))

    if "project_name" in registry:
        errors.extend(_check_string(registry["project_name"], "project_name", min_length=1))

    for ts_field in ("created", "updated"):
        if ts_field in registry:
            errors.extend(_check_iso_datetime(registry[ts_field], ts_field))

    if "next_tc_number" in registry:
        val = registry["next_tc_number"]
        if not isinstance(val, int) or val < 1:
            errors.append(f"next_tc_number must be a positive integer, got {val}")

    if "records" in registry:
        records = registry["records"]
        errors.extend(_check_array(records, "records"))
        if isinstance(records, list):
            for i, rec in enumerate(records):
                prefix = f"records[{i}]"
                if not isinstance(rec, dict):
                    errors.append(f"{prefix} must be an object")
                    continue
                errors.extend(_check_required_fields(
                    rec, ["tc_id", "title", "status", "scope", "priority", "created", "updated", "path"],
                    prefix
                ))
                if "status" in rec:
                    errors.extend(_check_enum(rec["status"], VALID_STATUSES, f"{prefix}.status"))
                if "scope" in rec:
                    errors.extend(_check_enum(rec["scope"], VALID_SCOPES, f"{prefix}.scope"))
                if "priority" in rec:
                    errors.extend(_check_enum(rec["priority"], VALID_PRIORITIES, f"{prefix}.priority"))

    if "statistics" in registry:
        stats = registry["statistics"]
        if not isinstance(stats, dict):
            errors.append("statistics must be an object")
        else:
            errors.extend(_check_required_fields(stats, ["total", "by_status", "by_scope", "by_priority"], "statistics"))

    return errors


# ---------------------------------------------------------------------------
# Utility Functions
# ---------------------------------------------------------------------------

def generate_next_tc_id(registry: dict, date_str: str, name_slug: str) -> str:
    """Generate the next TC ID from the registry.

    Args:
        registry: The tc_registry.json data
        date_str: Date in MM-DD-YY format
        name_slug: Kebab-case functionality name (e.g., 'user-authentication')

    Returns:
        TC ID string (e.g., 'TC-001-04-03-26-user-authentication')
    """
    num = registry.get("next_tc_number", 1)
    return f"TC-{num:03d}-{date_str}-{name_slug}"


def compute_registry_statistics(records: list[dict]) -> dict:
    """Recompute registry statistics from the records array.

    Call this every time the registry is modified.
    """
    stats = {
        "total": len(records),
        "by_status": {s: 0 for s in VALID_STATUSES},
        "by_scope": {s: 0 for s in VALID_SCOPES},
        "by_priority": {p: 0 for p in VALID_PRIORITIES},
    }
    for rec in records:
        status = rec.get("status", "")
        if status in stats["by_status"]:
            stats["by_status"][status] += 1
        scope = rec.get("scope", "")
        if scope in stats["by_scope"]:
            stats["by_scope"][scope] += 1
        priority = rec.get("priority", "")
        if priority in stats["by_priority"]:
            stats["by_priority"][priority] += 1
    return stats


def slugify(text: str) -> str:
    """Convert text to a URL/filename-safe kebab-case slug."""
    text = text.lower().strip()
    text = re.sub(r"[^a-z0-9\s-]", "", text)
    text = re.sub(r"[\s_]+", "-", text)
    text = re.sub(r"-+", "-", text)
    return text.strip("-")


# ---------------------------------------------------------------------------
# CLI Entry Point
# ---------------------------------------------------------------------------

def main() -> int:
    """CLI entry point. Validates a TC record or registry JSON file."""
    if len(sys.argv) < 2:
        print("Usage:")
        print("  python validate_tc.py <path_to_tc_record.json>")
        print("  python validate_tc.py --registry <path_to_tc_registry.json>")
        return 2

    is_registry = sys.argv[1] == "--registry"
    file_path = sys.argv[2] if is_registry else sys.argv[1]

    path = Path(file_path)
    if not path.exists():
        print(f"ERROR: File not found: {path}")
        return 2

    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
    except json.JSONDecodeError as e:
        print(f"ERROR: Invalid JSON in {path}: {e}")
        return 2

    if is_registry:
        errors = validate_registry(data)
    else:
        errors = validate_tc_record(data)

    if errors:
        print(f"VALIDATION ERRORS ({len(errors)}):")
        for i, err in enumerate(errors, 1):
            print(f"  {i}. {err}")
        return 1

    print("VALID")
    return 0


if __name__ == "__main__":
    sys.exit(main())
