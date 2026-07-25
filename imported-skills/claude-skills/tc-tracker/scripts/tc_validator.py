#!/usr/bin/env python3
"""TC Validator — Validate a TC record or registry against the schema and state machine.

Enforces:
  * Schema shape (required fields, types, enum values)
  * State machine transitions (planned -> in_progress -> implemented -> tested -> deployed)
  * Sequential R<n> revision IDs and T<n> test IDs
  * TC ID format (TC-NNN-MM-DD-YY-slug)
  * Sub-TC ID format (TC-NNN.A or TC-NNN.A.N)
  * Approval consistency (approved=true requires approved_by + approved_date)

Usage:
    python3 tc_validator.py --record path/to/tc_record.json
    python3 tc_validator.py --registry path/to/tc_registry.json
    python3 tc_validator.py --record path/to/tc_record.json --json

Exit codes:
    0 = valid
    1 = validation errors
    2 = file not found / JSON parse error / bad CLI args
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from datetime import datetime
from pathlib import Path

VALID_STATUSES = ("planned", "in_progress", "blocked", "implemented", "tested", "deployed")

VALID_TRANSITIONS = {
    "planned":     ["in_progress", "blocked"],
    "in_progress": ["blocked", "implemented"],
    "blocked":     ["in_progress", "planned"],
    "implemented": ["tested", "in_progress"],
    "tested":      ["deployed", "in_progress"],
    "deployed":    ["in_progress"],
}

VALID_SCOPES = ("feature", "bugfix", "refactor", "infrastructure", "documentation", "hotfix", "enhancement")
VALID_PRIORITIES = ("critical", "high", "medium", "low")
VALID_FILE_ACTIONS = ("created", "modified", "deleted", "renamed")
VALID_TEST_STATUSES = ("pending", "pass", "fail", "skip", "blocked")
VALID_EVIDENCE_TYPES = ("log_snippet", "screenshot", "file_reference", "command_output")
VALID_FIELD_CHANGE_ACTIONS = ("set", "changed", "added", "removed")
VALID_PLATFORMS = ("claude_code", "claude_web", "api", "other")
VALID_COVERAGE = ("none", "partial", "full")
VALID_FILE_IN_PROGRESS_STATES = ("editing", "needs_review", "partially_done", "ready")

TC_ID_PATTERN = re.compile(r"^TC-\d{3}-\d{2}-\d{2}-\d{2}-[a-z0-9]+(-[a-z0-9]+)*$")
SUB_TC_PATTERN = re.compile(r"^TC-\d{3}\.[A-Z](\.\d+)?$")
REVISION_ID_PATTERN = re.compile(r"^R(\d+)$")
TEST_ID_PATTERN = re.compile(r"^T(\d+)$")


def _enum(value, valid, name):
    if value not in valid:
        return [f"Field '{name}' has invalid value '{value}'. Must be one of: {', '.join(str(v) for v in valid)}"]
    return []


def _string(value, name, min_length=0, max_length=None):
    errors = []
    if not isinstance(value, str):
        return [f"Field '{name}' must be a string, got {type(value).__name__}"]
    if len(value) < min_length:
        errors.append(f"Field '{name}' must be at least {min_length} characters, got {len(value)}")
    if max_length is not None and len(value) > max_length:
        errors.append(f"Field '{name}' must be at most {max_length} characters, got {len(value)}")
    return errors


def _iso(value, name):
    if value is None:
        return []
    if not isinstance(value, str):
        return [f"Field '{name}' must be an ISO 8601 datetime string"]
    try:
        datetime.fromisoformat(value)
    except ValueError:
        return [f"Field '{name}' is not a valid ISO 8601 datetime: '{value}'"]
    return []


def _required(record, fields, prefix=""):
    errors = []
    for f in fields:
        if f not in record:
            path = f"{prefix}.{f}" if prefix else f
            errors.append(f"Missing required field: '{path}'")
    return errors


def validate_tc_id(tc_id):
    """Validate a TC identifier."""
    if not isinstance(tc_id, str):
        return [f"tc_id must be a string, got {type(tc_id).__name__}"]
    if not TC_ID_PATTERN.match(tc_id):
        return [f"tc_id '{tc_id}' does not match pattern TC-NNN-MM-DD-YY-slug"]
    return []


def validate_state_transition(current, new):
    """Validate a state machine transition. Same-status is a no-op."""
    errors = []
    if current not in VALID_STATUSES:
        errors.append(f"Current status '{current}' is invalid")
    if new not in VALID_STATUSES:
        errors.append(f"New status '{new}' is invalid")
    if errors:
        return errors
    if current == new:
        return []
    allowed = VALID_TRANSITIONS.get(current, [])
    if new not in allowed:
        return [f"Invalid transition '{current}' -> '{new}'. Allowed from '{current}': {', '.join(allowed) or 'none'}"]
    return []


def validate_tc_record(record):
    """Validate a TC record dict against the schema."""
    errors = []
    if not isinstance(record, dict):
        return [f"TC record must be a JSON object, got {type(record).__name__}"]

    top_required = [
        "tc_id", "title", "status", "priority", "created", "updated",
        "created_by", "project", "description", "files_affected",
        "revision_history", "test_cases", "approval", "session_context",
        "tags", "related_tcs", "notes", "metadata",
    ]
    errors.extend(_required(record, top_required))

    if "tc_id" in record:
        errors.extend(validate_tc_id(record["tc_id"]))
    if "title" in record:
        errors.extend(_string(record["title"], "title", 5, 120))
    if "status" in record:
        errors.extend(_enum(record["status"], VALID_STATUSES, "status"))
    if "priority" in record:
        errors.extend(_enum(record["priority"], VALID_PRIORITIES, "priority"))
    for ts in ("created", "updated"):
        if ts in record:
            errors.extend(_iso(record[ts], ts))
    if "created_by" in record:
        errors.extend(_string(record["created_by"], "created_by", 1))
    if "project" in record:
        errors.extend(_string(record["project"], "project", 1))

    desc = record.get("description")
    if isinstance(desc, dict):
        errors.extend(_required(desc, ["summary", "motivation", "scope"], "description"))
        if "summary" in desc:
            errors.extend(_string(desc["summary"], "description.summary", 10))
        if "motivation" in desc:
            errors.extend(_string(desc["motivation"], "description.motivation", 1))
        if "scope" in desc:
            errors.extend(_enum(desc["scope"], VALID_SCOPES, "description.scope"))
    elif "description" in record:
        errors.append("Field 'description' must be an object")

    files = record.get("files_affected")
    if isinstance(files, list):
        for i, f in enumerate(files):
            prefix = f"files_affected[{i}]"
            if not isinstance(f, dict):
                errors.append(f"{prefix} must be an object")
                continue
            errors.extend(_required(f, ["path", "action"], prefix))
            if "action" in f:
                errors.extend(_enum(f["action"], VALID_FILE_ACTIONS, f"{prefix}.action"))
    elif "files_affected" in record:
        errors.append("Field 'files_affected' must be an array")

    revs = record.get("revision_history")
    if isinstance(revs, list):
        if len(revs) < 1:
            errors.append("revision_history must have at least 1 entry")
        for i, rev in enumerate(revs):
            prefix = f"revision_history[{i}]"
            if not isinstance(rev, dict):
                errors.append(f"{prefix} must be an object")
                continue
            errors.extend(_required(rev, ["revision_id", "timestamp", "author", "summary"], prefix))
            rid = rev.get("revision_id")
            if isinstance(rid, str):
                m = REVISION_ID_PATTERN.match(rid)
                if not m:
                    errors.append(f"{prefix}.revision_id '{rid}' must match R<n>")
                elif int(m.group(1)) != i + 1:
                    errors.append(f"{prefix}.revision_id is '{rid}' but expected 'R{i + 1}' (must be sequential)")
            if "timestamp" in rev:
                errors.extend(_iso(rev["timestamp"], f"{prefix}.timestamp"))
    elif "revision_history" in record:
        errors.append("Field 'revision_history' must be an array")

    tests = record.get("test_cases")
    if isinstance(tests, list):
        for i, tc in enumerate(tests):
            prefix = f"test_cases[{i}]"
            if not isinstance(tc, dict):
                errors.append(f"{prefix} must be an object")
                continue
            errors.extend(_required(tc, ["test_id", "title", "procedure", "expected_result", "status"], prefix))
            tid = tc.get("test_id")
            if isinstance(tid, str):
                m = TEST_ID_PATTERN.match(tid)
                if not m:
                    errors.append(f"{prefix}.test_id '{tid}' must match T<n>")
                elif int(m.group(1)) != i + 1:
                    errors.append(f"{prefix}.test_id is '{tid}' but expected 'T{i + 1}' (must be sequential)")
            if "status" in tc:
                errors.extend(_enum(tc["status"], VALID_TEST_STATUSES, f"{prefix}.status"))

    appr = record.get("approval")
    if isinstance(appr, dict):
        errors.extend(_required(appr, ["approved", "test_coverage_status"], "approval"))
        if appr.get("approved") is True:
            if not appr.get("approved_by"):
                errors.append("approval.approved_by is required when approval.approved is true")
            if not appr.get("approved_date"):
                errors.append("approval.approved_date is required when approval.approved is true")
        if "test_coverage_status" in appr:
            errors.extend(_enum(appr["test_coverage_status"], VALID_COVERAGE, "approval.test_coverage_status"))
    elif "approval" in record:
        errors.append("Field 'approval' must be an object")

    ctx = record.get("session_context")
    if isinstance(ctx, dict):
        errors.extend(_required(ctx, ["current_session"], "session_context"))
        cs = ctx.get("current_session")
        if isinstance(cs, dict):
            errors.extend(_required(cs, ["session_id", "platform", "model", "started"], "session_context.current_session"))
            if "platform" in cs:
                errors.extend(_enum(cs["platform"], VALID_PLATFORMS, "session_context.current_session.platform"))
            if "started" in cs:
                errors.extend(_iso(cs["started"], "session_context.current_session.started"))

    meta = record.get("metadata")
    if isinstance(meta, dict):
        errors.extend(_required(meta, ["project", "created_by", "last_modified_by", "last_modified"], "metadata"))
        if "last_modified" in meta:
            errors.extend(_iso(meta["last_modified"], "metadata.last_modified"))

    return errors


def validate_registry(registry):
    """Validate a TC registry dict."""
    errors = []
    if not isinstance(registry, dict):
        return [f"Registry must be an object, got {type(registry).__name__}"]
    errors.extend(_required(registry, ["project_name", "created", "updated", "next_tc_number", "records", "statistics"]))
    if "next_tc_number" in registry:
        v = registry["next_tc_number"]
        if not isinstance(v, int) or v < 1:
            errors.append(f"next_tc_number must be a positive integer, got {v}")
    if isinstance(registry.get("records"), list):
        for i, rec in enumerate(registry["records"]):
            prefix = f"records[{i}]"
            if not isinstance(rec, dict):
                errors.append(f"{prefix} must be an object")
                continue
            errors.extend(_required(rec, ["tc_id", "title", "status", "scope", "priority", "created", "updated", "path"], prefix))
            if "status" in rec:
                errors.extend(_enum(rec["status"], VALID_STATUSES, f"{prefix}.status"))
            if "scope" in rec:
                errors.extend(_enum(rec["scope"], VALID_SCOPES, f"{prefix}.scope"))
            if "priority" in rec:
                errors.extend(_enum(rec["priority"], VALID_PRIORITIES, f"{prefix}.priority"))
    return errors


def slugify(text):
    """Convert text to a kebab-case slug."""
    text = text.lower().strip()
    text = re.sub(r"[^a-z0-9\s-]", "", text)
    text = re.sub(r"[\s_]+", "-", text)
    text = re.sub(r"-+", "-", text)
    return text.strip("-")


def compute_registry_statistics(records):
    """Recompute registry statistics from the records array."""
    stats = {
        "total": len(records),
        "by_status": {s: 0 for s in VALID_STATUSES},
        "by_scope": {s: 0 for s in VALID_SCOPES},
        "by_priority": {p: 0 for p in VALID_PRIORITIES},
    }
    for rec in records:
        for key, bucket in (("status", "by_status"), ("scope", "by_scope"), ("priority", "by_priority")):
            v = rec.get(key, "")
            if v in stats[bucket]:
                stats[bucket][v] += 1
    return stats


def main():
    parser = argparse.ArgumentParser(description="Validate a TC record or registry.")
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--record", help="Path to tc_record.json")
    group.add_argument("--registry", help="Path to tc_registry.json")
    parser.add_argument("--json", action="store_true", help="Output results as JSON")
    args = parser.parse_args()

    target = args.record or args.registry
    path = Path(target)
    if not path.exists():
        msg = f"File not found: {path}"
        print(json.dumps({"status": "error", "error": msg}) if args.json else f"ERROR: {msg}")
        return 2

    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as e:
        msg = f"Invalid JSON in {path}: {e}"
        print(json.dumps({"status": "error", "error": msg}) if args.json else f"ERROR: {msg}")
        return 2

    errors = validate_registry(data) if args.registry else validate_tc_record(data)

    if args.json:
        result = {
            "status": "valid" if not errors else "invalid",
            "file": str(path),
            "kind": "registry" if args.registry else "record",
            "error_count": len(errors),
            "errors": errors,
        }
        print(json.dumps(result, indent=2))
    else:
        if errors:
            print(f"VALIDATION ERRORS ({len(errors)}):")
            for i, err in enumerate(errors, 1):
                print(f"  {i}. {err}")
        else:
            print("VALID")

    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
