#!/usr/bin/env python3
"""TC Update — Update an existing TC record.

Each invocation appends a sequential R<n> revision entry, refreshes the
`updated` timestamp, validates the resulting record, and writes atomically.

Usage:
    # Status transition (validated against state machine)
    python3 tc_update.py --root . --tc-id <TC-ID> \\
        --set-status in_progress --reason "Starting implementation"

    # Add files
    python3 tc_update.py --root . --tc-id <TC-ID> \\
        --add-file src/auth.py:created \\
        --add-file src/middleware.py:modified

    # Add a test case
    python3 tc_update.py --root . --tc-id <TC-ID> \\
        --add-test "Login returns JWT" \\
        --test-procedure "POST /login with valid creds" \\
        --test-expected "200 + token in body"

    # Append handoff data
    python3 tc_update.py --root . --tc-id <TC-ID> \\
        --handoff-progress "JWT middleware wired up" \\
        --handoff-next "Write integration tests" \\
        --handoff-next "Update README" \\
        --handoff-blocker "Waiting on test fixtures"

    # Append a freeform note
    python3 tc_update.py --root . --tc-id <TC-ID> --note "Decision: use HS256"

Exit codes:
    0 = updated
    1 = warnings (e.g. validation produced errors but write skipped)
    2 = critical error (file missing, invalid transition, parse error)
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from datetime import datetime, timezone
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
VALID_FILE_ACTIONS = ("created", "modified", "deleted", "renamed")
VALID_TEST_STATUSES = ("pending", "pass", "fail", "skip", "blocked")
VALID_SCOPES = ("feature", "bugfix", "refactor", "infrastructure", "documentation", "hotfix", "enhancement")
VALID_PRIORITIES = ("critical", "high", "medium", "low")


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def write_json_atomic(path: Path, data: dict) -> None:
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    tmp.replace(path)


def find_record_path(tc_dir: Path, tc_id: str) -> Path | None:
    direct = tc_dir / "records" / tc_id / "tc_record.json"
    if direct.exists():
        return direct
    for entry in (tc_dir / "records").glob("*"):
        if entry.is_dir() and entry.name.startswith(tc_id):
            candidate = entry / "tc_record.json"
            if candidate.exists():
                return candidate
    return None


def validate_transition(current: str, new: str) -> str | None:
    if current == new:
        return None
    allowed = VALID_TRANSITIONS.get(current, [])
    if new not in allowed:
        return f"Invalid transition '{current}' -> '{new}'. Allowed: {', '.join(allowed) or 'none'}"
    return None


def next_revision_id(record: dict) -> str:
    return f"R{len(record.get('revision_history', [])) + 1}"


def next_test_id(record: dict) -> str:
    return f"T{len(record.get('test_cases', [])) + 1}"


def compute_stats(records: list) -> dict:
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


def parse_file_arg(spec: str) -> tuple[str, str]:
    """Parse 'path:action' or just 'path' (default action: modified)."""
    if ":" in spec:
        path, action = spec.rsplit(":", 1)
        action = action.strip()
        if action not in VALID_FILE_ACTIONS:
            raise ValueError(f"Invalid file action '{action}'. Must be one of {VALID_FILE_ACTIONS}")
        return path.strip(), action
    return spec.strip(), "modified"


def main() -> int:
    parser = argparse.ArgumentParser(description="Update an existing TC record.")
    parser.add_argument("--root", default=".", help="Project root (default: current directory)")
    parser.add_argument("--tc-id", required=True, help="Target TC ID (full or prefix)")
    parser.add_argument("--author", default=None, help="Author for this revision (defaults to config)")
    parser.add_argument("--reason", default="", help="Reason for the change (recorded in revision)")

    parser.add_argument("--set-status", choices=VALID_STATUSES, help="Transition status (state machine enforced)")
    parser.add_argument("--add-file", action="append", default=[], metavar="path[:action]",
                        help="Add a file. Action defaults to 'modified'. Repeatable.")
    parser.add_argument("--add-test", help="Add a test case with this title")
    parser.add_argument("--test-procedure", action="append", default=[],
                        help="Procedure step for the test being added. Repeatable.")
    parser.add_argument("--test-expected", help="Expected result for the test being added")

    parser.add_argument("--handoff-progress", help="Set progress_summary in handoff")
    parser.add_argument("--handoff-next", action="append", default=[], help="Append to next_steps. Repeatable.")
    parser.add_argument("--handoff-blocker", action="append", default=[], help="Append to blockers. Repeatable.")
    parser.add_argument("--handoff-context", action="append", default=[], help="Append to key_context. Repeatable.")

    parser.add_argument("--note", help="Append a freeform note (with timestamp)")
    parser.add_argument("--tag", action="append", default=[], help="Add a tag. Repeatable.")

    parser.add_argument("--json", action="store_true", help="Output as JSON")
    args = parser.parse_args()

    root = Path(args.root).resolve()
    tc_dir = root / "docs" / "TC"
    config_path = tc_dir / "tc_config.json"
    registry_path = tc_dir / "tc_registry.json"

    if not config_path.exists() or not registry_path.exists():
        msg = f"TC tracking not initialized at {tc_dir}. Run tc_init.py first."
        print(json.dumps({"status": "error", "error": msg}) if args.json else f"ERROR: {msg}")
        return 2

    record_path = find_record_path(tc_dir, args.tc_id)
    if record_path is None:
        msg = f"TC not found: {args.tc_id}"
        print(json.dumps({"status": "error", "error": msg}) if args.json else f"ERROR: {msg}")
        return 2

    try:
        config = json.loads(config_path.read_text(encoding="utf-8"))
        registry = json.loads(registry_path.read_text(encoding="utf-8"))
        record = json.loads(record_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as e:
        msg = f"Failed to read JSON: {e}"
        print(json.dumps({"status": "error", "error": msg}) if args.json else f"ERROR: {msg}")
        return 2

    author = args.author or config.get("default_author", "Claude")
    ts = now_iso()

    field_changes = []
    summary_parts = []

    if args.set_status:
        current = record.get("status")
        new = args.set_status
        err = validate_transition(current, new)
        if err:
            print(json.dumps({"status": "error", "error": err}) if args.json else f"ERROR: {err}")
            return 2
        if current != new:
            record["status"] = new
            field_changes.append({
                "field": "status", "action": "changed",
                "old_value": current, "new_value": new, "reason": args.reason or None,
            })
            summary_parts.append(f"status: {current} -> {new}")

    for spec in args.add_file:
        try:
            path, action = parse_file_arg(spec)
        except ValueError as e:
            print(json.dumps({"status": "error", "error": str(e)}) if args.json else f"ERROR: {e}")
            return 2
        record.setdefault("files_affected", []).append({
            "path": path, "action": action, "description": None,
            "lines_added": None, "lines_removed": None,
        })
        field_changes.append({
            "field": "files_affected", "action": "added",
            "new_value": {"path": path, "action": action},
            "reason": args.reason or None,
        })
        summary_parts.append(f"+file {path} ({action})")

    if args.add_test:
        if not args.test_procedure or not args.test_expected:
            msg = "--add-test requires at least one --test-procedure and --test-expected"
            print(json.dumps({"status": "error", "error": msg}) if args.json else f"ERROR: {msg}")
            return 2
        test_id = next_test_id(record)
        new_test = {
            "test_id": test_id,
            "title": args.add_test,
            "procedure": list(args.test_procedure),
            "expected_result": args.test_expected,
            "actual_result": None,
            "status": "pending",
            "evidence": [],
            "tested_by": None,
            "tested_date": None,
        }
        record.setdefault("test_cases", []).append(new_test)
        field_changes.append({
            "field": "test_cases", "action": "added",
            "new_value": test_id, "reason": args.reason or None,
        })
        summary_parts.append(f"+test {test_id}: {args.add_test}")

    handoff = record.setdefault("session_context", {}).setdefault("handoff", {
        "progress_summary": "", "next_steps": [], "blockers": [],
        "key_context": [], "files_in_progress": [], "decisions_made": [],
    })

    if args.handoff_progress is not None:
        old = handoff.get("progress_summary", "")
        handoff["progress_summary"] = args.handoff_progress
        field_changes.append({
            "field": "session_context.handoff.progress_summary",
            "action": "changed", "old_value": old, "new_value": args.handoff_progress,
            "reason": args.reason or None,
        })
        summary_parts.append("handoff: updated progress_summary")

    for step in args.handoff_next:
        handoff.setdefault("next_steps", []).append(step)
        field_changes.append({
            "field": "session_context.handoff.next_steps",
            "action": "added", "new_value": step, "reason": args.reason or None,
        })
        summary_parts.append(f"handoff: +next_step '{step}'")

    for blk in args.handoff_blocker:
        handoff.setdefault("blockers", []).append(blk)
        field_changes.append({
            "field": "session_context.handoff.blockers",
            "action": "added", "new_value": blk, "reason": args.reason or None,
        })
        summary_parts.append(f"handoff: +blocker '{blk}'")

    for ctx in args.handoff_context:
        handoff.setdefault("key_context", []).append(ctx)
        field_changes.append({
            "field": "session_context.handoff.key_context",
            "action": "added", "new_value": ctx, "reason": args.reason or None,
        })
        summary_parts.append(f"handoff: +context")

    if args.note:
        existing = record.get("notes", "") or ""
        addition = f"[{ts}] {args.note}"
        record["notes"] = (existing + "\n" + addition).strip() if existing else addition
        field_changes.append({
            "field": "notes", "action": "added",
            "new_value": args.note, "reason": args.reason or None,
        })
        summary_parts.append("note appended")

    for tag in args.tag:
        if tag not in record.setdefault("tags", []):
            record["tags"].append(tag)
            field_changes.append({
                "field": "tags", "action": "added",
                "new_value": tag, "reason": args.reason or None,
            })
            summary_parts.append(f"+tag {tag}")

    if not field_changes:
        msg = "No changes specified. Use --set-status, --add-file, --add-test, --handoff-*, --note, or --tag."
        print(json.dumps({"status": "noop", "message": msg}) if args.json else msg)
        return 0

    revision = {
        "revision_id": next_revision_id(record),
        "timestamp": ts,
        "author": author,
        "summary": "; ".join(summary_parts) if summary_parts else "TC updated",
        "field_changes": field_changes,
    }
    record.setdefault("revision_history", []).append(revision)

    record["updated"] = ts
    meta = record.setdefault("metadata", {})
    meta["last_modified"] = ts
    meta["last_modified_by"] = author

    cs = record.setdefault("session_context", {}).setdefault("current_session", {})
    cs["last_active"] = ts

    try:
        write_json_atomic(record_path, record)
    except OSError as e:
        msg = f"Failed to write record: {e}"
        print(json.dumps({"status": "error", "error": msg}) if args.json else f"ERROR: {msg}")
        return 2

    for entry in registry.get("records", []):
        if entry.get("tc_id") == record["tc_id"]:
            entry["status"] = record["status"]
            entry["updated"] = ts
            break
    registry["updated"] = ts
    registry["statistics"] = compute_stats(registry.get("records", []))

    try:
        write_json_atomic(registry_path, registry)
    except OSError as e:
        msg = f"Failed to update registry: {e}"
        print(json.dumps({"status": "error", "error": msg}) if args.json else f"ERROR: {msg}")
        return 2

    result = {
        "status": "updated",
        "tc_id": record["tc_id"],
        "revision": revision["revision_id"],
        "summary": revision["summary"],
        "current_status": record["status"],
    }
    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print(f"Updated {record['tc_id']} ({revision['revision_id']})")
        print(f"  {revision['summary']}")
        print(f"  Status: {record['status']}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
