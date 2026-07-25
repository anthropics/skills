#!/usr/bin/env python3
"""TC Create — Create a new Technical Change record.

Generates the next sequential TC ID, scaffolds the record directory, writes a
fully populated tc_record.json (status=planned, R1 creation revision), and
appends a registry entry with recomputed statistics.

Usage:
    python3 tc_create.py --root . --name user-auth \\
        --title "Add JWT authentication" --scope feature --priority high \\
        --summary "Adds JWT login + middleware" \\
        --motivation "Required for protected endpoints"

Exit codes:
    0 = created
    1 = warnings (e.g. validation soft warnings)
    2 = critical error (registry missing, bad args, schema invalid)
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from datetime import datetime, timezone
from pathlib import Path

VALID_STATUSES = ("planned", "in_progress", "blocked", "implemented", "tested", "deployed")
VALID_SCOPES = ("feature", "bugfix", "refactor", "infrastructure", "documentation", "hotfix", "enhancement")
VALID_PRIORITIES = ("critical", "high", "medium", "low")


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def slugify(text: str) -> str:
    text = text.lower().strip()
    text = re.sub(r"[^a-z0-9\s-]", "", text)
    text = re.sub(r"[\s_]+", "-", text)
    text = re.sub(r"-+", "-", text)
    return text.strip("-")


def date_slug(dt: datetime) -> str:
    return dt.strftime("%m-%d-%y")


def write_json_atomic(path: Path, data: dict) -> None:
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    tmp.replace(path)


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


def build_record(tc_id: str, title: str, scope: str, priority: str, summary: str,
                 motivation: str, project_name: str, author: str, session_id: str,
                 platform: str, model: str) -> dict:
    ts = now_iso()
    return {
        "tc_id": tc_id,
        "parent_tc": None,
        "title": title,
        "status": "planned",
        "priority": priority,
        "created": ts,
        "updated": ts,
        "created_by": author,
        "project": project_name,
        "description": {
            "summary": summary,
            "motivation": motivation,
            "scope": scope,
            "detailed_design": None,
            "breaking_changes": [],
            "dependencies": [],
        },
        "files_affected": [],
        "revision_history": [
            {
                "revision_id": "R1",
                "timestamp": ts,
                "author": author,
                "summary": "TC record created",
                "field_changes": [
                    {"field": "status", "action": "set", "new_value": "planned", "reason": "initial creation"},
                ],
            }
        ],
        "sub_tcs": [],
        "test_cases": [],
        "approval": {
            "approved": False,
            "approved_by": None,
            "approved_date": None,
            "approval_notes": "",
            "test_coverage_status": "none",
        },
        "session_context": {
            "current_session": {
                "session_id": session_id,
                "platform": platform,
                "model": model,
                "started": ts,
                "last_active": ts,
            },
            "handoff": {
                "progress_summary": "",
                "next_steps": [],
                "blockers": [],
                "key_context": [],
                "files_in_progress": [],
                "decisions_made": [],
            },
            "session_history": [],
        },
        "tags": [],
        "related_tcs": [],
        "notes": "",
        "metadata": {
            "project": project_name,
            "created_by": author,
            "last_modified_by": author,
            "last_modified": ts,
            "estimated_effort": None,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Create a new TC record.")
    parser.add_argument("--root", default=".", help="Project root (default: current directory)")
    parser.add_argument("--name", required=True, help="Functionality slug (kebab-case, e.g. user-auth)")
    parser.add_argument("--title", required=True, help="Human-readable title (5-120 chars)")
    parser.add_argument("--scope", required=True, choices=VALID_SCOPES, help="Change category")
    parser.add_argument("--priority", default="medium", choices=VALID_PRIORITIES, help="Priority level")
    parser.add_argument("--summary", required=True, help="Concise summary (10+ chars)")
    parser.add_argument("--motivation", required=True, help="Why this change is needed")
    parser.add_argument("--author", default=None, help="Author identifier (defaults to config default_author)")
    parser.add_argument("--session-id", default=None, help="Session identifier (default: auto)")
    parser.add_argument("--platform", default="claude_code", choices=("claude_code", "claude_web", "api", "other"))
    parser.add_argument("--model", default="unknown", help="AI model identifier")
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

    try:
        config = json.loads(config_path.read_text(encoding="utf-8"))
        registry = json.loads(registry_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as e:
        msg = f"Failed to read config/registry: {e}"
        print(json.dumps({"status": "error", "error": msg}) if args.json else f"ERROR: {msg}")
        return 2

    project_name = config.get("project_name", "Unknown Project")
    author = args.author or config.get("default_author", "Claude")
    session_id = args.session_id or f"session-{int(datetime.now().timestamp())}-{os.getpid()}"

    if len(args.title) < 5 or len(args.title) > 120:
        msg = "Title must be 5-120 characters."
        print(json.dumps({"status": "error", "error": msg}) if args.json else f"ERROR: {msg}")
        return 2
    if len(args.summary) < 10:
        msg = "Summary must be at least 10 characters."
        print(json.dumps({"status": "error", "error": msg}) if args.json else f"ERROR: {msg}")
        return 2

    name_slug = slugify(args.name)
    if not name_slug:
        msg = "Invalid name slug."
        print(json.dumps({"status": "error", "error": msg}) if args.json else f"ERROR: {msg}")
        return 2

    next_num = registry.get("next_tc_number", 1)
    today = datetime.now()
    tc_id = f"TC-{next_num:03d}-{date_slug(today)}-{name_slug}"

    record_dir = tc_dir / "records" / tc_id
    if record_dir.exists():
        msg = f"Record directory already exists: {record_dir}"
        print(json.dumps({"status": "error", "error": msg}) if args.json else f"ERROR: {msg}")
        return 2

    record = build_record(
        tc_id=tc_id,
        title=args.title,
        scope=args.scope,
        priority=args.priority,
        summary=args.summary,
        motivation=args.motivation,
        project_name=project_name,
        author=author,
        session_id=session_id,
        platform=args.platform,
        model=args.model,
    )

    try:
        record_dir.mkdir(parents=True, exist_ok=False)
        (tc_dir / "evidence" / tc_id).mkdir(parents=True, exist_ok=True)
        write_json_atomic(record_dir / "tc_record.json", record)
    except OSError as e:
        msg = f"Failed to write record: {e}"
        print(json.dumps({"status": "error", "error": msg}) if args.json else f"ERROR: {msg}")
        return 2

    registry_entry = {
        "tc_id": tc_id,
        "title": args.title,
        "status": "planned",
        "scope": args.scope,
        "priority": args.priority,
        "created": record["created"],
        "updated": record["updated"],
        "path": f"records/{tc_id}/tc_record.json",
    }
    registry["records"].append(registry_entry)
    registry["next_tc_number"] = next_num + 1
    registry["updated"] = now_iso()
    registry["statistics"] = compute_stats(registry["records"])

    try:
        write_json_atomic(registry_path, registry)
    except OSError as e:
        msg = f"Failed to update registry: {e}"
        print(json.dumps({"status": "error", "error": msg}) if args.json else f"ERROR: {msg}")
        return 2

    result = {
        "status": "created",
        "tc_id": tc_id,
        "title": args.title,
        "scope": args.scope,
        "priority": args.priority,
        "record_path": str(record_dir / "tc_record.json"),
    }
    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print(f"Created {tc_id}")
        print(f"  Title:    {args.title}")
        print(f"  Scope:    {args.scope}")
        print(f"  Priority: {args.priority}")
        print(f"  Record:   {record_dir / 'tc_record.json'}")
        print()
        print(f"Next: tc_update.py --root {args.root} --tc-id {tc_id} --set-status in_progress")

    return 0


if __name__ == "__main__":
    sys.exit(main())
