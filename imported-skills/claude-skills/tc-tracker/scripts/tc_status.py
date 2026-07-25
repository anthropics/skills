#!/usr/bin/env python3
"""TC Status — Show TC status for one record or the entire registry.

Usage:
    # Single TC
    python3 tc_status.py --root . --tc-id <TC-ID>
    python3 tc_status.py --root . --tc-id <TC-ID> --json

    # All TCs (registry summary)
    python3 tc_status.py --root . --all
    python3 tc_status.py --root . --all --json

Exit codes:
    0 = ok
    1 = warnings (e.g. validation issues found while reading)
    2 = critical error (file missing, parse error, bad args)
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


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


def render_single(record: dict) -> str:
    lines = []
    lines.append(f"TC: {record.get('tc_id')}")
    lines.append(f"  Title:    {record.get('title')}")
    lines.append(f"  Status:   {record.get('status')}")
    lines.append(f"  Priority: {record.get('priority')}")
    desc = record.get("description", {}) or {}
    lines.append(f"  Scope:    {desc.get('scope')}")
    lines.append(f"  Created:  {record.get('created')}")
    lines.append(f"  Updated:  {record.get('updated')}")
    lines.append(f"  Author:   {record.get('created_by')}")
    lines.append("")

    summary = desc.get("summary") or ""
    if summary:
        lines.append(f"  Summary: {summary}")
    motivation = desc.get("motivation") or ""
    if motivation:
        lines.append(f"  Motivation: {motivation}")
    lines.append("")

    files = record.get("files_affected", []) or []
    lines.append(f"  Files affected: {len(files)}")
    for f in files[:10]:
        lines.append(f"    - {f.get('path')} ({f.get('action')})")
    if len(files) > 10:
        lines.append(f"    ... and {len(files) - 10} more")
    lines.append("")

    tests = record.get("test_cases", []) or []
    pass_count = sum(1 for t in tests if t.get("status") == "pass")
    fail_count = sum(1 for t in tests if t.get("status") == "fail")
    lines.append(f"  Tests: {pass_count} pass / {fail_count} fail / {len(tests)} total")
    lines.append("")

    revs = record.get("revision_history", []) or []
    lines.append(f"  Revisions: {len(revs)}")
    if revs:
        latest = revs[-1]
        lines.append(f"    Latest: {latest.get('revision_id')} {latest.get('timestamp')}")
        lines.append(f"            {latest.get('author')}: {latest.get('summary')}")
    lines.append("")

    handoff = (record.get("session_context", {}) or {}).get("handoff", {}) or {}
    if any(handoff.get(k) for k in ("progress_summary", "next_steps", "blockers", "key_context")):
        lines.append("  Handoff:")
        if handoff.get("progress_summary"):
            lines.append(f"    Progress: {handoff['progress_summary']}")
        if handoff.get("next_steps"):
            lines.append("    Next steps:")
            for s in handoff["next_steps"]:
                lines.append(f"      - {s}")
        if handoff.get("blockers"):
            lines.append("    Blockers:")
            for b in handoff["blockers"]:
                lines.append(f"      ! {b}")
        if handoff.get("key_context"):
            lines.append("    Key context:")
            for c in handoff["key_context"]:
                lines.append(f"      * {c}")

    appr = record.get("approval", {}) or {}
    lines.append("")
    lines.append(f"  Approved: {appr.get('approved')} ({appr.get('test_coverage_status')} coverage)")
    if appr.get("approved"):
        lines.append(f"    By: {appr.get('approved_by')} on {appr.get('approved_date')}")

    return "\n".join(lines)


def render_registry(registry: dict) -> str:
    lines = []
    lines.append(f"Project: {registry.get('project_name')}")
    lines.append(f"Updated: {registry.get('updated')}")
    stats = registry.get("statistics", {}) or {}
    lines.append(f"Total TCs: {stats.get('total', 0)}")
    by_status = stats.get("by_status", {}) or {}
    lines.append("By status:")
    for status, count in by_status.items():
        if count:
            lines.append(f"  {status:12} {count}")
    lines.append("")

    records = registry.get("records", []) or []
    if records:
        lines.append(f"{'TC ID':40} {'Status':14} {'Scope':14} {'Priority':10} Title")
        lines.append("-" * 100)
        for rec in records:
            lines.append("{:40} {:14} {:14} {:10} {}".format(
                rec.get("tc_id", "")[:40],
                rec.get("status", "")[:14],
                rec.get("scope", "")[:14],
                rec.get("priority", "")[:10],
                rec.get("title", ""),
            ))
    else:
        lines.append("No TC records yet. Run tc_create.py to add one.")

    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description="Show TC status.")
    parser.add_argument("--root", default=".", help="Project root (default: current directory)")
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--tc-id", help="Show this single TC")
    group.add_argument("--all", action="store_true", help="Show registry summary for all TCs")
    parser.add_argument("--json", action="store_true", help="Output as JSON")
    args = parser.parse_args()

    root = Path(args.root).resolve()
    tc_dir = root / "docs" / "TC"
    registry_path = tc_dir / "tc_registry.json"

    if not registry_path.exists():
        msg = f"TC tracking not initialized at {tc_dir}. Run tc_init.py first."
        print(json.dumps({"status": "error", "error": msg}) if args.json else f"ERROR: {msg}")
        return 2

    try:
        registry = json.loads(registry_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as e:
        msg = f"Failed to read registry: {e}"
        print(json.dumps({"status": "error", "error": msg}) if args.json else f"ERROR: {msg}")
        return 2

    if args.all:
        if args.json:
            print(json.dumps({
                "status": "ok",
                "project_name": registry.get("project_name"),
                "updated": registry.get("updated"),
                "statistics": registry.get("statistics", {}),
                "records": registry.get("records", []),
            }, indent=2))
        else:
            print(render_registry(registry))
        return 0

    record_path = find_record_path(tc_dir, args.tc_id)
    if record_path is None:
        msg = f"TC not found: {args.tc_id}"
        print(json.dumps({"status": "error", "error": msg}) if args.json else f"ERROR: {msg}")
        return 2

    try:
        record = json.loads(record_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as e:
        msg = f"Failed to read record: {e}"
        print(json.dumps({"status": "error", "error": msg}) if args.json else f"ERROR: {msg}")
        return 2

    if args.json:
        print(json.dumps({"status": "ok", "record": record}, indent=2))
    else:
        print(render_single(record))

    return 0


if __name__ == "__main__":
    sys.exit(main())
