#!/usr/bin/env python3
"""Retroactive TC Batch Generator — Creates TC records from a structured changelog.

Reads a retro_changelog.json file and batch-creates all TC records, validates them,
generates HTML pages, updates the registry, and regenerates the dashboard.

Usage:
    python generate_retro_tcs.py <retro_changelog.json> <tc_root_dir>

    retro_changelog.json: Path to the changelog file matching tc_retro_changelog.schema.json
    tc_root_dir: Path to the project's docs/TC/ directory (must already be initialized)

Example:
    python generate_retro_tcs.py retro_changelog.json "/path/to/project/docs/TC"

Exit codes:
    0 = SUCCESS
    1 = VALIDATION ERRORS
    2 = FILE NOT FOUND or other errors
"""

from __future__ import annotations

import json
import os
import re
import sys
from datetime import datetime, timezone
from pathlib import Path

# Add parent dirs for imports
_SKILL_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(_SKILL_ROOT / "validators"))
sys.path.insert(0, str(_SKILL_ROOT / "generators"))

from validate_tc import (  # noqa: E402
    validate_tc_record,
    validate_registry,
    compute_registry_statistics,
    slugify,
    VALID_STATUSES,
    VALID_SCOPES,
    VALID_PRIORITIES,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _now_iso() -> str:
    """Return current time as ISO 8601 string with timezone."""
    return datetime.now(timezone.utc).astimezone().isoformat()


def _date_to_iso(date_str: str | None, fallback: str | None = None) -> str:
    """Convert YYYY-MM-DD to ISO 8601 datetime string."""
    if not date_str:
        return fallback or _now_iso()
    try:
        dt = datetime.strptime(date_str, "%Y-%m-%d")
        dt = dt.replace(hour=12, tzinfo=timezone.utc).astimezone()
        return dt.isoformat()
    except ValueError:
        return fallback or _now_iso()


def _date_to_mmddyy(date_str: str | None) -> str:
    """Convert YYYY-MM-DD to MM-DD-YY format for TC IDs."""
    if not date_str:
        now = datetime.now()
        return now.strftime("%m-%d-%y")
    try:
        dt = datetime.strptime(date_str, "%Y-%m-%d")
        return dt.strftime("%m-%d-%y")
    except ValueError:
        now = datetime.now()
        return now.strftime("%m-%d-%y")


def _validate_changelog(changelog: dict) -> list[str]:
    """Validate the retro changelog structure."""
    errors: list[str] = []

    if not isinstance(changelog, dict):
        return ["Changelog must be a JSON object"]

    if "project" not in changelog:
        errors.append("Missing required field: 'project'")
    if "changes" not in changelog:
        errors.append("Missing required field: 'changes'")
        return errors

    changes = changelog["changes"]
    if not isinstance(changes, list):
        errors.append("'changes' must be an array")
        return errors

    if len(changes) == 0:
        errors.append("'changes' must have at least 1 entry")

    for i, change in enumerate(changes):
        prefix = f"changes[{i}]"
        if not isinstance(change, dict):
            errors.append(f"{prefix} must be an object")
            continue

        # Required fields
        for field in ("title", "scope", "description"):
            if field not in change:
                errors.append(f"{prefix} missing required field: '{field}'")

        if "scope" in change and change["scope"] not in VALID_SCOPES:
            errors.append(f"{prefix}.scope '{change['scope']}' invalid")

        if "priority" in change and change["priority"] not in VALID_PRIORITIES:
            errors.append(f"{prefix}.priority '{change['priority']}' invalid")

        if "status" in change and change["status"] not in VALID_STATUSES:
            errors.append(f"{prefix}.status '{change['status']}' invalid")

        if "title" in change and isinstance(change["title"], str):
            if len(change["title"]) < 5:
                errors.append(f"{prefix}.title must be at least 5 characters")

        if "description" in change and isinstance(change["description"], str):
            if len(change["description"]) < 10:
                errors.append(f"{prefix}.description must be at least 10 characters")

    return errors


# ---------------------------------------------------------------------------
# TC Record Builder
# ---------------------------------------------------------------------------

def build_tc_record(
    tc_number: int,
    change: dict,
    project: str,
    author: str,
) -> dict:
    """Build a complete tc_record.json from a changelog entry."""
    date_str = change.get("date")
    mmddyy = _date_to_mmddyy(date_str)
    title_slug = slugify(change["title"])

    # Truncate slug to keep ID reasonable
    if len(title_slug) > 60:
        title_slug = title_slug[:60].rstrip("-")

    tc_id = f"TC-{tc_number:03d}-{mmddyy}-{title_slug}"
    iso_date = _date_to_iso(date_str)
    now = _now_iso()

    status = change.get("status", "deployed")
    priority = change.get("priority", "medium")
    scope = change["scope"]
    description_text = change["description"]
    motivation = change.get("motivation") or description_text
    detailed_design = change.get("detailed_design")

    # Build files_affected from the files list
    files_affected = []
    for f in change.get("files", []):
        files_affected.append({
            "path": f.replace("\\", "/"),
            "action": "modified",
            "description": None,
            "lines_added": None,
            "lines_removed": None,
        })

    # Build the record
    record = {
        "tc_id": tc_id,
        "parent_tc": None,
        "title": change["title"],
        "status": status,
        "priority": priority,
        "created": iso_date,
        "updated": now,
        "created_by": author,
        "project": project,
        "description": {
            "summary": description_text,
            "motivation": motivation,
            "scope": scope,
            "detailed_design": detailed_design,
            "breaking_changes": change.get("breaking_changes", []),
            "dependencies": change.get("dependencies", []),
        },
        "files_affected": files_affected,
        "revision_history": [
            {
                "revision_id": "R1",
                "timestamp": iso_date,
                "author": author,
                "summary": f"Retroactive TC creation — {change['title']}",
                "field_changes": [
                    {
                        "field": "status",
                        "action": "set",
                        "new_value": status,
                        "reason": "Retroactive documentation of existing change",
                    }
                ],
            }
        ],
        "sub_tcs": [],
        "test_cases": [],
        "approval": {
            "approved": status == "deployed",
            "approved_by": author if status == "deployed" else None,
            "approved_date": now if status == "deployed" else None,
            "approval_notes": "Retroactive approval — change was already in production" if status == "deployed" else "",
            "test_coverage_status": "none",
        },
        "session_context": {
            "current_session": {
                "session_id": "retro-batch-generation",
                "platform": "claude_code",
                "model": "batch-generator",
                "started": now,
                "last_active": now,
            },
            "handoff": {
                "progress_summary": f"Retroactive TC created for: {change['title']}",
                "next_steps": [],
                "blockers": [],
                "key_context": ["This TC was created retroactively from project history"],
                "files_in_progress": [],
                "decisions_made": [],
            },
            "session_history": [],
        },
        "tags": change.get("tags", []),
        "related_tcs": [],
        "notes": f"Retroactively documented.{' Version: ' + change['version'] if change.get('version') else ''}",
        "metadata": {
            "project": project,
            "created_by": author,
            "last_modified_by": author,
            "last_modified": now,
            "estimated_effort": None,
        },
    }

    return record


# ---------------------------------------------------------------------------
# Batch Processor
# ---------------------------------------------------------------------------

def process_retro_changelog(changelog: dict, tc_root: Path) -> tuple[int, int, list[str]]:
    """Process the entire retro changelog.

    Returns: (created_count, error_count, error_messages)
    """
    project = changelog["project"]
    author = changelog.get("default_author", "retroactive")
    changes = changelog["changes"]

    # Read existing registry
    registry_path = tc_root / "tc_registry.json"
    if not registry_path.exists():
        return 0, 0, ["tc_registry.json not found — run /tc init first"]

    with open(registry_path, "r", encoding="utf-8") as f:
        registry = json.load(f)

    records_dir = tc_root / "records"
    records_dir.mkdir(parents=True, exist_ok=True)

    created = 0
    errors_list: list[str] = []
    start_number = registry.get("next_tc_number", 1)

    # Build a mapping of index -> tc_id for related_tcs
    tc_id_map: dict[int, str] = {}

    print(f"Processing {len(changes)} changes for project '{project}'...")
    print()

    for i, change in enumerate(changes):
        tc_number = start_number + i
        record = build_tc_record(tc_number, change, project, author)
        tc_id = record["tc_id"]
        tc_id_map[i] = tc_id

        # Validate
        validation_errors = validate_tc_record(record)
        if validation_errors:
            errors_list.append(f"TC-{tc_number:03d} ({change['title']}): {'; '.join(validation_errors)}")
            continue

        # Create directory
        tc_dir = records_dir / tc_id
        tc_dir.mkdir(parents=True, exist_ok=True)

        # Write record (atomic: write to .tmp then rename)
        tmp_path = tc_dir / "tc_record.json.tmp"
        final_path = tc_dir / "tc_record.json"

        with open(tmp_path, "w", encoding="utf-8") as f:
            json.dump(record, f, indent=2, ensure_ascii=False)
        tmp_path.replace(final_path)

        # Add to registry
        date_mmddyy = _date_to_mmddyy(change.get("date"))
        registry["records"].append({
            "tc_id": tc_id,
            "title": change["title"],
            "status": record["status"],
            "scope": change["scope"],
            "priority": record["priority"],
            "created": record["created"],
            "updated": record["updated"],
            "path": f"records/{tc_id}",
            "sub_tc_count": 0,
            "test_summary": {
                "total": 0, "pass": 0, "fail": 0,
                "pending": 0, "skip": 0, "blocked": 0,
            },
        })

        created += 1
        status_icon = "+" if record["status"] == "deployed" else "~"
        print(f"  [{status_icon}] {tc_id}: {change['title']}")

    # Resolve related_tcs references
    for i, change in enumerate(changes):
        related_indices = change.get("related_indices", [])
        if related_indices and i in tc_id_map:
            tc_id = tc_id_map[i]
            tc_dir = records_dir / tc_id
            record_path = tc_dir / "tc_record.json"
            if record_path.exists():
                with open(record_path, "r", encoding="utf-8") as f:
                    record = json.load(f)
                record["related_tcs"] = [
                    tc_id_map[idx] for idx in related_indices
                    if idx in tc_id_map and idx != i
                ]
                with open(record_path, "w", encoding="utf-8") as f:
                    json.dump(record, f, indent=2, ensure_ascii=False)

    # Update registry
    registry["next_tc_number"] = start_number + len(changes)
    registry["updated"] = _now_iso()
    registry["statistics"] = compute_registry_statistics(registry["records"])

    # Write registry (atomic)
    tmp_reg = tc_root / "tc_registry.json.tmp"
    with open(tmp_reg, "w", encoding="utf-8") as f:
        json.dump(registry, f, indent=2, ensure_ascii=False)
    tmp_reg.replace(registry_path)

    print()
    print(f"Created: {created}/{len(changes)} TC records")
    if errors_list:
        print(f"Errors: {len(errors_list)}")
        for err in errors_list:
            print(f"  ! {err}")

    return created, len(errors_list), errors_list


def generate_all_html(tc_root: Path) -> int:
    """Generate HTML for all TC records and the dashboard."""
    from generate_tc_html import generate_tc_html, _load_css  # noqa: E402
    from generate_dashboard import generate_dashboard_html  # noqa: E402

    css = _load_css()
    records_dir = tc_root / "records"
    generated = 0

    if records_dir.exists():
        for tc_dir in sorted(records_dir.iterdir()):
            record_path = tc_dir / "tc_record.json"
            if record_path.exists():
                try:
                    with open(record_path, "r", encoding="utf-8") as f:
                        record = json.load(f)
                    html = generate_tc_html(record, css)
                    html_path = tc_dir / "tc_record.html"
                    with open(html_path, "w", encoding="utf-8") as f:
                        f.write(html)
                    generated += 1
                except Exception as e:
                    print(f"  ! HTML error for {tc_dir.name}: {e}")

    # Generate dashboard
    registry_path = tc_root / "tc_registry.json"
    if registry_path.exists():
        with open(registry_path, "r", encoding="utf-8") as f:
            registry = json.load(f)
        dashboard_html = generate_dashboard_html(registry, css, tc_root)
        with open(tc_root / "index.html", "w", encoding="utf-8") as f:
            f.write(dashboard_html)
        print(f"  Dashboard generated")

    return generated


# ---------------------------------------------------------------------------
# CLI Entry Point
# ---------------------------------------------------------------------------

def main() -> int:
    """CLI entry point."""
    if len(sys.argv) < 3:
        print("Usage: python generate_retro_tcs.py <retro_changelog.json> <tc_root_dir>")
        print()
        print("  retro_changelog.json: Structured changelog file")
        print("  tc_root_dir: Project's docs/TC/ directory (must be initialized)")
        return 2

    changelog_path = Path(sys.argv[1])
    tc_root = Path(sys.argv[2])

    if not changelog_path.exists():
        print(f"ERROR: Changelog not found: {changelog_path}")
        return 2

    if not (tc_root / "tc_registry.json").exists():
        print(f"ERROR: tc_registry.json not found in {tc_root}")
        print("Run /tc init first to initialize TC tracking.")
        return 2

    # Load and validate changelog
    try:
        with open(changelog_path, "r", encoding="utf-8") as f:
            changelog = json.load(f)
    except json.JSONDecodeError as e:
        print(f"ERROR: Invalid JSON: {e}")
        return 2

    errors = _validate_changelog(changelog)
    if errors:
        print(f"CHANGELOG VALIDATION ERRORS ({len(errors)}):")
        for i, err in enumerate(errors, 1):
            print(f"  {i}. {err}")
        return 1

    # Process
    print(f"=== TC Retro Batch Generator ===")
    print(f"Project: {changelog['project']}")
    print(f"Changes: {len(changelog['changes'])}")
    print(f"TC Root: {tc_root}")
    print()

    created, error_count, error_msgs = process_retro_changelog(changelog, tc_root)

    if created > 0:
        print()
        print(f"Generating HTML for {created} records...")
        html_count = generate_all_html(tc_root)
        print(f"Generated {html_count} HTML pages + dashboard")

    print()
    if error_count == 0:
        print(f"SUCCESS: {created} TC records created, validated, and rendered.")
        return 0
    else:
        print(f"PARTIAL: {created} created, {error_count} errors.")
        return 1


if __name__ == "__main__":
    sys.exit(main())
