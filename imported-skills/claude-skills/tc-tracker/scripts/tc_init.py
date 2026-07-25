#!/usr/bin/env python3
"""TC Init — Initialize TC tracking inside a project.

Creates docs/TC/ with tc_config.json, tc_registry.json, records/, and evidence/.
Idempotent: re-running on an already-initialized project reports current stats
and exits cleanly.

Usage:
    python3 tc_init.py --project "My Project" --root .
    python3 tc_init.py --project "My Project" --root /path/to/project --json

Exit codes:
    0 = initialized OR already initialized
    1 = warnings (e.g. partial state)
    2 = bad CLI args / I/O error
"""

from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path

VALID_STATUSES = ("planned", "in_progress", "blocked", "implemented", "tested", "deployed")
VALID_SCOPES = ("feature", "bugfix", "refactor", "infrastructure", "documentation", "hotfix", "enhancement")
VALID_PRIORITIES = ("critical", "high", "medium", "low")


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def detect_project_name(root: Path) -> str:
    """Try CLAUDE.md heading, package.json name, pyproject.toml name, then directory basename."""
    claude_md = root / "CLAUDE.md"
    if claude_md.exists():
        try:
            for line in claude_md.read_text(encoding="utf-8").splitlines():
                line = line.strip()
                if line.startswith("# "):
                    return line[2:].strip()
        except OSError:
            pass

    pkg = root / "package.json"
    if pkg.exists():
        try:
            data = json.loads(pkg.read_text(encoding="utf-8"))
            name = data.get("name")
            if isinstance(name, str) and name.strip():
                return name.strip()
        except (OSError, json.JSONDecodeError):
            pass

    pyproject = root / "pyproject.toml"
    if pyproject.exists():
        try:
            for line in pyproject.read_text(encoding="utf-8").splitlines():
                stripped = line.strip()
                if stripped.startswith("name") and "=" in stripped:
                    value = stripped.split("=", 1)[1].strip().strip('"').strip("'")
                    if value:
                        return value
        except OSError:
            pass

    return root.resolve().name


def build_config(project_name: str) -> dict:
    return {
        "project_name": project_name,
        "tc_root": "docs/TC",
        "created": now_iso(),
        "auto_track": True,
        "default_author": "Claude",
        "categories": list(VALID_SCOPES),
    }


def build_registry(project_name: str) -> dict:
    return {
        "project_name": project_name,
        "created": now_iso(),
        "updated": now_iso(),
        "next_tc_number": 1,
        "records": [],
        "statistics": {
            "total": 0,
            "by_status": {s: 0 for s in VALID_STATUSES},
            "by_scope": {s: 0 for s in VALID_SCOPES},
            "by_priority": {p: 0 for p in VALID_PRIORITIES},
        },
    }


def write_json_atomic(path: Path, data: dict) -> None:
    """Write JSON to a temp file and rename, to avoid partial writes."""
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    tmp.replace(path)


def main() -> int:
    parser = argparse.ArgumentParser(description="Initialize TC tracking in a project.")
    parser.add_argument("--root", default=".", help="Project root directory (default: current directory)")
    parser.add_argument("--project", help="Project name (auto-detected if omitted)")
    parser.add_argument("--force", action="store_true", help="Re-initialize even if config exists (preserves registry)")
    parser.add_argument("--json", action="store_true", help="Output as JSON")
    args = parser.parse_args()

    root = Path(args.root).resolve()
    if not root.exists() or not root.is_dir():
        msg = f"Project root does not exist or is not a directory: {root}"
        print(json.dumps({"status": "error", "error": msg}) if args.json else f"ERROR: {msg}")
        return 2

    tc_dir = root / "docs" / "TC"
    config_path = tc_dir / "tc_config.json"
    registry_path = tc_dir / "tc_registry.json"

    if config_path.exists() and not args.force:
        try:
            cfg = json.loads(config_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as e:
            msg = f"Existing tc_config.json is unreadable: {e}"
            print(json.dumps({"status": "error", "error": msg}) if args.json else f"ERROR: {msg}")
            return 2

        stats = {}
        if registry_path.exists():
            try:
                reg = json.loads(registry_path.read_text(encoding="utf-8"))
                stats = reg.get("statistics", {})
            except (OSError, json.JSONDecodeError):
                stats = {}

        result = {
            "status": "already_initialized",
            "project_name": cfg.get("project_name"),
            "tc_root": str(tc_dir),
            "statistics": stats,
        }
        if args.json:
            print(json.dumps(result, indent=2))
        else:
            print(f"TC tracking already initialized for project '{cfg.get('project_name')}'.")
            print(f"  TC root: {tc_dir}")
            if stats:
                print(f"  Total TCs: {stats.get('total', 0)}")
        return 0

    project_name = args.project or detect_project_name(root)

    try:
        tc_dir.mkdir(parents=True, exist_ok=True)
        (tc_dir / "records").mkdir(exist_ok=True)
        (tc_dir / "evidence").mkdir(exist_ok=True)
        write_json_atomic(config_path, build_config(project_name))
        if not registry_path.exists() or args.force:
            write_json_atomic(registry_path, build_registry(project_name))
    except OSError as e:
        msg = f"Failed to create TC directories or files: {e}"
        print(json.dumps({"status": "error", "error": msg}) if args.json else f"ERROR: {msg}")
        return 2

    result = {
        "status": "initialized",
        "project_name": project_name,
        "tc_root": str(tc_dir),
        "files_created": [
            str(config_path),
            str(registry_path),
            str(tc_dir / "records"),
            str(tc_dir / "evidence"),
        ],
    }
    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print(f"Initialized TC tracking for project '{project_name}'")
        print(f"  TC root:   {tc_dir}")
        print(f"  Config:    {config_path}")
        print(f"  Registry:  {registry_path}")
        print(f"  Records:   {tc_dir / 'records'}")
        print(f"  Evidence:  {tc_dir / 'evidence'}")
        print()
        print("Next: python3 tc_create.py --root . --name <slug> --title <title> --scope <scope> ...")

    return 0


if __name__ == "__main__":
    sys.exit(main())
