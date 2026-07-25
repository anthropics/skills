#!/usr/bin/env python3
"""Cleanup old handoff scaffolds — mtime-guarded.

Deletes handoff files older than the configured retention window. NEVER
deletes a file whose mtime > ctime (i.e., touched after generation). That
guard prevents data loss if a user used the handoff doc as a working
surface for notes.

Stdlib-only.
"""


import argparse
import datetime as dt
import json
import os
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import config_loader  # noqa: E402

HANDOFF_FILENAME_PATTERNS = ("handoff-", "handoff_", "handoff.md")


def _candidate_dirs(config: dict) -> list[Path]:
    save = config.get("save_location", {})
    mode = save.get("mode", "temp")
    raw_path = save.get("path")
    dirs: list[Path] = []
    if mode == "temp":
        dirs.append(Path(tempfile.gettempdir()))
    elif raw_path:
        dirs.append(Path(raw_path))
    else:
        dirs.append(Path(tempfile.gettempdir()))
    return [d for d in dirs if d.exists()]


def _looks_like_handoff(p: Path) -> bool:
    name = p.name.lower()
    if not name.endswith(".md"):
        return False
    return any(token in name for token in HANDOFF_FILENAME_PATTERNS)


def _was_edited(stat: os.stat_result, slack_seconds: int = 2) -> bool:
    """True if mtime is meaningfully newer than ctime (file was edited)."""
    try:
        return (stat.st_mtime - stat.st_ctime) > slack_seconds
    except AttributeError:
        return False


def find_candidates(config: dict) -> list[Path]:
    out: list[Path] = []
    for d in _candidate_dirs(config):
        try:
            for entry in d.iterdir():
                if entry.is_file() and _looks_like_handoff(entry):
                    out.append(entry)
        except OSError:
            continue
    return out


def plan_cleanup(config: dict, now: dt.datetime | None = None) -> dict:
    retention = int(config.get("retention_days", 7))
    now = now or dt.datetime.utcnow()
    plan = {
        "retention_days": retention,
        "candidates": [],
        "to_delete": [],
        "preserved_edited": [],
        "preserved_recent": [],
        "errors": [],
    }
    if retention <= 0:
        plan["mode"] = "disabled"
        return plan
    plan["mode"] = "active"
    cutoff = now - dt.timedelta(days=retention)
    for path in find_candidates(config):
        try:
            stat = path.stat()
        except OSError as exc:
            plan["errors"].append({"path": str(path), "error": str(exc)})
            continue
        ctime = dt.datetime.utcfromtimestamp(stat.st_ctime)
        entry = {
            "path": str(path),
            "ctime": ctime.isoformat() + "Z",
            "age_days": round((now - ctime).total_seconds() / 86400, 2),
        }
        plan["candidates"].append(entry)
        if _was_edited(stat):
            plan["preserved_edited"].append(entry)
            continue
        if ctime > cutoff:
            plan["preserved_recent"].append(entry)
            continue
        plan["to_delete"].append(entry)
    return plan


def execute(plan: dict, dry_run: bool = False) -> list[str]:
    deleted: list[str] = []
    if plan.get("mode") != "active":
        return deleted
    for entry in plan["to_delete"]:
        path = Path(entry["path"])
        if dry_run:
            deleted.append(str(path))
            continue
        try:
            path.unlink()
            deleted.append(str(path))
        except OSError:
            continue
    return deleted


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Cleanup old handoff scaffolds (mtime-guarded).")
    parser.add_argument("--dry-run", action="store_true", help="Print the plan, do not delete.")
    parser.add_argument("--json", action="store_true", help="Emit JSON.")
    parser.add_argument("--sample", action="store_true", help="Run the plan without deleting.")
    args = parser.parse_args(argv)

    config = config_loader.load_config()
    plan = plan_cleanup(config)

    if args.sample or args.dry_run:
        deleted = execute(plan, dry_run=True)
    else:
        deleted = execute(plan, dry_run=False)

    if args.json:
        out = dict(plan)
        out["deleted"] = deleted
        out["dry_run"] = bool(args.sample or args.dry_run)
        print(json.dumps(out, indent=2))
        return 0

    print(f"Retention window: {plan['retention_days']} days (mode: {plan['mode']})")
    print(f"Candidates inspected: {len(plan['candidates'])}")
    print(f"Preserved (edited):   {len(plan['preserved_edited'])}")
    print(f"Preserved (recent):   {len(plan['preserved_recent'])}")
    print(f"Eligible for delete:  {len(plan['to_delete'])}")
    if args.sample or args.dry_run:
        print("Dry-run — no files removed.")
        for entry in plan["to_delete"]:
            print(f"  would delete: {entry['path']} (age {entry['age_days']}d)")
    else:
        print(f"Deleted: {len(deleted)}")
        for path in deleted:
            print(f"  removed: {path}")
    if plan["errors"]:
        print(f"Errors: {len(plan['errors'])}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
