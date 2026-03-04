#!/usr/bin/env python3
"""
safe_backup.py - Snapshot and revert files during multi-edit sessions.

Creates timestamped backups before edits, lists available snapshots,
and reverts to any previous version with one command.

Usage:
    python safe_backup.py snapshot file.py              # Create backup
    python safe_backup.py snapshot file.py "before refactor"  # With label
    python safe_backup.py list file.py                  # Show all backups
    python safe_backup.py revert file.py                # Revert to latest backup
    python safe_backup.py revert file.py 2              # Revert to snapshot #2
    python safe_backup.py diff file.py                  # Diff current vs latest backup
    python safe_backup.py diff file.py 2                # Diff current vs snapshot #2
    python safe_backup.py clean file.py                 # Remove all backups
"""

import argparse
import os
import shutil
import json
import difflib
from datetime import datetime
from pathlib import Path

BACKUP_DIR = ".safe-edit-backups"


def get_backup_dir(filepath):
    """Get or create backup directory for a file."""
    filepath = Path(filepath).resolve()
    backup_dir = filepath.parent / BACKUP_DIR / filepath.name
    backup_dir.mkdir(parents=True, exist_ok=True)
    return backup_dir


def get_manifest_path(filepath):
    """Get path to the manifest file tracking all snapshots."""
    return get_backup_dir(filepath) / "manifest.json"


def load_manifest(filepath):
    """Load or create the snapshot manifest."""
    manifest_path = get_manifest_path(filepath)
    if manifest_path.exists():
        with open(manifest_path, 'r') as f:
            return json.load(f)
    return {"file": str(Path(filepath).resolve()), "snapshots": []}


def save_manifest(filepath, manifest):
    """Save the snapshot manifest."""
    with open(get_manifest_path(filepath), 'w') as f:
        json.dump(manifest, f, indent=2)


def snapshot(filepath, label=None):
    """Create a snapshot of the current file state."""
    filepath = Path(filepath).resolve()
    if not filepath.exists():
        print(f"Error: {filepath} not found")
        return False

    manifest = load_manifest(filepath)
    snapshot_num = len(manifest["snapshots"]) + 1
    timestamp = datetime.now().isoformat()
    backup_name = f"snapshot_{snapshot_num:03d}.bak"
    backup_path = get_backup_dir(filepath) / backup_name

    shutil.copy2(filepath, backup_path)

    # Get file stats for the manifest
    stat = filepath.stat()
    with open(filepath, 'r', errors='replace') as f:
        line_count = sum(1 for _ in f)

    manifest["snapshots"].append({
        "num": snapshot_num,
        "timestamp": timestamp,
        "label": label or f"Snapshot {snapshot_num}",
        "backup_file": backup_name,
        "size_bytes": stat.st_size,
        "line_count": line_count
    })
    save_manifest(filepath, manifest)

    label_str = f' "{label}"' if label else ""
    print(f"Snapshot #{snapshot_num}{label_str} created")
    print(f"  File: {filepath.name} ({line_count} lines, {stat.st_size} bytes)")
    print(f"  Time: {timestamp}")
    return True


def list_snapshots(filepath):
    """List all available snapshots for a file."""
    manifest = load_manifest(filepath)
    snapshots = manifest["snapshots"]

    if not snapshots:
        print(f"No snapshots found for {filepath}")
        return

    filepath = Path(filepath).resolve()
    print(f"Snapshots for {filepath.name}:")
    print(f"{'#':>3}  {'Timestamp':<20} {'Lines':>6} {'Size':>8}  Label")
    print(f"{'─'*3}  {'─'*20} {'─'*6} {'─'*8}  {'─'*30}")

    for s in snapshots:
        ts = s['timestamp'][:19].replace('T', ' ')
        size = f"{s['size_bytes']:,}"
        print(f"{s['num']:>3}  {ts:<20} {s['line_count']:>6} {size:>8}  {s['label']}")

    # Show current file stats for comparison
    if filepath.exists():
        stat = filepath.stat()
        with open(filepath, 'r', errors='replace') as f:
            current_lines = sum(1 for _ in f)
        print(f"\n  Current: {current_lines} lines, {stat.st_size:,} bytes")


def revert(filepath, snapshot_num=None):
    """Revert file to a previous snapshot."""
    manifest = load_manifest(filepath)
    snapshots = manifest["snapshots"]

    if not snapshots:
        print(f"No snapshots found for {filepath}")
        return False

    if snapshot_num is None:
        target = snapshots[-1]
    else:
        matches = [s for s in snapshots if s['num'] == snapshot_num]
        if not matches:
            print(f"Snapshot #{snapshot_num} not found")
            list_snapshots(filepath)
            return False
        target = matches[0]

    filepath = Path(filepath).resolve()
    backup_path = get_backup_dir(filepath) / target['backup_file']

    if not backup_path.exists():
        print(f"Error: Backup file {backup_path} missing")
        return False

    # Create a safety snapshot of the current state before reverting
    snapshot(filepath, label=f"Auto-backup before revert to #{target['num']}")

    shutil.copy2(backup_path, filepath)
    print(f"Reverted to snapshot #{target['num']}: {target['label']}")
    print(f"  Restored: {target['line_count']} lines, {target['size_bytes']} bytes")
    return True


def diff_snapshot(filepath, snapshot_num=None):
    """Show diff between current file and a snapshot."""
    manifest = load_manifest(filepath)
    snapshots = manifest["snapshots"]

    if not snapshots:
        print(f"No snapshots found for {filepath}")
        return

    if snapshot_num is None:
        target = snapshots[-1]
    else:
        matches = [s for s in snapshots if s['num'] == snapshot_num]
        if not matches:
            print(f"Snapshot #{snapshot_num} not found")
            return
        target = matches[0]

    filepath = Path(filepath).resolve()
    backup_path = get_backup_dir(filepath) / target['backup_file']

    with open(backup_path, 'r', errors='replace') as f:
        old_lines = f.readlines()
    with open(filepath, 'r', errors='replace') as f:
        new_lines = f.readlines()

    diff = difflib.unified_diff(
        old_lines, new_lines,
        fromfile=f"snapshot #{target['num']} ({target['label']})",
        tofile="current",
        lineterm=''
    )

    diff_lines = list(diff)
    if not diff_lines:
        print(f"No differences from snapshot #{target['num']}")
    else:
        additions = sum(1 for l in diff_lines if l.startswith('+') and not l.startswith('+++'))
        deletions = sum(1 for l in diff_lines if l.startswith('-') and not l.startswith('---'))
        print(f"Diff vs snapshot #{target['num']} ({target['label']}):")
        print(f"  +{additions} lines added, -{deletions} lines removed\n")
        for line in diff_lines[:100]:  # Limit output
            print(line.rstrip('\n'))
        if len(diff_lines) > 100:
            print(f"\n  ... ({len(diff_lines) - 100} more diff lines)")


def clean(filepath):
    """Remove all backups for a file."""
    backup_dir = get_backup_dir(filepath)
    if backup_dir.exists():
        shutil.rmtree(backup_dir)
        print(f"Cleaned all backups for {filepath}")
    else:
        print(f"No backups found for {filepath}")


def main():
    parser = argparse.ArgumentParser(description="Safe file backup and revert")
    parser.add_argument("command", choices=["snapshot", "list", "revert", "diff", "clean"])
    parser.add_argument("file", help="Target file path")
    parser.add_argument("arg", nargs="?", help="Snapshot number or label")
    args = parser.parse_args()

    if args.command == "snapshot":
        snapshot(args.file, label=args.arg)
    elif args.command == "list":
        list_snapshots(args.file)
    elif args.command == "revert":
        num = int(args.arg) if args.arg and args.arg.isdigit() else None
        revert(args.file, num)
    elif args.command == "diff":
        num = int(args.arg) if args.arg and args.arg.isdigit() else None
        diff_snapshot(args.file, num)
    elif args.command == "clean":
        clean(args.file)


if __name__ == "__main__":
    main()
