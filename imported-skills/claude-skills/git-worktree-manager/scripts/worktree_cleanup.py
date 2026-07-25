#!/usr/bin/env python3
"""Inspect and clean stale git worktrees with safety checks.

Supports:
- JSON input from stdin or --input file
- Stale age detection
- Dirty working tree detection
- Merged branch detection
- Optional removal of merged, clean stale worktrees
"""

import argparse
import json
import subprocess
import sys
import time
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Any, Dict, List, Optional


class CLIError(Exception):
    """Raised for expected CLI errors."""


@dataclass
class WorktreeInfo:
    path: str
    branch: str
    is_main: bool
    age_days: int
    stale: bool
    dirty: bool
    merged_into_base: bool


def run(cmd: List[str], cwd: Optional[Path] = None, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(cmd, cwd=cwd, text=True, capture_output=True, check=check)


def load_json_input(input_file: Optional[str]) -> Dict[str, Any]:
    if input_file:
        try:
            return json.loads(Path(input_file).read_text(encoding="utf-8"))
        except Exception as exc:
            raise CLIError(f"Failed reading --input file: {exc}") from exc
    if not sys.stdin.isatty():
        raw = sys.stdin.read().strip()
        if raw:
            try:
                return json.loads(raw)
            except json.JSONDecodeError as exc:
                raise CLIError(f"Invalid JSON from stdin: {exc}") from exc
    return {}


def parse_worktrees(repo: Path) -> List[Dict[str, str]]:
    proc = run(["git", "worktree", "list", "--porcelain"], cwd=repo)
    entries: List[Dict[str, str]] = []
    current: Dict[str, str] = {}
    for line in proc.stdout.splitlines():
        if not line.strip():
            if current:
                entries.append(current)
            current = {}
            continue
        key, _, value = line.partition(" ")
        current[key] = value
    if current:
        entries.append(current)
    return entries


def get_branch(path: Path) -> str:
    proc = run(["git", "rev-parse", "--abbrev-ref", "HEAD"], cwd=path)
    return proc.stdout.strip()


def get_last_commit_age_days(path: Path) -> int:
    proc = run(["git", "log", "-1", "--format=%ct"], cwd=path)
    timestamp = int(proc.stdout.strip() or "0")
    age_seconds = int(time.time()) - timestamp
    return max(0, age_seconds // 86400)


def is_dirty(path: Path) -> bool:
    proc = run(["git", "status", "--porcelain"], cwd=path)
    return bool(proc.stdout.strip())


def is_merged(repo: Path, branch: str, base_branch: str) -> bool:
    if branch in ("HEAD", base_branch):
        return False
    try:
        run(["git", "merge-base", "--is-ancestor", branch, base_branch], cwd=repo)
        return True
    except subprocess.CalledProcessError:
        return False


def format_text(items: List[WorktreeInfo], removed: List[str]) -> str:
    lines = ["Worktree cleanup report"]
    for item in items:
        lines.append(
            f"- {item.path} | branch={item.branch} | age={item.age_days}d | "
            f"stale={item.stale} dirty={item.dirty} merged={item.merged_into_base}"
        )
    if removed:
        lines.append("Removed:")
        for path in removed:
            lines.append(f"- {path}")
    return "\n".join(lines)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Analyze and optionally cleanup stale git worktrees.")
    parser.add_argument("--input", help="Path to JSON input file. If omitted, reads JSON from stdin when piped.")
    parser.add_argument("--repo", default=".", help="Repository root path.")
    parser.add_argument("--base-branch", default="main", help="Base branch to evaluate merged branches.")
    parser.add_argument("--stale-days", type=int, default=14, help="Threshold for stale worktrees.")
    parser.add_argument("--remove-merged", action="store_true", help="Remove worktrees that are stale, clean, and merged.")
    parser.add_argument("--force", action="store_true", help="Allow removal even if dirty (use carefully).")
    parser.add_argument("--format", choices=["text", "json"], default="text", help="Output format.")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    payload = load_json_input(args.input)

    repo = Path(str(payload.get("repo", args.repo))).resolve()
    stale_days = int(payload.get("stale_days", args.stale_days))
    base_branch = str(payload.get("base_branch", args.base_branch))
    remove_merged = bool(payload.get("remove_merged", args.remove_merged))
    force = bool(payload.get("force", args.force))

    try:
        run(["git", "rev-parse", "--is-inside-work-tree"], cwd=repo)
    except subprocess.CalledProcessError as exc:
        raise CLIError(f"Not a git repository: {repo}") from exc

    try:
        run(["git", "rev-parse", "--verify", base_branch], cwd=repo)
    except subprocess.CalledProcessError as exc:
        raise CLIError(f"Base branch not found: {base_branch}") from exc

    entries = parse_worktrees(repo)
    if not entries:
        raise CLIError("No worktrees found.")

    main_path = Path(entries[0].get("worktree", "")).resolve()
    infos: List[WorktreeInfo] = []
    removed: List[str] = []

    for entry in entries:
        path = Path(entry.get("worktree", "")).resolve()
        branch = get_branch(path)
        age = get_last_commit_age_days(path)
        dirty = is_dirty(path)
        stale = age >= stale_days
        merged = is_merged(repo, branch, base_branch)
        info = WorktreeInfo(
            path=str(path),
            branch=branch,
            is_main=path == main_path,
            age_days=age,
            stale=stale,
            dirty=dirty,
            merged_into_base=merged,
        )
        infos.append(info)

        if remove_merged and not info.is_main and info.stale and info.merged_into_base and (force or not info.dirty):
            try:
                cmd = ["git", "worktree", "remove", str(path)]
                if force:
                    cmd.append("--force")
                run(cmd, cwd=repo)
                removed.append(str(path))
            except subprocess.CalledProcessError as exc:
                raise CLIError(f"Failed removing worktree {path}: {exc.stderr}") from exc

    if args.format == "json":
        print(json.dumps({"worktrees": [asdict(i) for i in infos], "removed": removed}, indent=2))
    else:
        print(format_text(infos, removed))

    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except CLIError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
