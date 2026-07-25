#!/usr/bin/env python3
"""Create and prepare git worktrees with deterministic port allocation.

Supports:
- JSON input from stdin or --input file
- Worktree creation from existing/new branch
- .env file sync from main repo
- Optional dependency installation
- JSON or text output
"""

import argparse
import json
import os
import shutil
import subprocess
import sys
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Any, Dict, List, Optional


ENV_FILES = [".env", ".env.local", ".env.development", ".envrc"]
LOCKFILE_COMMANDS = [
    ("pnpm-lock.yaml", ["pnpm", "install"]),
    ("yarn.lock", ["yarn", "install"]),
    ("package-lock.json", ["npm", "install"]),
    ("bun.lockb", ["bun", "install"]),
    ("requirements.txt", [sys.executable, "-m", "pip", "install", "-r", "requirements.txt"]),
]


@dataclass
class WorktreeResult:
    repo: str
    worktree_path: str
    branch: str
    created: bool
    ports: Dict[str, int]
    copied_env_files: List[str]
    dependency_install: str


class CLIError(Exception):
    """Raised for expected CLI errors."""


def run(cmd: List[str], cwd: Optional[Path] = None, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(cmd, cwd=cwd, text=True, capture_output=True, check=check)


def load_json_input(input_file: Optional[str]) -> Dict[str, Any]:
    if input_file:
        try:
            return json.loads(Path(input_file).read_text(encoding="utf-8"))
        except Exception as exc:
            raise CLIError(f"Failed reading --input file: {exc}") from exc

    if not sys.stdin.isatty():
        data = sys.stdin.read().strip()
        if data:
            try:
                return json.loads(data)
            except json.JSONDecodeError as exc:
                raise CLIError(f"Invalid JSON from stdin: {exc}") from exc
    return {}


def parse_worktree_list(repo: Path) -> List[Dict[str, str]]:
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


def find_next_ports(repo: Path, app_base: int, db_base: int, redis_base: int, stride: int) -> Dict[str, int]:
    used_ports = set()
    for entry in parse_worktree_list(repo):
        wt_path = Path(entry.get("worktree", ""))
        ports_file = wt_path / ".worktree-ports.json"
        if ports_file.exists():
            try:
                payload = json.loads(ports_file.read_text(encoding="utf-8"))
                used_ports.update(int(v) for v in payload.values() if isinstance(v, int))
            except Exception:
                continue

    index = 0
    while True:
        ports = {
            "app": app_base + (index * stride),
            "db": db_base + (index * stride),
            "redis": redis_base + (index * stride),
        }
        if all(p not in used_ports for p in ports.values()):
            return ports
        index += 1


def sync_env_files(src_repo: Path, dest_repo: Path) -> List[str]:
    copied = []
    for name in ENV_FILES:
        src = src_repo / name
        if src.exists() and src.is_file():
            dst = dest_repo / name
            shutil.copy2(src, dst)
            copied.append(name)
    return copied


def install_dependencies_if_requested(worktree_path: Path, install: bool) -> str:
    if not install:
        return "skipped"

    for lockfile, command in LOCKFILE_COMMANDS:
        if (worktree_path / lockfile).exists():
            try:
                run(command, cwd=worktree_path, check=True)
                return f"installed via {' '.join(command)}"
            except subprocess.CalledProcessError as exc:
                raise CLIError(f"Dependency install failed: {' '.join(command)}\n{exc.stderr}") from exc

    return "no known lockfile found"


def ensure_worktree(repo: Path, branch: str, name: str, base_branch: str) -> Path:
    wt_parent = repo.parent
    wt_path = wt_parent / name

    existing_paths = {Path(e.get("worktree", "")) for e in parse_worktree_list(repo)}
    if wt_path in existing_paths:
        return wt_path

    try:
        run(["git", "show-ref", "--verify", f"refs/heads/{branch}"], cwd=repo)
        run(["git", "worktree", "add", str(wt_path), branch], cwd=repo)
    except subprocess.CalledProcessError:
        try:
            run(["git", "worktree", "add", "-b", branch, str(wt_path), base_branch], cwd=repo)
        except subprocess.CalledProcessError as exc:
            raise CLIError(f"Failed to create worktree: {exc.stderr}") from exc

    return wt_path


def format_text(result: WorktreeResult) -> str:
    lines = [
        "Worktree prepared",
        f"- repo: {result.repo}",
        f"- path: {result.worktree_path}",
        f"- branch: {result.branch}",
        f"- created: {result.created}",
        f"- ports: app={result.ports['app']} db={result.ports['db']} redis={result.ports['redis']}",
        f"- copied env files: {', '.join(result.copied_env_files) if result.copied_env_files else 'none'}",
        f"- dependency install: {result.dependency_install}",
    ]
    return "\n".join(lines)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Create and prepare a git worktree.")
    parser.add_argument("--input", help="Path to JSON input file. If omitted, reads JSON from stdin when piped.")
    parser.add_argument("--repo", default=".", help="Path to repository root (default: current directory).")
    parser.add_argument("--branch", help="Branch name for the worktree.")
    parser.add_argument("--name", help="Worktree directory name (created adjacent to repo).")
    parser.add_argument("--base-branch", default="main", help="Base branch when creating a new branch.")
    parser.add_argument("--app-base", type=int, default=3000, help="Base app port.")
    parser.add_argument("--db-base", type=int, default=5432, help="Base DB port.")
    parser.add_argument("--redis-base", type=int, default=6379, help="Base Redis port.")
    parser.add_argument("--stride", type=int, default=10, help="Port stride between worktrees.")
    parser.add_argument("--install-deps", action="store_true", help="Install dependencies in the new worktree.")
    parser.add_argument("--format", choices=["text", "json"], default="text", help="Output format.")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    payload = load_json_input(args.input)

    repo = Path(str(payload.get("repo", args.repo))).resolve()
    branch = payload.get("branch", args.branch)
    name = payload.get("name", args.name)
    base_branch = str(payload.get("base_branch", args.base_branch))

    app_base = int(payload.get("app_base", args.app_base))
    db_base = int(payload.get("db_base", args.db_base))
    redis_base = int(payload.get("redis_base", args.redis_base))
    stride = int(payload.get("stride", args.stride))
    install_deps = bool(payload.get("install_deps", args.install_deps))

    if not branch or not name:
        raise CLIError("Missing required values: --branch and --name (or provide via JSON input).")

    try:
        run(["git", "rev-parse", "--is-inside-work-tree"], cwd=repo)
    except subprocess.CalledProcessError as exc:
        raise CLIError(f"Not a git repository: {repo}") from exc

    wt_path = ensure_worktree(repo, branch, name, base_branch)
    created = (wt_path / ".worktree-ports.json").exists() is False

    ports = find_next_ports(repo, app_base, db_base, redis_base, stride)
    (wt_path / ".worktree-ports.json").write_text(json.dumps(ports, indent=2), encoding="utf-8")

    copied = sync_env_files(repo, wt_path)
    install_status = install_dependencies_if_requested(wt_path, install_deps)

    result = WorktreeResult(
        repo=str(repo),
        worktree_path=str(wt_path),
        branch=branch,
        created=created,
        ports=ports,
        copied_env_files=copied,
        dependency_install=install_status,
    )

    if args.format == "json":
        print(json.dumps(asdict(result), indent=2))
    else:
        print(format_text(result))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except CLIError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
