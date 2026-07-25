#!/usr/bin/env python3
"""Scan a repo for stale feature flags (Karpathy goal-driven cleanup).

Detects flag identifiers from common code patterns, dates each one by its
introducing commit, and flags items older than --max-age-days that appear in
fewer than --min-uses places as cleanup candidates.
"""
import argparse
import json
import os
import re
import subprocess
import sys
from collections import defaultdict
from datetime import datetime, timezone

FLAG_PATTERNS = [
    re.compile(r'\b(?:isFlagEnabled|isEnabled|featureFlag|getFlag|flag|useFlag|useExperiment)\(\s*["\']([\w.\-:]+)["\']'),
    re.compile(r'\b(?:client|ld|unleash|growthbook|statsig)\.(?:variation|isEnabled|feature|getValue|getExperiment)\(\s*["\']([\w.\-:]+)["\']'),
]

CODE_EXTS = {".py", ".js", ".ts", ".tsx", ".jsx", ".go", ".rb", ".java", ".kt", ".cs", ".rs", ".php"}
SKIP_DIRS = {".git", "node_modules", ".venv", "venv", "dist", "build", "__pycache__", ".next"}


def _walk_code_files(repo):
    for root, dirs, files in os.walk(repo):
        dirs[:] = [d for d in dirs if d not in SKIP_DIRS]
        for f in files:
            if os.path.splitext(f)[1] in CODE_EXTS:
                yield os.path.join(root, f)


def _scan_file(path):
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as f:
            text = f.read()
    except OSError:
        return []
    found = set()
    for pat in FLAG_PATTERNS:
        for m in pat.finditer(text):
            found.add(m.group(1))
    return list(found)


def _first_commit_date(repo, flag_name):
    try:
        out = subprocess.run(
            ["git", "-C", repo, "log", "--diff-filter=A", "--format=%cI", "-S", flag_name],
            capture_output=True, text=True, timeout=10, check=False,
        )
    except (subprocess.SubprocessError, OSError):
        return None
    lines = [ln for ln in out.stdout.strip().split("\n") if ln]
    if not lines:
        return None
    try:
        return datetime.fromisoformat(lines[-1])
    except ValueError:
        return None


def _age_days(when):
    if when is None:
        return None
    now = datetime.now(timezone.utc)
    return (now - when).days


def collect_flags(repo):
    flags_to_paths = defaultdict(list)
    for path in _walk_code_files(repo):
        for name in _scan_file(path):
            flags_to_paths[name].append(os.path.relpath(path, repo))
    return flags_to_paths


def assess(repo, flags_to_paths, max_age_days, min_uses):
    rows = []
    for name in sorted(flags_to_paths.keys()):
        paths = flags_to_paths[name]
        when = _first_commit_date(repo, name)
        age = _age_days(when)
        is_debt = (
            age is not None
            and age > max_age_days
            and len(paths) <= min_uses
        )
        rows.append({
            "flag": name,
            "uses": len(paths),
            "age_days": age,
            "first_seen": when.date().isoformat() if when else None,
            "files": paths[:5],
            "is_debt": is_debt,
        })
    return rows


def render_text(rows, max_age_days):
    debt = [r for r in rows if r["is_debt"]]
    print(f"Flag Debt Scanner — {len(rows)} flags found, {len(debt)} stale (>{max_age_days}d, ≤2 uses)")
    print("")
    if not debt:
        print("No debt detected. Nice.")
        return
    print(f"{'flag':40} {'age':>6}  {'uses':>4}  files")
    print("-" * 80)
    for r in debt:
        files = ", ".join(r["files"][:2]) + ("…" if len(r["files"]) > 2 else "")
        age = f"{r['age_days']}d" if r["age_days"] is not None else "?"
        print(f"{r['flag']:40} {age:>6}  {r['uses']:>4}  {files}")
    print("")
    print("Suggested action: confirm reached 100% (or killed); delete dead branch; remove flag.")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--repo", default=".", help="Path to repo root (default: .)")
    ap.add_argument("--max-age-days", type=int, default=90, help="Flags older than this are debt candidates (default: 90)")
    ap.add_argument("--min-uses", type=int, default=2, help="Flags with ≤ this many uses are debt candidates (default: 2)")
    ap.add_argument("--format", choices=["text", "json"], default="text")
    args = ap.parse_args()

    repo = os.path.abspath(args.repo)
    if not os.path.isdir(os.path.join(repo, ".git")):
        print(f"WARN: {repo} is not a git repo; age detection disabled", file=sys.stderr)

    flags = collect_flags(repo)
    rows = assess(repo, flags, args.max_age_days, args.min_uses)
    if args.format == "json":
        print(json.dumps(rows, indent=2, default=str))
    else:
        render_text(rows, args.max_age_days)
    return 1 if any(r["is_debt"] for r in rows) else 0


if __name__ == "__main__":
    sys.exit(main())
