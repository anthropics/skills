#!/usr/bin/env python3
"""Generate changelog sections from git log or piped commit messages using conventional commit prefixes."""

import argparse
import shutil
import subprocess
import sys
from collections import defaultdict


SECTIONS = {
    "feat": "Features",
    "fix": "Fixes",
    "docs": "Documentation",
    "refactor": "Refactors",
    "test": "Tests",
    "chore": "Chores",
    "perf": "Performance",
    "ci": "CI",
    "build": "Build",
    "style": "Style",
    "revert": "Reverts",
}

DEMO_COMMITS = [
    "feat: add user dashboard with analytics widgets",
    "feat: implement dark mode toggle",
    "fix: resolve crash on empty CSV import",
    "fix: correct timezone offset in calendar view",
    "docs: update API reference for v2 endpoints",
    "refactor: extract shared validation into utils module",
    "chore: bump dependencies to latest patch versions",
    "perf: optimize database queries for user listing",
]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate changelog from git commits or piped input.",
        epilog="Examples:\n"
               "  %(prog)s --from v1.0.0 --to HEAD\n"
               "  git log --pretty=format:%%s v1.0..HEAD | %(prog)s --stdin\n"
               "  %(prog)s --demo\n",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--from", dest="from_ref", default="HEAD~50",
                        help="Start ref for git log (default: HEAD~50)")
    parser.add_argument("--to", dest="to_ref", default="HEAD",
                        help="End ref for git log (default: HEAD)")
    parser.add_argument("--format", choices=["markdown", "text"], default="markdown",
                        help="Output format (default: markdown)")
    parser.add_argument("--stdin", action="store_true",
                        help="Read commit subjects from stdin instead of git log")
    parser.add_argument("--demo", action="store_true",
                        help="Run with sample data (no git required)")
    return parser.parse_args()


def get_git_log(from_ref: str, to_ref: str) -> list[str]:
    """Get commit subjects from git log. Requires git on PATH and a git repo."""
    if not shutil.which("git"):
        print("Error: git not found on PATH. Use --stdin or --demo instead.", file=sys.stderr)
        sys.exit(1)
    commit_range = f"{from_ref}..{to_ref}"
    cmd = ["git", "log", "--pretty=format:%s", commit_range]
    try:
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=30)
    except subprocess.TimeoutExpired:
        print("Error: git log timed out.", file=sys.stderr)
        sys.exit(1)
    if result.returncode != 0:
        print(f"Error: git log failed: {result.stderr.strip()}", file=sys.stderr)
        sys.exit(1)
    lines = [line.strip() for line in result.stdout.splitlines() if line.strip()]
    return lines


def read_stdin() -> list[str]:
    """Read commit subjects from stdin, one per line."""
    return [line.strip() for line in sys.stdin if line.strip()]


def group_commits(subjects: list[str]) -> dict[str, list[str]]:
    grouped: dict[str, list[str]] = defaultdict(list)

    for subject in subjects:
        commit_type = "other"
        for prefix in SECTIONS:
            if subject.startswith(f"{prefix}:") or subject.startswith(f"{prefix}("):
                commit_type = prefix
                break
        grouped[commit_type].append(subject)

    return grouped


def render_markdown(grouped: dict[str, list[str]]) -> str:
    out = ["# Changelog", ""]
    ordered_types = list(SECTIONS.keys()) + ["other"]
    for commit_type in ordered_types:
        commits = grouped.get(commit_type, [])
        if not commits:
            continue
        header = SECTIONS.get(commit_type, "Other")
        out.append(f"## {header}")
        for item in commits:
            out.append(f"- {item}")
        out.append("")
    return "\n".join(out).rstrip() + "\n"


def render_text(grouped: dict[str, list[str]]) -> str:
    out: list[str] = []
    ordered_types = list(SECTIONS.keys()) + ["other"]
    for commit_type in ordered_types:
        commits = grouped.get(commit_type, [])
        if not commits:
            continue
        header = SECTIONS.get(commit_type, "Other")
        out.append(header.upper())
        for item in commits:
            out.append(f"* {item}")
        out.append("")
    return "\n".join(out).rstrip() + "\n"


def main() -> int:
    args = parse_args()

    if args.demo:
        subjects = DEMO_COMMITS
    elif args.stdin:
        subjects = read_stdin()
    else:
        subjects = get_git_log(args.from_ref, args.to_ref)

    if not subjects:
        print("No commits found.", file=sys.stderr)
        return 0

    grouped = group_commits(subjects)

    if args.format == "markdown":
        print(render_markdown(grouped), end="")
    else:
        print(render_text(grouped), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
