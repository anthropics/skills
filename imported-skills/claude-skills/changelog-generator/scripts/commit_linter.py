#!/usr/bin/env python3
"""Lint commit messages against Conventional Commits.

Input sources (priority order):
1) --input file (one commit subject per line)
2) stdin lines
3) git range via --from-ref/--to-ref

Use --strict for non-zero exit on violations.
"""

import argparse
import json
import re
import subprocess
import sys
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import List, Optional


CONVENTIONAL_RE = re.compile(
    r"^(feat|fix|perf|refactor|docs|test|build|ci|chore|security|deprecated|remove)"
    r"(\([a-z0-9._/-]+\))?(!)?:\s+.{1,120}$"
)


class CLIError(Exception):
    """Raised for expected CLI errors."""


@dataclass
class LintReport:
    total: int
    valid: int
    invalid: int
    violations: List[str]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Validate conventional commit subjects.")
    parser.add_argument("--input", help="File with commit subjects (one per line).")
    parser.add_argument("--from-ref", help="Git ref start (exclusive).")
    parser.add_argument("--to-ref", help="Git ref end (inclusive).")
    parser.add_argument("--strict", action="store_true", help="Exit non-zero when violations exist.")
    parser.add_argument("--format", choices=["text", "json"], default="text", help="Output format.")
    return parser.parse_args()


def lines_from_file(path: str) -> List[str]:
    try:
        return [line.strip() for line in Path(path).read_text(encoding="utf-8").splitlines() if line.strip()]
    except Exception as exc:
        raise CLIError(f"Failed reading --input file: {exc}") from exc


def lines_from_stdin() -> List[str]:
    if sys.stdin.isatty():
        return []
    data = sys.stdin.read()
    return [line.strip() for line in data.splitlines() if line.strip()]


def lines_from_git(args: argparse.Namespace) -> List[str]:
    if not args.to_ref:
        return []
    range_spec = f"{args.from_ref}..{args.to_ref}" if args.from_ref else args.to_ref
    try:
        proc = subprocess.run(
            ["git", "log", range_spec, "--pretty=format:%s", "--no-merges"],
            text=True,
            capture_output=True,
            check=True,
        )
    except subprocess.CalledProcessError as exc:
        raise CLIError(f"git log failed for range '{range_spec}': {exc.stderr.strip()}") from exc
    return [line.strip() for line in proc.stdout.splitlines() if line.strip()]


def load_lines(args: argparse.Namespace) -> List[str]:
    if args.input:
        return lines_from_file(args.input)
    stdin_lines = lines_from_stdin()
    if stdin_lines:
        return stdin_lines
    git_lines = lines_from_git(args)
    if git_lines:
        return git_lines
    raise CLIError("No commit input found. Use --input, stdin, or --to-ref.")


def lint(lines: List[str]) -> LintReport:
    violations: List[str] = []
    valid = 0

    for idx, line in enumerate(lines, start=1):
        if CONVENTIONAL_RE.match(line):
            valid += 1
            continue
        violations.append(f"line {idx}: {line}")

    return LintReport(total=len(lines), valid=valid, invalid=len(violations), violations=violations)


def format_text(report: LintReport) -> str:
    lines = [
        "Conventional commit lint report",
        f"- total: {report.total}",
        f"- valid: {report.valid}",
        f"- invalid: {report.invalid}",
    ]
    if report.violations:
        lines.append("Violations:")
        lines.extend([f"- {v}" for v in report.violations])
    return "\n".join(lines)


def main() -> int:
    args = parse_args()
    lines = load_lines(args)
    report = lint(lines)

    if args.format == "json":
        print(json.dumps(asdict(report), indent=2))
    else:
        print(format_text(report))

    if args.strict and report.invalid > 0:
        return 1
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except CLIError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
