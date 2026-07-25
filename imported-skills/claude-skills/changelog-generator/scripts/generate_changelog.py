#!/usr/bin/env python3
"""Generate changelog entries from Conventional Commits.

Input sources (priority order):
1) --input file with one commit subject per line
2) stdin commit subjects
3) git log from --from-tag/--to-tag or --from-ref/--to-ref

Outputs markdown or JSON and can prepend into CHANGELOG.md.
"""

import argparse
import json
import re
import subprocess
import sys
from dataclasses import dataclass, asdict, field
from datetime import date
from pathlib import Path
from typing import Dict, List, Optional


COMMIT_RE = re.compile(
    r"^(?P<type>feat|fix|perf|refactor|docs|test|build|ci|chore|security|deprecated|remove)"
    r"(?:\((?P<scope>[^)]+)\))?(?P<breaking>!)?:\s+(?P<summary>.+)$"
)

SECTION_MAP = {
    "feat": "Added",
    "fix": "Fixed",
    "perf": "Changed",
    "refactor": "Changed",
    "security": "Security",
    "deprecated": "Deprecated",
    "remove": "Removed",
}


class CLIError(Exception):
    """Raised for expected CLI failures."""


@dataclass
class ParsedCommit:
    raw: str
    ctype: str
    scope: Optional[str]
    summary: str
    breaking: bool


@dataclass
class ChangelogEntry:
    version: str
    release_date: str
    sections: Dict[str, List[str]] = field(default_factory=dict)
    breaking_changes: List[str] = field(default_factory=list)
    bump: str = "patch"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate changelog from conventional commits.")
    parser.add_argument("--input", help="Text file with one commit subject per line.")
    parser.add_argument("--from-tag", help="Git tag start (exclusive).")
    parser.add_argument("--to-tag", help="Git tag end (inclusive).")
    parser.add_argument("--from-ref", help="Git ref start (exclusive).")
    parser.add_argument("--to-ref", help="Git ref end (inclusive).")
    parser.add_argument("--next-version", default="Unreleased", help="Version label for the generated entry.")
    parser.add_argument("--date", dest="entry_date", default=str(date.today()), help="Release date (YYYY-MM-DD).")
    parser.add_argument("--format", choices=["markdown", "json"], default="markdown", help="Output format.")
    parser.add_argument("--write", help="Prepend generated markdown entry into this changelog file.")
    return parser.parse_args()


def read_lines_from_file(path: str) -> List[str]:
    try:
        return [line.strip() for line in Path(path).read_text(encoding="utf-8").splitlines() if line.strip()]
    except Exception as exc:
        raise CLIError(f"Failed reading --input file: {exc}") from exc


def read_lines_from_stdin() -> List[str]:
    if sys.stdin.isatty():
        return []
    payload = sys.stdin.read()
    return [line.strip() for line in payload.splitlines() if line.strip()]


def read_lines_from_git(args: argparse.Namespace) -> List[str]:
    if args.from_tag or args.to_tag:
        if not args.to_tag:
            raise CLIError("--to-tag is required when using tag range.")
        start = args.from_tag
        end = args.to_tag
    elif args.from_ref or args.to_ref:
        if not args.to_ref:
            raise CLIError("--to-ref is required when using ref range.")
        start = args.from_ref
        end = args.to_ref
    else:
        return []

    range_spec = f"{start}..{end}" if start else end
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


def load_commits(args: argparse.Namespace) -> List[str]:
    if args.input:
        return read_lines_from_file(args.input)

    stdin_lines = read_lines_from_stdin()
    if stdin_lines:
        return stdin_lines

    git_lines = read_lines_from_git(args)
    if git_lines:
        return git_lines

    raise CLIError("No commit input found. Use --input, stdin, or git range flags.")


def parse_commits(lines: List[str]) -> List[ParsedCommit]:
    parsed: List[ParsedCommit] = []
    for line in lines:
        match = COMMIT_RE.match(line)
        if not match:
            continue
        ctype = match.group("type")
        scope = match.group("scope")
        summary = match.group("summary")
        breaking = bool(match.group("breaking")) or "BREAKING CHANGE" in line
        parsed.append(ParsedCommit(raw=line, ctype=ctype, scope=scope, summary=summary, breaking=breaking))
    return parsed


def determine_bump(commits: List[ParsedCommit]) -> str:
    if any(c.breaking for c in commits):
        return "major"
    if any(c.ctype == "feat" for c in commits):
        return "minor"
    return "patch"


def build_entry(commits: List[ParsedCommit], version: str, entry_date: str) -> ChangelogEntry:
    sections: Dict[str, List[str]] = {
        "Security": [],
        "Added": [],
        "Changed": [],
        "Deprecated": [],
        "Removed": [],
        "Fixed": [],
    }
    breaking_changes: List[str] = []

    for commit in commits:
        if commit.breaking:
            breaking_changes.append(commit.summary)
        section = SECTION_MAP.get(commit.ctype)
        if section:
            line = commit.summary if not commit.scope else f"{commit.scope}: {commit.summary}"
            sections[section].append(line)

    sections = {k: v for k, v in sections.items() if v}
    return ChangelogEntry(
        version=version,
        release_date=entry_date,
        sections=sections,
        breaking_changes=breaking_changes,
        bump=determine_bump(commits),
    )


def render_markdown(entry: ChangelogEntry) -> str:
    lines = [f"## [{entry.version}] - {entry.release_date}", ""]
    if entry.breaking_changes:
        lines.append("### Breaking")
        lines.extend([f"- {item}" for item in entry.breaking_changes])
        lines.append("")

    ordered_sections = ["Security", "Added", "Changed", "Deprecated", "Removed", "Fixed"]
    for section in ordered_sections:
        items = entry.sections.get(section, [])
        if not items:
            continue
        lines.append(f"### {section}")
        lines.extend([f"- {item}" for item in items])
        lines.append("")

    lines.append(f"<!-- recommended-semver-bump: {entry.bump} -->")
    return "\n".join(lines).strip() + "\n"


def prepend_changelog(path: Path, entry_md: str) -> None:
    if path.exists():
        original = path.read_text(encoding="utf-8")
    else:
        original = "# Changelog\n\nAll notable changes to this project will be documented in this file.\n\n"

    if original.startswith("# Changelog"):
        first_break = original.find("\n")
        head = original[: first_break + 1]
        tail = original[first_break + 1 :].lstrip("\n")
        combined = f"{head}\n{entry_md}\n{tail}"
    else:
        combined = f"# Changelog\n\n{entry_md}\n{original}"
    path.write_text(combined, encoding="utf-8")


def main() -> int:
    args = parse_args()
    lines = load_commits(args)
    parsed = parse_commits(lines)
    if not parsed:
        raise CLIError("No valid conventional commit messages found in input.")

    entry = build_entry(parsed, args.next_version, args.entry_date)

    if args.format == "json":
        print(json.dumps(asdict(entry), indent=2))
    else:
        markdown = render_markdown(entry)
        print(markdown, end="")
        if args.write:
            prepend_changelog(Path(args.write), markdown)

    if args.format == "json" and args.write:
        prepend_changelog(Path(args.write), render_markdown(entry))

    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except CLIError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
