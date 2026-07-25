#!/usr/bin/env python3
"""Self-check for handoff drafts — operationalizes handoff_prompt.md.

Reads a draft handoff and flags fidelity issues the agent might have
left behind when free-handing the summary. Complements the redaction
linter (which finds secrets) by finding structural / fidelity gaps.

Checks:
  1. All 5 sections present (Goal, State, Decisions, Skills, Artifacts).
  2. Goal section is not empty / placeholder.
  3. State of play has at least one Done or In-flight bullet that
     references an artifact (commit hash, PR/issue number, or path).
  4. Open decisions: if the git repo has uncommitted changes or recent
     commits, expect at least one decision OR an explicit "- None.".
  5. Skills to use: 3-5 entries, each with a one-line "why".
  6. Artifacts: every bullet looks like a path or URL, no inline bodies.

Exit codes:
  0 — clean (or warn mode with findings)
  1 — findings in strict mode (default)
  2 — usage / IO error

Stdlib-only.
"""

import argparse
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

SECTION_HEADERS = [
    "Goal of next session",
    "State of play",
    "Open decisions",
    "Skills to use",
    "Artifacts",
]

PLACEHOLDER_PATTERNS = [
    r"_<!--.*-->_",
    r"<!--.*-->",
    r"^\s*\.\.\.\s*$",
    r"^\s*TODO\s*$",
    r"^\s*\?\?\?\s*$",
]

ARTIFACT_HINTS = re.compile(
    r"(\b[a-f0-9]{7,40}\b"             # git commit hash
    r"|#\d+"                            # PR/issue number
    r"|\bPR\s+\d+\b|\bissue\s+\d+\b"
    r"|https?://"
    r"|\b[\w./-]+\.(?:py|md|ts|tsx|js|jsx|json|yaml|yml|toml|sql|sh)\b"
    r"|`[^`]+\.[a-z]+`"
    r")",
    re.IGNORECASE,
)

URL_OR_PATH = re.compile(
    r"^[\s\-*]*"
    r"(?:[A-Za-z][\w\s-]{0,30}:\s*)?"   # optional label like "PR:" or "Branch:"
    r"(?:https?://\S+|[\w./-]+\.\w+|`[^`]+`|/[\w./-]+|\S+/\S+)",
    re.IGNORECASE,
)


@dataclass
class Finding:
    severity: str  # high | medium | low
    code: str
    message: str
    suggestion: str
    line_hint: int | None = None


@dataclass
class Report:
    findings: list[Finding] = field(default_factory=list)

    def add(self, severity: str, code: str, message: str, suggestion: str, line: int | None = None) -> None:
        self.findings.append(Finding(severity, code, message, suggestion, line))

    def by_severity(self) -> dict[str, int]:
        counts = {"high": 0, "medium": 0, "low": 0}
        for f in self.findings:
            counts[f.severity] = counts.get(f.severity, 0) + 1
        return counts


def _strip_frontmatter(text: str) -> str:
    if not text.startswith("---"):
        return text
    end = text.find("\n---", 3)
    if end == -1:
        return text
    return text[end + 4:].lstrip("\n")


def _split_sections(text: str) -> dict[str, str]:
    body = _strip_frontmatter(text)
    sections: dict[str, str] = {}
    current_header: str | None = None
    current_lines: list[str] = []
    for line in body.splitlines():
        m = re.match(r"^##\s+(.+?)\s*$", line)
        if m:
            if current_header is not None:
                sections[current_header] = "\n".join(current_lines).strip()
            current_header = m.group(1).strip()
            current_lines = []
        else:
            if current_header is not None:
                current_lines.append(line)
    if current_header is not None:
        sections[current_header] = "\n".join(current_lines).strip()
    return sections


def _is_placeholder(text: str) -> bool:
    stripped = text.strip()
    if not stripped:
        return True
    for pattern in PLACEHOLDER_PATTERNS:
        if re.fullmatch(pattern, stripped, re.IGNORECASE):
            return True
    # Section content that is ONLY placeholder comment(s)
    non_placeholder = re.sub(r"_?<!--.*?-->_?", "", stripped, flags=re.DOTALL).strip()
    return not non_placeholder


def _bullet_lines(section: str) -> list[str]:
    out = []
    for line in section.splitlines():
        line = line.rstrip()
        if re.match(r"^\s*[-*+]\s+", line):
            out.append(line)
    return out


def _git_state(cwd: Path) -> dict[str, int]:
    state = {"dirty": 0, "recent_commits": 0, "in_repo": 0}

    def run(cmd: list[str]) -> str | None:
        try:
            r = subprocess.run(
                cmd, cwd=str(cwd), check=False,
                capture_output=True, text=True, timeout=5,
            )
        except (OSError, subprocess.SubprocessError):
            return None
        return r.stdout if r.returncode == 0 else None

    if run(["git", "rev-parse", "--is-inside-work-tree"]):
        state["in_repo"] = 1
        status = run(["git", "status", "--porcelain"]) or ""
        state["dirty"] = sum(1 for ln in status.splitlines() if ln.strip())
        log = run(["git", "log", "--since=1.day.ago", "--oneline"]) or ""
        state["recent_commits"] = sum(1 for ln in log.splitlines() if ln.strip())
    return state


def check(text: str, cwd: Path | None = None) -> Report:
    report = Report()
    sections = _split_sections(text)

    # Check 1: all 5 sections present
    for header in SECTION_HEADERS:
        if header not in sections:
            report.add(
                "high", "MISSING_SECTION",
                f"Section missing: '## {header}'",
                f"Add a `## {header}` section. See references/handoff_structure.md.",
            )

    # Check 2: Goal section is not empty/placeholder
    goal = sections.get("Goal of next session", "")
    if _is_placeholder(goal):
        report.add(
            "high", "EMPTY_GOAL",
            "Goal section is empty or placeholder text.",
            "Write one sentence describing what the next session must accomplish.",
        )

    # Check 3: State of play references an artifact
    state_text = sections.get("State of play", "")
    if _is_placeholder(state_text):
        report.add(
            "high", "EMPTY_STATE",
            "State of play is empty or placeholder text.",
            "List what's done/in-flight/blocked. Each bullet references a commit, PR, file path, or issue.",
        )
    else:
        bullets = _bullet_lines(state_text)
        substantive = [b for b in bullets if not _is_placeholder(b)]
        with_artifact = [b for b in substantive if ARTIFACT_HINTS.search(b)]
        if substantive and not with_artifact:
            report.add(
                "high", "STATE_NO_ARTIFACT",
                "State of play bullets do not reference any artifact (commit hash, PR/issue number, file path).",
                "For every bullet, name the artifact that proves it. See handoff_prompt.md Step 2.",
            )

    # Check 4: Open decisions vs git context
    decisions_text = sections.get("Open decisions", "")
    has_decisions = (
        not _is_placeholder(decisions_text)
        and "none." not in decisions_text.lower()[:30]
    )
    if cwd is not None:
        gs = _git_state(cwd)
        if gs["in_repo"] and (gs["dirty"] > 0 or gs["recent_commits"] > 1) and not has_decisions:
            report.add(
                "medium", "MISSING_DECISIONS",
                f"Repo has {gs['dirty']} dirty file(s) and {gs['recent_commits']} commit(s) today, but Open decisions is empty.",
                "Either list the decisions that surfaced during this work, or write '- None.' explicitly.",
            )

    # Check 5: Skills to use — 3 to 5 entries
    skills_text = sections.get("Skills to use", "")
    skill_bullets = _bullet_lines(skills_text)
    substantive_skills = [b for b in skill_bullets if not _is_placeholder(b)]
    n = len(substantive_skills)
    if n == 0:
        report.add(
            "medium", "NO_SKILLS",
            "Skills to use section has no entries.",
            "Run scripts/skill_recommender.py and pick 3-5 skills. Each with a one-line 'why'.",
        )
    elif n > 5:
        report.add(
            "medium", "TOO_MANY_SKILLS",
            f"{n} skills listed. Hard cap is 5.",
            "Trim to the 3-5 skills the next session actually needs. See handoff_prompt.md Step 4.",
        )
    elif n < 3:
        report.add(
            "low", "FEW_SKILLS",
            f"Only {n} skill(s) listed. Minimum recommended is 3.",
            "Consider adding a review or verifier skill.",
        )
    # Each skill should have a 'why' (em-dash or hyphen + explanation)
    for b in substantive_skills:
        if not re.search(r"[-—–]\s+\S+", b.split("**", 2)[-1] if "**" in b else b):
            report.add(
                "low", "SKILL_NO_WHY",
                f"Skill bullet has no '— why' explanation: {b.strip()[:60]}",
                "Format: `- skill-name — one-line why this session needs it`",
            )
            break  # only flag once

    # Check 6: Artifacts — only paths/URLs, no inline bodies
    artifacts_text = sections.get("Artifacts", "")
    if not _is_placeholder(artifacts_text):
        artifact_bullets = _bullet_lines(artifacts_text)
        for line in artifact_bullets:
            if _is_placeholder(line):
                continue
            # If bullet is very long (>200 chars) it likely embeds content
            if len(line) > 200:
                report.add(
                    "medium", "ARTIFACT_INLINE_BODY",
                    f"Artifact bullet is suspiciously long ({len(line)} chars) — likely embedded content.",
                    "Replace inline content with a path/URL. See deduplication_discipline.md.",
                )
                break

    return report


def _format_human(report: Report, mode: str, path: Path) -> str:
    if not report.findings:
        return f"OK: handoff passes self-check ({path})."
    lines = [f"Found {len(report.findings)} fidelity issue(s) in {path}:", ""]
    for f in report.findings:
        lines.append(f"  [{f.severity}] {f.code}: {f.message}")
        lines.append(f"    fix: {f.suggestion}")
        lines.append("")
    counts = report.by_severity()
    lines.append(f"Severity counts: high={counts['high']} medium={counts['medium']} low={counts['low']}")
    if mode == "strict":
        lines.append("Mode: STRICT — save is blocked until findings are resolved.")
    else:
        lines.append("Mode: WARN — save proceeds; review findings before sharing.")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Self-check a handoff draft for fidelity issues.",
        epilog="Pairs with redaction_linter.py: this finds structural gaps, that finds secrets.",
    )
    parser.add_argument("file", nargs="?", help="Path to the handoff markdown file.")
    parser.add_argument(
        "--mode",
        choices=["strict", "warn"],
        default="strict",
        help="strict: exit 1 on high-severity findings; warn: always exit 0.",
    )
    parser.add_argument("--json", action="store_true", help="Emit JSON instead of human output.")
    parser.add_argument("--sample", action="store_true", help="Run against a built-in bad fixture and exit.")
    parser.add_argument(
        "--no-git", action="store_true",
        help="Skip git context probing (Check 4 becomes a no-op).",
    )
    args = parser.parse_args(argv)

    if args.sample:
        fixture = """---
goal: ""
---

# Handoff

## Goal of next session

_<!-- one sentence: what the next session must accomplish -->_

## State of play

- Done: implemented the feature
- In flight: testing
- Blocked: nothing

## Open decisions

_<!-- What must the next agent decide before continuing? -->_

## Skills to use

- code-review
- handoff
- security-scan
- update-docs
- skill-tester
- review
- something-else

## Artifacts

- _<!-- e.g. PR: https://github.com/org/repo/pull/123 -->_
"""
        report = check(fixture, cwd=None)
        if args.json:
            print(json.dumps({
                "findings": [
                    {"severity": f.severity, "code": f.code, "message": f.message, "suggestion": f.suggestion}
                    for f in report.findings
                ],
                "counts": report.by_severity(),
            }, indent=2))
        else:
            print(_format_human(report, args.mode, Path("<sample>")))
        return 1 if report.findings and args.mode == "strict" else 0

    if not args.file:
        parser.error("file is required unless --sample is used.")

    path = Path(args.file)
    if not path.exists():
        print(f"File not found: {path}", file=sys.stderr)
        return 2

    try:
        text = path.read_text(encoding="utf-8")
    except OSError as exc:
        print(f"Error reading {path}: {exc}", file=sys.stderr)
        return 2

    cwd = None if args.no_git else Path.cwd()
    report = check(text, cwd=cwd)

    if args.json:
        print(json.dumps({
            "file": str(path),
            "mode": args.mode,
            "findings": [
                {"severity": f.severity, "code": f.code, "message": f.message, "suggestion": f.suggestion}
                for f in report.findings
            ],
            "counts": report.by_severity(),
        }, indent=2))
    else:
        print(_format_human(report, args.mode, path))

    if not report.findings:
        return 0
    if args.mode == "strict":
        return 1 if any(f.severity == "high" for f in report.findings) else 0
    return 0


if __name__ == "__main__":
    sys.exit(main())
