#!/usr/bin/env python3
"""artifact_deduplicator.py — Detect content in a handoff draft that should be referenced not duplicated.

Stdlib-only. Scans a handoff markdown draft for content patterns that look like
duplicated artifact content (PRD-style, plan-style, ADR-style, commit-message-style,
issue-style). Reports candidates for replacement with path/URL references.

Detection signals:
  - PRD/plan headers ("Problem statement", "Solution", "Success metrics", "Out of scope")
  - ADR template fields ("Decision", "Consequences", "Status: Accepted")
  - Commit-message style (Conventional Commit prefix + multi-line body)
  - Issue-style fields ("Steps to reproduce", "Expected behavior", "Actual behavior")
  - Long code blocks (>20 lines) that look like checked-in code

For each detection: report location + suggested replacement ("Replace with link to PRD-path.md").

NO LLM CALLS. Pure pattern matching.

Usage:
    python artifact_deduplicator.py                              # uses embedded sample
    python artifact_deduplicator.py path/to/handoff-draft.md
    python artifact_deduplicator.py handoff.md --output json
"""

import argparse
import json
import re
import sys
from typing import Any, Dict, List, Optional


PRD_HEADERS = ["problem statement", "solution", "success metrics", "out of scope", "user stories", "acceptance criteria"]
ADR_FIELDS = ["status:", "decision:", "consequences:", "context:", "alternatives considered"]
ISSUE_FIELDS = ["steps to reproduce", "expected behavior", "actual behavior", "environment:", "labels:"]
COMMIT_PREFIXES = ["feat:", "fix:", "docs:", "chore:", "refactor:", "test:", "ci:", "build:", "perf:"]


def _make_finding(line_no: int, kind: str, trigger: str, context: str, suggestion: str) -> Dict[str, Any]:
    return {
        "line": line_no,
        "kind": kind,
        "trigger": trigger,
        "context": context[:120],
        "suggestion": suggestion,
    }


_PRD_SUGGESTION = "Replace this section with a link to the canonical PRD file (e.g., `[Full PRD](path/to/prd.md)`)."
_ADR_SUGGESTION = "Replace with a link to the ADR file (e.g., `[ADR-NNNN](docs/adr/NNNN.md)`)."
_ISSUE_SUGGESTION = "Replace with issue reference (e.g., `#NNN` or full URL)."
_COMMIT_SUGGESTION = "Replace with commit SHA + URL (e.g., `[abc1234](https://github.com/.../commit/abc1234)`)."


def _match_header_in_line(line: str, line_no: int, header: str, kind: str, suggestion: str) -> Optional[Dict[str, Any]]:
    if header in line.lower() and ("#" in line or ":" in line):
        return _make_finding(line_no, kind, header, line.strip(), suggestion)
    return None


def _match_field_in_line(line: str, line_no: int, field: str, kind: str, suggestion: str) -> Optional[Dict[str, Any]]:
    if field in line.lower():
        return _make_finding(line_no, kind, field, line.strip(), suggestion)
    return None


def find_prd_content(text: str) -> List[Dict[str, Any]]:
    findings: List[Dict[str, Any]] = []
    for line_no, line in enumerate(text.splitlines(), start=1):
        for header in PRD_HEADERS:
            f = _match_header_in_line(line, line_no, header, "prd_content", _PRD_SUGGESTION)
            if f:
                findings.append(f)
                break
    return findings


def find_adr_content(text: str) -> List[Dict[str, Any]]:
    findings: List[Dict[str, Any]] = []
    for line_no, line in enumerate(text.splitlines(), start=1):
        for field in ADR_FIELDS:
            f = _match_field_in_line(line, line_no, field, "adr_content", _ADR_SUGGESTION)
            if f:
                findings.append(f)
                break
    return findings


def find_issue_content(text: str) -> List[Dict[str, Any]]:
    findings: List[Dict[str, Any]] = []
    for line_no, line in enumerate(text.splitlines(), start=1):
        for field in ISSUE_FIELDS:
            f = _match_field_in_line(line, line_no, field, "issue_content", _ISSUE_SUGGESTION)
            if f:
                findings.append(f)
                break
    return findings


def find_commit_style(text: str) -> List[Dict[str, Any]]:
    findings: List[Dict[str, Any]] = []
    for line_no, line in enumerate(text.splitlines(), start=1):
        stripped = line.strip().lower()
        for prefix in COMMIT_PREFIXES:
            if stripped.startswith(prefix):
                findings.append(_make_finding(line_no, "commit_style", prefix, line.strip(), _COMMIT_SUGGESTION))
                break
    return findings


_LONG_CODE_SUGGESTION = (
    "Long code blocks usually duplicate checked-in code. Replace with file path + commit SHA "
    "(e.g., `[src/foo.py:42-80](https://github.com/.../blob/SHA/src/foo.py#L42-L80)`)."
)


def _record_long_block(block_start: int, end_line: int, block_lines: int) -> Dict[str, Any]:
    return _make_finding(
        line_no=block_start,
        kind="long_code_block",
        trigger=f"{block_lines} lines",
        context=f"Code block L{block_start}-L{end_line}",
        suggestion=_LONG_CODE_SUGGESTION,
    )


def find_long_code_blocks(text: str, threshold: int = 20) -> List[Dict[str, Any]]:
    findings: List[Dict[str, Any]] = []
    in_block = False
    block_start = 0
    block_lines = 0
    for line_no, line in enumerate(text.splitlines(), start=1):
        is_fence = line.strip().startswith("```")
        if is_fence and in_block:
            if block_lines > threshold:
                findings.append(_record_long_block(block_start, line_no, block_lines))
            in_block = False
            block_lines = 0
        elif is_fence:
            in_block = True
            block_start = line_no
            block_lines = 0
        elif in_block:
            block_lines += 1
    return findings


def analyze(text: str) -> Dict[str, Any]:
    all_findings = (
        find_prd_content(text)
        + find_adr_content(text)
        + find_issue_content(text)
        + find_commit_style(text)
        + find_long_code_blocks(text)
    )
    by_kind: Dict[str, int] = {}
    for f in all_findings:
        by_kind[f["kind"]] = by_kind.get(f["kind"], 0) + 1
    verdict = "CLEAN" if not all_findings else ("WARN" if len(all_findings) <= 3 else "FAIL")
    return {
        "total_findings": len(all_findings),
        "by_kind": by_kind,
        "findings": all_findings,
        "verdict": verdict,
    }


def render_text(r: Dict[str, Any]) -> str:
    lines = []
    lines.append("=" * 72)
    lines.append("HANDOFF ARTIFACT DEDUPLICATOR (per Matt Pocock's no-duplication rule)")
    lines.append("=" * 72)
    lines.append("")
    lines.append(f"Total findings: {r['total_findings']}")
    lines.append(f"By kind: {r['by_kind']}")
    lines.append("")
    lines.append("-" * 72)
    if not r["findings"]:
        lines.append("No duplicated artifact content detected. Good handoff hygiene.")
    else:
        for f in r["findings"]:
            lines.append(f"  L{f['line']:>4d} [{f['kind']:18s}] '{f['trigger']}'")
            lines.append(f"        Context: {f['context']}")
            lines.append(f"        Suggestion: {f['suggestion']}")
            lines.append("")
    lines.append("-" * 72)
    lines.append(f"Verdict: {r['verdict']}")
    return "\n".join(lines)


SAMPLE_HANDOFF_BAD = """# Handoff

## Problem statement
Users complain about slow auth. We need to make it fast.

## Solution
Implement OAuth2 with refresh tokens.

## Status: Accepted

Decision: Use Auth0 over Okta.
Consequences: $200/month cost; faster integration.

## Steps to reproduce the bug
1. Login
2. Wait 10 seconds
3. Re-login

feat: add OAuth2 support
This change adds OAuth2 to the auth middleware.
- Added refresh token handling
- Added expiry check
"""


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Detect duplicated artifact content in a handoff draft.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("path", nargs="?", help="Path to handoff markdown (uses embedded sample if omitted)")
    parser.add_argument("--output", choices=("text", "json"), default="text", help="Output format")
    args = parser.parse_args()

    if args.path:
        try:
            with open(args.path, "r", encoding="utf-8") as f:
                text = f.read()
        except (IOError, OSError) as e:
            print(f"error: {e}", file=sys.stderr)
            return 1
    else:
        text = SAMPLE_HANDOFF_BAD

    result = analyze(text)
    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_text(result))
    return 0 if result["verdict"] == "CLEAN" else 1


if __name__ == "__main__":
    sys.exit(main())
