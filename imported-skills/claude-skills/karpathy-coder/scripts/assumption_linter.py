#!/usr/bin/env python3
"""
assumption_linter.py — Detect hidden assumptions in a plan or proposal.

Karpathy Principle #1 (Think Before Coding): "State your assumptions
explicitly. If uncertain, ask. If multiple interpretations exist, present
them — don't pick silently."

Reads a markdown plan (or stdin) and flags:
  - Phrases that indicate silent choices ("I'll just...", "Obviously...", "Simply...")
  - Missing scope boundaries ("export" without specifying what/who/how)
  - Format/location assumptions without explicit mention
  - Single-interpretation language for ambiguous requirements
  - Missing error/edge-case consideration

Usage:
    python assumption_linter.py plan.md
    echo "I'll add a function to export user data" | python assumption_linter.py -
    python assumption_linter.py plan.md --json

This is a heuristic tool, not a proof engine. False positives are expected;
the point is to trigger a conversation about assumptions.
"""
from __future__ import annotations
import argparse
import json
import re
import sys
from pathlib import Path

# --- Pattern library ---

ASSUMPTION_SIGNALS = [
    (re.compile(r"\b(?:I'll just|let me just|we can just|just)\b", re.I),
     "assumption-just", "'just' often hides complexity. What's being skipped?"),
    (re.compile(r"\b(?:obviously|clearly|of course|naturally)\b", re.I),
     "assumption-obvious", "Signals an unstated assumption. Is it really obvious?"),
    (re.compile(r"\b(?:simply|straightforward|trivial|easy)\b", re.I),
     "assumption-simple", "Minimizing language. Could be hiding real complexity."),
    (re.compile(r"\b(?:should be fine|should work|shouldn't be a problem)\b", re.I),
     "assumption-hopeful", "Hopeful rather than verified. How will you confirm?"),
    (re.compile(r"\b(?:I assume|assuming|I'm guessing|probably)\b", re.I),
     "assumption-explicit", "At least it's explicit — but have you verified?"),
    (re.compile(r"\b(?:all users|every|everything|always|never)\b", re.I),
     "scope-absolute", "Absolute scope. Is that really the case?"),
]

MISSING_CLARIFICATION = [
    (re.compile(r"\b(?:export|import|save|load|fetch|send)\b.*\b(?:data|file|users)\b", re.I),
     "missing-format", "Export/save/fetch mentioned but format not specified (JSON? CSV? API?)"),
    (re.compile(r"\b(?:fix|improve|optimize|refactor|update)\b", re.I),
     "vague-action", "Vague action verb. What specifically changes? What's the measurable improvement?"),
    (re.compile(r"\b(?:handle|deal with|take care of)\b.*\b(?:error|edge|case)\b", re.I),
     "vague-error-handling", "Error handling mentioned vaguely. Which errors? What behavior?"),
    (re.compile(r"\b(?:the user|users)\b(?!.*\b(?:who|which|specific|certain|admin|role)\b)", re.I),
     "unscoped-user", "Which user(s)? All? Specific role? Authenticated only?"),
]

NO_VERIFICATION = [
    (re.compile(r"^(?:(?!(?:test|verify|check|assert|confirm|ensure|validate)).)*$", re.I),
     "no-verification", "No verification step found in this block. How will you know it works?"),
]


def lint_text(text, source_name="stdin"):
    """Lint a plan text. Return list of findings."""
    findings = []
    lines = text.splitlines()

    for i, line in enumerate(lines, 1):
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue

        for pattern, category, message in ASSUMPTION_SIGNALS:
            for m in pattern.finditer(stripped):
                findings.append({
                    "line": i,
                    "category": category,
                    "matched": m.group(0),
                    "message": message,
                    "context": stripped[:120],
                })

        for pattern, category, message in MISSING_CLARIFICATION:
            if pattern.search(stripped):
                findings.append({
                    "line": i,
                    "category": category,
                    "matched": pattern.search(stripped).group(0),
                    "message": message,
                    "context": stripped[:120],
                })

    # Check if any "plan" or numbered-list block lacks verification
    plan_blocks = re.findall(r"(?:^|\n)((?:\d+\.\s+.+\n?)+)", text)
    for block in plan_blocks:
        has_verify = bool(re.search(r"\b(?:test|verify|check|assert|confirm|ensure|validate)\b", block, re.I))
        if not has_verify:
            findings.append({
                "line": 0,
                "category": "missing-verification",
                "matched": block[:80].replace("\n", " "),
                "message": "Plan block has no verification step. Add 'verify:' checks.",
                "context": block[:120].replace("\n", " "),
            })

    return findings


def main():
    p = argparse.ArgumentParser(
        description="Detect hidden assumptions in a plan or proposal (Karpathy Principle #1).",
        epilog="Reads a markdown file or stdin. Flags silent choices, vague actions, and missing verification.",
    )
    p.add_argument("input", nargs="?", default="-", help="Markdown file to lint, or - for stdin")
    p.add_argument("--json", action="store_true", help="JSON output")
    args = p.parse_args()

    if args.input == "-":
        text = sys.stdin.read()
        source = "stdin"
    else:
        path = Path(args.input)
        if not path.exists():
            print(f"[error] {path} not found", file=sys.stderr)
            sys.exit(1)
        text = path.read_text(encoding="utf-8", errors="replace")
        source = str(path)

    findings = lint_text(text, source)

    categories = {}
    for f in findings:
        categories.setdefault(f["category"], []).append(f)

    result = {
        "status": "ok",
        "source": source,
        "total_findings": len(findings),
        "by_category": {k: len(v) for k, v in categories.items()},
        "verdict": "CLEAN" if len(findings) == 0 else ("REVIEW" if len(findings) < 5 else "CLARIFY"),
        "findings": findings,
    }

    if args.json:
        print(json.dumps(result, indent=2))
        return

    print(f"Assumption Linter — {source}")
    print(f"Findings: {len(findings)}  Verdict: {result['verdict']}")
    if findings:
        print()
        for cat, items in categories.items():
            print(f"  [{cat}] ({len(items)})")
            for item in items[:5]:
                line_ref = f"L{item['line']}: " if item["line"] else ""
                print(f"    {line_ref}{item['message']}")
                print(f"    → \"{item['matched']}\" in: {item['context'][:80]}")
            if len(items) > 5:
                print(f"    ... and {len(items) - 5} more")
            print()
    else:
        print("\n  Plan looks explicit. Assumptions are surfaced.")

    print(f"\nVerdict: {result['verdict']}")


if __name__ == "__main__":
    main()
