#!/usr/bin/env python3
"""decision_tree_extractor.py — Extract decision branches from a plan/design doc.

Stdlib-only. Scans a markdown plan and identifies decision branches by detecting:

  1. Modal verbs of intent: "we'll", "we will", "we plan to", "we should", "we could"
  2. Open questions: sentences ending in "?"
  3. Choices: "X or Y" / "either X or Y" / "vs"
  4. TBDs: "TBD", "to be decided", "open question"
  5. Trade-off markers: "trade-off", "tradeoff", "pros/cons"

Output: numbered list of decision branches with line refs.

NO LLM CALLS. Pure regex + line walking.

Usage:
    python decision_tree_extractor.py                          # uses embedded sample
    python decision_tree_extractor.py path/to/plan.md
    python decision_tree_extractor.py plan.md --output json
"""

import argparse
import json
import re
import sys
from typing import Any, Dict, List


# Regex patterns that indicate a decision branch
DECISION_PATTERNS = [
    (re.compile(r"\bwe\s*(?:'ll|will|plan\s+to|should|could|might|may)\b", re.IGNORECASE),
     "intent"),
    (re.compile(r"\b(?:either|or)\b.{0,80}\b(?:or|alternatively)\b", re.IGNORECASE),
     "choice"),
    (re.compile(r"\bversus\b|\bvs\.?\b", re.IGNORECASE),
     "choice"),
    (re.compile(r"\bTBD\b|\bto\s+be\s+(?:decided|determined)\b", re.IGNORECASE),
     "open"),
    (re.compile(r"\bopen\s+question\b", re.IGNORECASE),
     "open"),
    (re.compile(r"\btrade-?offs?\b", re.IGNORECASE),
     "tradeoff"),
    (re.compile(r"\bdepends?\s+on\b", re.IGNORECASE),
     "dependency"),
    (re.compile(r"\?\s*$"),
     "question"),
]


SAMPLE_PLAN = """# Plan: Multi-tenant SaaS Migration

## Architecture
We'll move to a single-tenant database per customer. Or maybe we should
do schema-per-tenant for cost. This is a trade-off between isolation and ops cost.

## Auth
TBD: SSO provider — Okta or Auth0?

## Migration sequence
We plan to migrate the largest tenant first. Depends on whether their data fits in 24h.
Open question: rollback strategy?

## Data layer
We could use Postgres logical replication, but we might prefer dual-writes.
Trade-off: complexity vs zero-downtime guarantee.

## Cut-over
Final decision TBD on whether to flip DNS at midnight or use feature flags.
"""


def extract_branches(text: str) -> List[Dict[str, Any]]:
    branches: List[Dict[str, Any]] = []
    seen_lines = set()
    for line_no, line in enumerate(text.splitlines(), start=1):
        for pattern, kind in DECISION_PATTERNS:
            match = pattern.search(line)
            if not match:
                continue
            if line_no in seen_lines:
                continue
            seen_lines.add(line_no)
            branches.append({
                "line": line_no,
                "kind": kind,
                "trigger": match.group(0),
                "context": line.strip()[:160],
            })
            break
    return branches


def analyze(text: str) -> Dict[str, Any]:
    branches = extract_branches(text)
    by_kind: Dict[str, int] = {}
    for b in branches:
        by_kind[b["kind"]] = by_kind.get(b["kind"], 0) + 1
    return {
        "total_branches": len(branches),
        "by_kind": by_kind,
        "branches": branches,
    }


def render_text(r: Dict[str, Any]) -> str:
    lines = []
    lines.append("=" * 72)
    lines.append("DECISION TREE EXTRACTOR")
    lines.append("=" * 72)
    lines.append("")
    lines.append(f"Total decision branches found: {r['total_branches']}")
    lines.append(f"By kind: {r['by_kind']}")
    lines.append("")
    lines.append("-" * 72)
    for i, b in enumerate(r["branches"], start=1):
        lines.append(f"  [{i:2d}] L{b['line']:>4d} ({b['kind']:11s}) {b['context']}")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Extract decision branches from a plan/design document.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("path", nargs="?", help="Path to markdown plan (uses embedded sample if omitted)")
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
        text = SAMPLE_PLAN

    result = analyze(text)
    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_text(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
