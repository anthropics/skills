#!/usr/bin/env python3
"""dump_classifier.py — Heuristic classifier for brain-dump lines.

Stdlib-only. Reads a dump file (or stdin) and labels each line as one of:
  - task            (action-oriented, imperative or 'I should X')
  - decision        ('decide between X and Y', 'should we X or Y')
  - question        (ends in '?')
  - idea            (creative spark, 'what if', 'maybe we should X')
  - project-component  (sub-element of a larger project, often noun-phrased)
  - context         (preamble, framing, no actionable content)

The classifier is HEURISTIC. The capture skill uses these labels as a SEED for
its own structuring — it overrides based on dump-level context. Do not treat
the labels as authoritative.

NO LLM CALLS. Pure regex + line walking.

Usage:
    python dump_classifier.py path/to/dump.txt
    python dump_classifier.py path/to/dump.txt --output json
    python dump_classifier.py --sample
"""

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any, Dict, List, Tuple


# Pattern → label, ordered by precedence (first match wins per line).
# Each pattern is a compiled regex.
PATTERNS: List[Tuple[re.Pattern, str]] = [
    (re.compile(r"\bdecide\s+(?:between|on|whether)\b", re.IGNORECASE), "decision"),
    (re.compile(r"^\s*decide\s*:", re.IGNORECASE), "decision"),
    (re.compile(r"\b(?:should we|do we|are we)\b.*\b(?:or|vs|versus)\b", re.IGNORECASE), "decision"),
    (re.compile(r"\?\s*$"), "question"),
    (re.compile(r"^\s*(?:resolve|q)\s*:", re.IGNORECASE), "question"),
    (re.compile(r"\bwhat\s+if\b", re.IGNORECASE), "idea"),
    (re.compile(r"\b(?:maybe|might|could)\s+(?:we|i)\s+(?:should\s+)?", re.IGNORECASE), "idea"),
    (re.compile(r"\bidea\s*:", re.IGNORECASE), "idea"),
    (re.compile(r"^\s*(?:i\s+(?:should|need\s+to|gotta|have\s+to))\b", re.IGNORECASE), "task"),
    (re.compile(r"^\s*(?:fix|build|write|draft|email|send|talk to|finish|investigate|research|sketch|scaffold|deploy|push|merge|review|read|call|schedule)\b", re.IGNORECASE), "task"),
    (re.compile(r"^\s*todo\s*:", re.IGNORECASE), "task"),
    (re.compile(r"^\s*-\s*(?:fix|build|write|draft|email|send|talk to|finish|investigate)\b", re.IGNORECASE), "task"),
]

PROJECT_COMPONENT_HINTS = {
    "module", "feature", "component", "endpoint", "page", "screen", "form",
    "model", "schema", "migration", "test", "doc", "readme", "config",
}


SAMPLE_DUMP = """Ok dump time.

Q3 launch is approaching - need to nail down pricing.
Draft the launch email.
Brief Sarah on the marketing angle.

Decide: launch on July 15 or August 1?

Ferret app keeps nagging me. Should I talk to my cofounder about it?
What if it's actually a real business?
Sketch the matching algorithm if it's serious.

Fix the damn auth bug.
Rewrite the login form because it's ugly.
Write tests for both.
Auth: 2fa module.

Do my Q3 OKRs before launch.
"""


def classify_line(raw: str) -> str:
    line = raw.strip()
    if not line:
        return "blank"

    # Strip leading bullet markers for matching, but keep original for output
    stripped = re.sub(r"^[-*+]\s+", "", line)

    for pattern, label in PATTERNS:
        if pattern.search(stripped):
            return label

    # Project-component heuristic: short noun-phrase containing a hint word
    if len(stripped.split()) <= 6:
        for hint in PROJECT_COMPONENT_HINTS:
            if re.search(rf"\b{hint}s?\b", stripped, re.IGNORECASE):
                return "project-component"

    # Single-noun-phrase or short fragment without verb → likely context or component
    if len(stripped.split()) <= 4 and not stripped.endswith("?"):
        return "project-component"

    # Default: treat as context (the skill folds this into project framing)
    return "context"


def classify(text: str) -> Dict[str, Any]:
    items: List[Dict[str, Any]] = []
    counts: Dict[str, int] = {}
    for line_no, raw in enumerate(text.splitlines(), start=1):
        if not raw.strip():
            continue
        label = classify_line(raw)
        if label == "blank":
            continue
        items.append({"line": line_no, "label": label, "text": raw.strip()})
        counts[label] = counts.get(label, 0) + 1
    return {"item_count": len(items), "by_label": counts, "items": items}


def render_human(result: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append(f"Dump classification ({result['item_count']} non-empty items)")
    out.append("By label:")
    for label, n in sorted(result["by_label"].items(), key=lambda kv: -kv[1]):
        out.append(f"  {label:<20s} {n}")
    out.append("")
    out.append("Per-line labels:")
    for it in result["items"]:
        out.append(f"  L{it['line']:>3}  {it['label']:<20s} {it['text'][:80]}")
    return "\n".join(out)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("path", nargs="?", help="Path to dump file (or omit for --sample)")
    parser.add_argument("--sample", action="store_true", help="Classify the embedded sample dump")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    if args.sample:
        text = SAMPLE_DUMP
    elif args.path:
        p = Path(args.path)
        if not p.exists():
            print(f"error: {args.path} not found", file=sys.stderr)
            return 2
        text = p.read_text(encoding="utf-8")
    else:
        parser.print_help()
        return 0

    result = classify(text)
    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_human(result))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
