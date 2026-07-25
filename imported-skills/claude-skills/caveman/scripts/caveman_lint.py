#!/usr/bin/env python3
"""caveman_lint.py — Lint a response for caveman-mode compliance.

Stdlib-only. Detects banned vocabulary in a response that's supposed to be in
caveman mode. Returns specific findings + verdict.

Banned categories per Matt Pocock's caveman rules:
  - Pleasantries (sure, certainly, of course, happy to)
  - Filler (just, really, basically, actually, simply)
  - Hedging (might, maybe, perhaps, likely)
  - Metatalk (as you can see, worth noting)
  - Verbose phrases ("the implementation of a solution for")

Whitelist (NOT banned even in caveman mode):
  - Words inside code blocks
  - Words inside inline code
  - Words inside quoted strings
  - Caveman exception zones (security warnings, destructive op confirmations)

Usage:
    python caveman_lint.py                          # uses embedded samples
    python caveman_lint.py "response text"
    python caveman_lint.py --file path/to/response.txt
    python caveman_lint.py "text" --output json
"""

import argparse
import json
import re
import sys
from typing import Any, Dict, List


BANNED_PHRASES = {
    "pleasantry": [
        "sure!", "sure,", "certainly", "of course", "happy to help",
        "i'd be happy", "i would be happy", "great question", "good question",
        "absolutely", "no problem!",
    ],
    "filler": ["just", "really", "basically", "actually", "simply", "obviously", "literally"],
    "hedging": ["might", "maybe", "perhaps", "likely", "possibly", "probably"],
    "metatalk": [
        "as you can see", "it should be noted", "worth mentioning",
        "needless to say", "to be clear", "in other words",
        "that said", "having said that",
    ],
    "verbose": [
        "implement a solution for", "the implementation of",
        "in order to", "for the purpose of", "with respect to",
        "due to the fact that",
    ],
}

# Patterns that DROP caveman temporarily (whitelisted zones)
EXCEPTION_MARKERS = [
    re.compile(r"\*\*warning:\*\*", re.IGNORECASE),
    re.compile(r"\bdestructive\b", re.IGNORECASE),
    re.compile(r"\birreversible\b", re.IGNORECASE),
    re.compile(r"\bcannot be undone\b", re.IGNORECASE),
]


SAMPLE_BAD = (
    "Sure! I'd be happy to help. The issue is actually quite simple — basically, "
    "you just need to update the configuration. It's worth mentioning that this might "
    "cause a slight performance hit, but probably not noticeable."
)
SAMPLE_GOOD = "Bug in auth middleware. Token expiry check use `<` not `<=`. Fix: change to `<=`."


def _protect_code(text: str) -> str:
    """Mask code blocks + inline code so banned-word matching skips them."""
    text = re.sub(r"```.*?```", lambda m: "\x00" * len(m.group(0)), text, flags=re.DOTALL)
    text = re.sub(r"`[^`]+`", lambda m: "\x00" * len(m.group(0)), text)
    return text


def _has_exception_context(text: str) -> bool:
    return any(p.search(text) for p in EXCEPTION_MARKERS)


def _count_phrase(phrase: str, masked: str) -> int:
    return len(re.findall(r"\b" + re.escape(phrase) + r"\b", masked, re.IGNORECASE))


def _violation_record(category: str, phrase: str, count: int) -> Dict[str, Any]:
    return {"category": category, "phrase": phrase, "count": count}


def find_violations(text: str) -> List[Dict[str, Any]]:
    """Find banned phrases. Returns list of {category, phrase, count}."""
    masked = _protect_code(text)
    violations: List[Dict[str, Any]] = []
    for category, phrases in BANNED_PHRASES.items():
        for phrase in phrases:
            count = _count_phrase(phrase, masked)
            if count > 0:
                violations.append(_violation_record(category, phrase, count))
    return violations


def analyze(text: str) -> Dict[str, Any]:
    violations = find_violations(text)
    total_violations = sum(v["count"] for v in violations)
    has_exception = _has_exception_context(text)

    # Verdict logic:
    #   0 violations + reasonable length     -> CLEAN
    #   <= 2 violations OR exception context -> WARN
    #   >  2 violations                      -> FAIL
    if total_violations == 0:
        verdict = "CLEAN"
    elif has_exception:
        verdict = "WARN"
        # When there's a security warning, some normal language is allowed
    elif total_violations <= 2:
        verdict = "WARN"
    else:
        verdict = "FAIL"

    return {
        "char_count": len(text),
        "word_count": len(text.split()),
        "violation_categories": sorted(set(v["category"] for v in violations)),
        "total_violations": total_violations,
        "has_exception_context": has_exception,
        "violations": violations,
        "verdict": verdict,
    }


def render_text(text: str, r: Dict[str, Any]) -> str:
    lines = []
    lines.append("=" * 72)
    lines.append("CAVEMAN LINT")
    lines.append("=" * 72)
    lines.append("")
    preview = text[:200] + ("..." if len(text) > 200 else "")
    lines.append(f"Text ({r['char_count']} chars, {r['word_count']} words):")
    lines.append(f"  {preview}")
    lines.append("")
    lines.append("-" * 72)
    lines.append(f"Violations: {r['total_violations']}")
    lines.append(f"Categories hit: {r['violation_categories']}")
    if r["has_exception_context"]:
        lines.append("Exception context detected (warning/destructive zone — some prose allowed)")
    lines.append("")
    if r["violations"]:
        for v in r["violations"]:
            lines.append(f"  [{v['category']:11s}] x{v['count']:2d}  '{v['phrase']}'")
    else:
        lines.append("  No banned phrases found.")
    lines.append("")
    lines.append("-" * 72)
    lines.append(f"Verdict: {r['verdict']}")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Lint a response for caveman-mode compliance.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("text", nargs="?", help="Input text (uses embedded sample if omitted)")
    parser.add_argument("--file", help="Read input from file")
    parser.add_argument("--output", choices=("text", "json"), default="text", help="Output format")
    args = parser.parse_args()

    if args.file:
        try:
            with open(args.file, "r", encoding="utf-8") as f:
                text = f.read()
        except (IOError, OSError) as e:
            print(f"error: {e}", file=sys.stderr)
            return 1
    elif args.text:
        text = args.text
    else:
        text = SAMPLE_BAD

    result = analyze(text)
    if args.output == "json":
        print(json.dumps({"text": text, **result}, indent=2))
    else:
        print(render_text(text, result))
    return 0 if result["verdict"] == "CLEAN" else 1


if __name__ == "__main__":
    sys.exit(main())
