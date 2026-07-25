#!/usr/bin/env python3
"""skill_description_validator.py — Validate a skill's description against Matt Pocock's rules.

Stdlib-only. Parses YAML frontmatter of a SKILL.md and checks the `description`
field against the criteria from Matt Pocock's write-a-skill:

  1. Description present (non-empty after `description:` key)
  2. Length <= 1024 characters
  3. Written in third person (no first-person pronouns I/me/my; no second-person you)
  4. Has explicit trigger phrase: "Use when ..." (or similar trigger pattern)
  5. First sentence describes what the skill does (heuristic: at least one verb)

Outputs pass/fail per check + overall verdict.

Deterministic logic. No LLM calls. Stdlib only.

Usage:
    python skill_description_validator.py                       # uses embedded sample
    python skill_description_validator.py path/to/SKILL.md
    python skill_description_validator.py path/to/SKILL.md --output json
"""

import argparse
import json
import re
import sys
from typing import Any, Dict, List, Optional


# Embedded sample: a SKILL.md description that PASSES all checks
SAMPLE_DESCRIPTION = (
    "Extract text and tables from PDF files, fill forms, merge documents. "
    "Use when working with PDF files or when user mentions PDFs, forms, or document extraction."
)

# Embedded sample: SKILL.md content (just the frontmatter + body shell)
SAMPLE_SKILL_MD = f"""---
name: pdf-tools
description: {SAMPLE_DESCRIPTION}
---

# PDF Tools

## Quick start
...
"""


# First-person pronouns + second-person pronouns to flag
FIRST_PERSON = {"i", "me", "my", "myself", "we", "us", "our", "ours", "ourselves"}
SECOND_PERSON = {"you", "your", "yours", "yourself"}

# Trigger phrases that count as explicit "use when" triggers
# Per Matt Pocock's rule: descriptions need an explicit trigger so agents know when to invoke.
# Natural English variants are all accepted: "Use when/before/during/after/for/while ..." etc.
TRIGGER_PATTERNS = [
    re.compile(r"\buse\s+when\b", re.IGNORECASE),
    re.compile(r"\buse\s+for\b", re.IGNORECASE),
    re.compile(r"\buse\s+before\b", re.IGNORECASE),
    re.compile(r"\buse\s+during\b", re.IGNORECASE),
    re.compile(r"\buse\s+after\b", re.IGNORECASE),
    re.compile(r"\buse\s+while\b", re.IGNORECASE),
    re.compile(r"\binvoke\s+when\b", re.IGNORECASE),
    re.compile(r"\binvoke\s+before\b", re.IGNORECASE),
    re.compile(r"\binvoke\s+after\b", re.IGNORECASE),
    re.compile(r"\btrigger\s+when\b", re.IGNORECASE),
    re.compile(r"\bapply\s+when\b", re.IGNORECASE),
    re.compile(r"\brun\s+when\b", re.IGNORECASE),
    re.compile(r"\brun\s+before\b", re.IGNORECASE),
]


def extract_frontmatter(text: str) -> Dict[str, str]:
    """Extract YAML frontmatter as a flat dict. Stdlib-only — minimal YAML parser
    sufficient for SKILL.md frontmatter (key: value pairs, no nesting)."""
    if not text.startswith("---"):
        return {}
    end = text.find("\n---", 3)
    if end == -1:
        return {}
    block = text[3:end].strip()
    out: Dict[str, str] = {}
    current_key: Optional[str] = None
    buffer: List[str] = []
    for line in block.splitlines():
        if ":" in line and not line.startswith(" ") and not line.startswith("\t"):
            # Flush previous
            if current_key:
                out[current_key] = " ".join(buffer).strip()
                buffer = []
            key, _, val = line.partition(":")
            current_key = key.strip()
            val = val.strip()
            if val and val != ">":
                buffer.append(val)
        elif current_key and line.strip():
            buffer.append(line.strip())
    if current_key:
        out[current_key] = " ".join(buffer).strip()
    return out


def check_present(desc: str) -> Dict[str, Any]:
    return {
        "rule": "description_present",
        "pass": bool(desc and desc.strip()),
        "detail": f"Length: {len(desc)} chars" if desc else "Missing or empty description field",
    }


def check_length(desc: str, max_chars: int = 1024) -> Dict[str, Any]:
    n = len(desc)
    return {
        "rule": "description_length",
        "pass": n <= max_chars,
        "detail": f"{n} chars (limit {max_chars})",
    }


def check_third_person(desc: str) -> Dict[str, Any]:
    words = re.findall(r"\b[a-zA-Z]+\b", desc.lower())
    flagged_first = [w for w in words if w in FIRST_PERSON]
    flagged_second = [w for w in words if w in SECOND_PERSON]
    flagged = flagged_first + flagged_second
    return {
        "rule": "third_person",
        "pass": len(flagged) == 0,
        "detail": f"Found pronouns: {sorted(set(flagged))}" if flagged else "No 1st/2nd-person pronouns",
    }


def check_trigger(desc: str) -> Dict[str, Any]:
    for pattern in TRIGGER_PATTERNS:
        if pattern.search(desc):
            return {
                "rule": "explicit_trigger",
                "pass": True,
                "detail": f"Found trigger phrase matching: {pattern.pattern}",
            }
    return {
        "rule": "explicit_trigger",
        "pass": False,
        "detail": 'No explicit trigger ("Use when..." or similar). Agent will struggle to know when to invoke.',
    }


# Action verb vocabulary used to detect "first sentence describes what the skill does"
# This is content data, not an assumption — these are the verbs we look for in skill descriptions.
ACTION_VERB_VOCABULARY = (
    "extract", "fill", "merge", "create", "build", "generate", "analyze", "analyse",
    "validate", "check", "run", "format", "parse", "render", "review", "audit", "scan",
    "compute", "score", "track", "report", "transform", "convert", "deploy", "test",
    "monitor", "log", "search", "find", "fetch", "store", "send", "read", "write",
    "refresh", "remove", "process", "manage", "apply", "implement", "interrogate",
    "orchestrate", "classify",
)
ACTION_VERB_RE = re.compile(
    r"\b(" + "|".join(ACTION_VERB_VOCABULARY) + r")s?\b",
    re.IGNORECASE,
)


def check_first_sentence_has_verb(desc: str) -> Dict[str, Any]:
    # Heuristic: split on first period; first sentence should have an action verb
    parts = re.split(r"\.\s+", desc, maxsplit=1)
    first = parts[0] if parts else desc
    verbs = ACTION_VERB_RE.findall(first)
    return {
        "rule": "first_sentence_has_action_verb",
        "pass": len(verbs) >= 1,
        "detail": f"Verb(s) found in first sentence: {verbs}" if verbs else "No action verb detected in first sentence",
    }


def analyze(skill_md_text: str) -> Dict[str, Any]:
    fm = extract_frontmatter(skill_md_text)
    desc = fm.get("description", "")
    checks = [
        check_present(desc),
        check_length(desc),
        check_third_person(desc),
        check_trigger(desc),
        check_first_sentence_has_verb(desc),
    ]
    passed = sum(1 for c in checks if c["pass"])
    overall = "PASS" if passed == len(checks) else ("WARN" if passed >= 3 else "FAIL")
    return {
        "description": desc,
        "checks": checks,
        "passed": passed,
        "total": len(checks),
        "overall": overall,
    }


def render_text(r: Dict[str, Any], source: str) -> str:
    lines = []
    lines.append("=" * 72)
    lines.append("SKILL DESCRIPTION VALIDATOR")
    lines.append(f"Source: {source}")
    lines.append("=" * 72)
    lines.append("")
    lines.append(f"Description ({len(r['description'])} chars):")
    lines.append(f"  {r['description'][:200]}{'...' if len(r['description']) > 200 else ''}")
    lines.append("")
    lines.append("-" * 72)
    lines.append(f"Checks: {r['passed']} / {r['total']} passed")
    lines.append("")
    for c in r["checks"]:
        marker = "PASS" if c["pass"] else "FAIL"
        lines.append(f"  [{marker}] {c['rule']:30s}  {c['detail']}")
    lines.append("")
    lines.append("-" * 72)
    lines.append(f"Verdict: {r['overall']}")
    lines.append("")
    lines.append("Rules (per Matt Pocock's write-a-skill):")
    lines.append("  - Max 1024 chars")
    lines.append("  - Third person (no I/we/you)")
    lines.append("  - First sentence: what it does (action verb)")
    lines.append("  - Second sentence: 'Use when [specific triggers]'")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Validate a SKILL.md description per Matt Pocock's rules.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("path", nargs="?", help="Path to SKILL.md (uses embedded sample if omitted)")
    parser.add_argument("--output", choices=("text", "json"), default="text", help="Output format")
    args = parser.parse_args()

    if args.path:
        try:
            with open(args.path, "r", encoding="utf-8") as f:
                text = f.read()
            source = args.path
        except (IOError, OSError) as e:
            print(f"error: could not read {args.path}: {e}", file=sys.stderr)
            return 1
    else:
        text = SAMPLE_SKILL_MD
        source = "<embedded sample: pdf-tools description (PASS expected)>"

    result = analyze(text)
    if args.output == "json":
        print(json.dumps({"source": source, **result}, indent=2))
    else:
        print(render_text(result, source))
    return 0 if result["overall"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
