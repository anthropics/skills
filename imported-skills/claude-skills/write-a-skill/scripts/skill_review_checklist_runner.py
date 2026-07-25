#!/usr/bin/env python3
"""skill_review_checklist_runner.py — Run Matt Pocock's 6-item review checklist programmatically.

Stdlib-only. Combines the description-validator + structure-validator into a single
report that mirrors Matt Pocock's review checklist from write-a-skill:

  1. [ ] Description includes triggers ("Use when...")
  2. [ ] SKILL.md under 100 lines
  3. [ ] No time-sensitive info (heuristic: no year mentions / "as of" claims / version-specific dates)
  4. [ ] Consistent terminology (heuristic: no obvious synonym pairs in same doc — light check)
  5. [ ] Concrete examples included (>=1 code block)
  6. [ ] References one level deep

This is the canonical pre-commit check for any new skill in this repo.

Deterministic logic. No LLM calls. Stdlib only.

Usage:
    python skill_review_checklist_runner.py                       # uses embedded sample (this skill's own folder)
    python skill_review_checklist_runner.py path/to/skill-folder/
    python skill_review_checklist_runner.py path/to/skill-folder/ --output json
"""

import argparse
import json
import os
import re
import sys
from typing import Any, Dict, List


# Phrases that suggest time-sensitive content
TIME_SENSITIVE_PATTERNS = [
    re.compile(r"\bas\s+of\s+\d{4}\b", re.IGNORECASE),
    re.compile(r"\bin\s+(20\d{2})\b", re.IGNORECASE),
    re.compile(r"\b(?:january|february|march|april|may|june|july|august|september|october|november|december)\s+\d{4}\b", re.IGNORECASE),
    re.compile(r"\b(?:released|launched|published|updated)\s+(?:on|in)\b", re.IGNORECASE),
]


def find_skill_md(folder: str) -> str:
    candidate = os.path.join(folder, "SKILL.md")
    return candidate if os.path.isfile(candidate) else ""


def extract_frontmatter_description(text: str) -> str:
    """Extract description from YAML frontmatter (single key)."""
    if not text.startswith("---"):
        return ""
    end = text.find("\n---", 3)
    if end == -1:
        return ""
    block = text[3:end]
    # Match "description: ..." potentially spanning multiple lines (>- folded)
    match = re.search(r"^description:\s*(.*)$(?:\n[ ]+(.*))*", block, re.MULTILINE)
    if not match:
        return ""
    val = match.group(1).strip()
    if val == ">" or val == "|":
        # Folded scalar — collect indented continuation lines
        lines_iter = iter(block.splitlines())
        for line in lines_iter:
            if line.strip().startswith("description:"):
                break
        collected = []
        for line in lines_iter:
            if line.startswith(" ") or line.startswith("\t"):
                collected.append(line.strip())
            else:
                break
        val = " ".join(collected)
    return val


# Trigger phrases that count as explicit "use when ..." triggers in a description.
# Per Matt Pocock's rule: explicit trigger phrase. Natural English variants all accepted.
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


def check_description_has_trigger(text: str) -> Dict[str, Any]:
    desc = extract_frontmatter_description(text)
    has_trigger = any(p.search(desc) for p in TRIGGER_PATTERNS)
    return {
        "rule": "1. Description includes triggers",
        "pass": has_trigger,
        "detail": ("Found explicit trigger phrase" if has_trigger
                   else "Missing explicit trigger phrase (Use when/before/after/for ...)"),
    }


def check_skill_md_length(filepath: str, max_lines: int = 100) -> Dict[str, Any]:
    with open(filepath, "r", encoding="utf-8") as f:
        lines = sum(1 for _ in f)
    return {
        "rule": f"2. SKILL.md under {max_lines} lines",
        "pass": lines <= max_lines,
        "detail": f"{lines} lines",
    }


def check_no_time_sensitive(text: str) -> Dict[str, Any]:
    flagged = []
    for pattern in TIME_SENSITIVE_PATTERNS:
        for m in pattern.finditer(text):
            flagged.append(m.group(0))
    # Limit
    flagged = list(dict.fromkeys(flagged))[:5]
    return {
        "rule": "3. No time-sensitive info",
        "pass": len(flagged) == 0,
        "detail": ("No date/year/version-bound claims detected" if not flagged
                   else f"Flagged phrases: {flagged}"),
    }


def check_consistent_terminology(text: str) -> Dict[str, Any]:
    """Light check for common synonym mismatches in the same doc."""
    synonyms = [
        ("agent", "bot"),
        ("skill", "tool"),
        ("user", "developer"),
    ]
    findings = []
    text_lower = text.lower()
    for a, b in synonyms:
        if re.search(rf"\b{re.escape(a)}\b", text_lower) and re.search(rf"\b{re.escape(b)}\b", text_lower):
            findings.append(f"Both '{a}' and '{b}' used")
    return {
        "rule": "4. Consistent terminology",
        "pass": len(findings) == 0,
        "detail": ("No obvious synonym pairs detected" if not findings
                   else "; ".join(findings)),
    }


def check_concrete_examples(text: str) -> Dict[str, Any]:
    code_blocks = re.findall(r"```", text)
    has_examples = len(code_blocks) >= 2  # opening + closing = 1 block
    return {
        "rule": "5. Concrete examples included",
        "pass": has_examples,
        "detail": f"{len(code_blocks) // 2} code block(s) found",
    }


def _find_nested_md(refs_subdir: str) -> List[str]:
    """Return .md files nested deeper than refs_subdir."""
    nested: List[str] = []
    if not os.path.isdir(refs_subdir):
        return nested
    for root, _, files in os.walk(refs_subdir):
        if root == refs_subdir:
            continue
        nested.extend(os.path.join(root, f) for f in files if f.endswith(".md"))
    return nested


def check_references_one_level_deep(folder: str) -> Dict[str, Any]:
    deeper = _find_nested_md(os.path.join(folder, "references"))
    return {
        "rule": "6. References one level deep",
        "pass": len(deeper) == 0,
        "detail": ("All references at one level" if not deeper
                   else f"Found nested ref files: {deeper}"),
    }


def analyze(folder: str) -> Dict[str, Any]:
    skill_md = find_skill_md(folder)
    if not skill_md:
        detail = f"SKILL.md not found at {folder}"
        missing_check = {"rule": "skill_md_present", "pass": False, "detail": detail}
        return {
            "folder": folder,
            "checks": [missing_check],
            "passed": 0,
            "total": 1,
            "overall": "FAIL",
        }
    with open(skill_md, "r", encoding="utf-8") as f:
        text = f.read()

    checks = [
        check_description_has_trigger(text),
        check_skill_md_length(skill_md, max_lines=100),
        check_no_time_sensitive(text),
        check_consistent_terminology(text),
        check_concrete_examples(text),
        check_references_one_level_deep(folder),
    ]
    passed = sum(1 for c in checks if c["pass"])
    total = len(checks)
    overall = "PASS" if passed == total else ("WARN" if passed >= total - 1 else "FAIL")

    return {
        "folder": folder,
        "skill_md": skill_md,
        "checks": checks,
        "passed": passed,
        "total": total,
        "overall": overall,
    }


def render_text(r: Dict[str, Any]) -> str:
    lines = []
    lines.append("=" * 72)
    lines.append("SKILL REVIEW CHECKLIST RUNNER (per Matt Pocock's write-a-skill)")
    lines.append(f"Folder: {r['folder']}")
    lines.append("=" * 72)
    lines.append("")
    lines.append(f"Checks: {r['passed']} / {r['total']} passed")
    lines.append("")
    for c in r["checks"]:
        marker = "[x]" if c["pass"] else "[ ]"
        lines.append(f"  {marker} {c['rule']}")
        lines.append(f"        {c['detail']}")
    lines.append("")
    lines.append("-" * 72)
    lines.append(f"Verdict: {r['overall']}")
    lines.append("")
    lines.append("Reference: Matt Pocock's 6-item review checklist from write-a-skill (MIT).")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Run Matt Pocock's 6-item review checklist on a skill folder.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("path", nargs="?", help="Path to skill folder (uses embedded sample if omitted)")
    parser.add_argument("--output", choices=("text", "json"), default="text", help="Output format")
    args = parser.parse_args()

    if args.path:
        folder = args.path
    else:
        folder = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

    if not os.path.isdir(folder):
        print(f"error: not a directory: {folder}", file=sys.stderr)
        return 1

    result = analyze(folder)
    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_text(result))
    return 0 if result["overall"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
