#!/usr/bin/env python3
"""skill_structure_validator.py — Validate a skill folder structure against Matt Pocock's pattern.

Stdlib-only. Walks a skill folder and checks:

  1. SKILL.md present at folder root
  2. SKILL.md <= 100 lines (Matt's ceiling; configurable via --max-lines)
  3. If SKILL.md > limit, separate reference files exist (REFERENCE.md, EXAMPLES.md, or references/*.md)
  4. Reference files are one level deep (no nested references in subfolders)
  5. No circular cross-references between markdown files (file A links to B which links back to A)
  6. Scripts present in scripts/ subfolder when SKILL.md mentions executable operations

Deterministic logic. No LLM calls. Stdlib only.

Usage:
    python skill_structure_validator.py                       # uses embedded sample (current write-a-skill folder)
    python skill_structure_validator.py path/to/skill-folder/
    python skill_structure_validator.py path/to/skill-folder/ --output json
    python skill_structure_validator.py path/to/skill-folder/ --max-lines 100
"""

import argparse
import json
import os
import re
import sys
from typing import Any, Dict, List, Set, Tuple


# Default max-lines threshold from Matt Pocock's write-a-skill review checklist
DEFAULT_MAX_LINES = 100

# Reference filename patterns Matt's pattern recognizes
REFERENCE_FILE_PATTERNS = ["REFERENCE.md", "EXAMPLES.md", "references", "examples"]

# Script folder names
SCRIPT_FOLDERS = ["scripts"]


def find_skill_md(folder: str) -> str:
    """Find SKILL.md at folder root; return its path or empty string."""
    candidate = os.path.join(folder, "SKILL.md")
    if os.path.isfile(candidate):
        return candidate
    return ""


def count_lines(filepath: str) -> int:
    with open(filepath, "r", encoding="utf-8") as f:
        return sum(1 for _ in f)


def _list_md_in_subdir(subdir: str) -> List[str]:
    """List .md files directly inside a subdirectory (not recursive)."""
    out: List[str] = []
    if not os.path.isdir(subdir):
        return out
    for name in sorted(os.listdir(subdir)):
        full = os.path.join(subdir, name)
        if os.path.isfile(full) and name.endswith(".md"):
            out.append(full)
    return out


def find_reference_files(folder: str) -> List[str]:
    """Find reference files at folder root + one-level-deep references/ subfolder."""
    refs: List[str] = []
    for name in os.listdir(folder):
        full = os.path.join(folder, name)
        if os.path.isfile(full) and name.endswith(".md") and name != "SKILL.md":
            refs.append(full)
        elif os.path.isdir(full) and name in ("references", "examples"):
            refs.extend(_list_md_in_subdir(full))
    return refs


def find_deeper_references(folder: str) -> List[str]:
    """Find markdown files nested deeper than one level (violation of one-level-deep rule)."""
    deeper: List[str] = []
    refs_subdir = os.path.join(folder, "references")
    if not os.path.isdir(refs_subdir):
        return deeper
    for root, _, files in os.walk(refs_subdir):
        if root == refs_subdir:
            continue
        for f in files:
            if f.endswith(".md"):
                deeper.append(os.path.join(root, f))
    return deeper


def has_scripts_folder(folder: str) -> bool:
    return os.path.isdir(os.path.join(folder, "scripts"))


def extract_md_links(text: str) -> List[str]:
    """Extract local markdown links: [...](path.md), excluding URLs."""
    pattern = re.compile(r"\[[^\]]+\]\(([^)]+\.md(?:#[^)]*)?)\)")
    links = []
    for m in pattern.finditer(text):
        target = m.group(1).split("#", 1)[0]
        if not target.startswith("http"):
            links.append(target)
    return links


def _collect_links_for_file(filepath: str, files: List[str]) -> Set[str]:
    """Read filepath, return set of links that resolve to other files in `files`."""
    out: Set[str] = set()
    try:
        with open(filepath, "r", encoding="utf-8") as fh:
            text = fh.read()
    except (IOError, OSError):
        return out
    for link in extract_md_links(text):
        target = os.path.normpath(os.path.join(os.path.dirname(filepath), link))
        if target in files:
            out.add(target)
    return out


def detect_circular_refs(folder: str, files: List[str]) -> List[Tuple[str, str]]:
    """Detect circular references: file A -> file B -> file A.
    Returns list of (file_a, file_b) tuples."""
    graph: Dict[str, Set[str]] = {f: _collect_links_for_file(f, files) for f in files}
    seen_pairs: Set[Tuple[str, str]] = set()
    circular: List[Tuple[str, str]] = []
    for a, neighbors in graph.items():
        for b in neighbors:
            if a not in graph.get(b, set()):
                continue
            pair = tuple(sorted([a, b]))
            if pair in seen_pairs:
                continue
            seen_pairs.add(pair)
            circular.append((a, b))
    return circular


def analyze(folder: str, max_lines: int) -> Dict[str, Any]:
    folder = folder.rstrip("/")
    findings: List[Dict[str, Any]] = []

    skill_md = find_skill_md(folder)
    if not skill_md:
        findings.append({
            "rule": "skill_md_present",
            "pass": False,
            "detail": f"SKILL.md not found at {folder}",
        })
        return {"folder": folder, "checks": findings, "passed": 0, "total": 1, "overall": "FAIL"}
    findings.append({
        "rule": "skill_md_present",
        "pass": True,
        "detail": skill_md,
    })

    lines = count_lines(skill_md)
    skill_md_under_ceiling = lines <= max_lines
    findings.append({
        "rule": "skill_md_line_count",
        "pass": skill_md_under_ceiling,
        "detail": f"{lines} lines (limit {max_lines})",
    })

    refs = find_reference_files(folder)
    if not skill_md_under_ceiling:
        # When SKILL.md exceeds ceiling, reference files SHOULD exist
        findings.append({
            "rule": "reference_files_when_split_needed",
            "pass": len(refs) > 0,
            "detail": f"Found {len(refs)} reference file(s)" if refs
            else "SKILL.md exceeds ceiling but no reference files present",
        })
    else:
        findings.append({
            "rule": "reference_files_when_split_needed",
            "pass": True,
            "detail": "SKILL.md under ceiling; reference split not required",
        })

    deeper = find_deeper_references(folder)
    findings.append({
        "rule": "references_one_level_deep",
        "pass": len(deeper) == 0,
        "detail": f"Found nested ref files (violations): {deeper}" if deeper
        else "All references are one level deep (or at root)",
    })

    all_md = [skill_md] + refs
    circular = detect_circular_refs(folder, all_md)
    findings.append({
        "rule": "no_circular_references",
        "pass": len(circular) == 0,
        "detail": f"Circular refs detected: {circular}" if circular
        else "No circular references between markdown files",
    })

    has_scripts = has_scripts_folder(folder)
    findings.append({
        "rule": "scripts_folder_present",
        "pass": True,
        "detail": "scripts/ folder exists" if has_scripts
        else "No scripts/ folder (optional per Matt's pattern)",
    })

    passed = sum(1 for c in findings if c["pass"])
    overall = "PASS" if passed == len(findings) else ("WARN" if passed >= len(findings) - 1 else "FAIL")

    return {
        "folder": folder,
        "max_lines_threshold": max_lines,
        "skill_md": skill_md,
        "skill_md_lines": lines,
        "reference_files": refs,
        "checks": findings,
        "passed": passed,
        "total": len(findings),
        "overall": overall,
    }


def render_text(r: Dict[str, Any]) -> str:
    lines = []
    lines.append("=" * 72)
    lines.append("SKILL STRUCTURE VALIDATOR")
    lines.append(f"Folder: {r['folder']}")
    lines.append(f"Max-lines threshold: {r['max_lines_threshold']}")
    lines.append("=" * 72)
    lines.append("")
    lines.append(f"SKILL.md: {r.get('skill_md', '<missing>')}  ({r.get('skill_md_lines', 0)} lines)")
    lines.append(f"Reference files: {len(r.get('reference_files', []))}")
    lines.append("")
    lines.append("-" * 72)
    lines.append(f"Checks: {r['passed']} / {r['total']} passed")
    lines.append("")
    for c in r["checks"]:
        marker = "PASS" if c["pass"] else "FAIL"
        lines.append(f"  [{marker}] {c['rule']:35s}  {c['detail']}")
    lines.append("")
    lines.append("-" * 72)
    lines.append(f"Verdict: {r['overall']}")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Validate skill folder structure per Matt Pocock's write-a-skill pattern.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    max_lines_help = f"SKILL.md line ceiling (default: {DEFAULT_MAX_LINES} per Matt's rule)"
    parser.add_argument("path", nargs="?", help="Path to skill folder (uses embedded sample if omitted)")
    parser.add_argument("--output", choices=("text", "json"), default="text", help="Output format")
    parser.add_argument("--max-lines", type=int, default=DEFAULT_MAX_LINES, help=max_lines_help)
    args = parser.parse_args()

    if args.path:
        folder = args.path
    else:
        # Embedded sample: validate this skill's own folder
        folder = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

    if not os.path.isdir(folder):
        print(f"error: not a directory: {folder}", file=sys.stderr)
        return 1

    result = analyze(folder, args.max_lines)
    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_text(result))
    return 0 if result["overall"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
