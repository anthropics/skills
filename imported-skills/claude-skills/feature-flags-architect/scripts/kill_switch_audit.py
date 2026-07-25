#!/usr/bin/env python3
"""Verify every feature flag in code has a documented kill switch.

Cross-references flag identifiers found in source code against a markdown
flag registry. Each documented flag must declare: owner, type, kill switch,
dashboard. Reports undocumented flags (FAIL) and incompletely-documented
flags (WARN). Use as a pre-merge gate.
"""
import argparse
import json
import os
import re
import sys

FLAG_PATTERNS = [
    re.compile(r'\b(?:isFlagEnabled|isEnabled|featureFlag|getFlag|flag|useFlag|useExperiment)\(\s*["\']([\w.\-:]+)["\']'),
    re.compile(r'\b(?:client|ld|unleash|growthbook|statsig)\.(?:variation|isEnabled|feature|getValue|getExperiment)\(\s*["\']([\w.\-:]+)["\']'),
]

REQUIRED_FIELDS = ("owner", "type", "kill switch", "dashboard")

CODE_EXTS = {".py", ".js", ".ts", ".tsx", ".jsx", ".go", ".rb", ".java", ".kt", ".cs", ".rs", ".php"}
SKIP_DIRS = {".git", "node_modules", ".venv", "venv", "dist", "build", "__pycache__", ".next"}


def _walk_code_files(repo):
    for root, dirs, files in os.walk(repo):
        dirs[:] = [d for d in dirs if d not in SKIP_DIRS]
        for f in files:
            if os.path.splitext(f)[1] in CODE_EXTS:
                yield os.path.join(root, f)


def discover_code_flags(repo):
    found = set()
    for path in _walk_code_files(repo):
        try:
            with open(path, "r", encoding="utf-8", errors="replace") as f:
                text = f.read()
        except OSError:
            continue
        for pat in FLAG_PATTERNS:
            for m in pat.finditer(text):
                found.add(m.group(1))
    return found


def _split_sections(text):
    """Split flag-doc into per-flag sections by H2 (## flag-name) or H3."""
    sections = {}
    current = None
    buf = []
    for line in text.splitlines():
        m = re.match(r"^#{2,3}\s+([\w.\-:]+)\s*$", line)
        if m:
            if current is not None:
                sections[current] = "\n".join(buf)
            current = m.group(1)
            buf = []
        else:
            buf.append(line)
    if current is not None:
        sections[current] = "\n".join(buf)
    return sections


def _missing_fields(section_text):
    lower = section_text.lower()
    return [f for f in REQUIRED_FIELDS if f not in lower]


def audit(repo, flag_doc_path):
    if not os.path.isfile(flag_doc_path):
        return {"error": f"flag-doc not found: {flag_doc_path}"}

    with open(flag_doc_path, "r", encoding="utf-8") as f:
        doc_text = f.read()
    sections = _split_sections(doc_text)
    documented = set(sections.keys())

    code_flags = discover_code_flags(repo)
    undocumented = sorted(code_flags - documented)
    orphaned_docs = sorted(documented - code_flags)

    incomplete = []
    for name in sorted(code_flags & documented):
        missing = _missing_fields(sections[name])
        if missing:
            incomplete.append({"flag": name, "missing": missing})

    return {
        "code_flags": sorted(code_flags),
        "documented_flags": sorted(documented),
        "undocumented": undocumented,
        "incomplete": incomplete,
        "orphaned_in_doc": orphaned_docs,
    }


def render_text(result):
    if "error" in result:
        print(f"ERROR: {result['error']}")
        return
    code, doc = result["code_flags"], result["documented_flags"]
    print(f"Kill Switch Audit — {len(code)} flags in code, {len(doc)} documented")
    print("")
    if result["undocumented"]:
        print(f"FAIL: {len(result['undocumented'])} undocumented flag(s):")
        for f in result["undocumented"]:
            print(f"  - {f}")
        print("")
    if result["incomplete"]:
        print(f"WARN: {len(result['incomplete'])} flag(s) with incomplete documentation:")
        for item in result["incomplete"]:
            print(f"  - {item['flag']}: missing {', '.join(item['missing'])}")
        print("")
    if result["orphaned_in_doc"]:
        print(f"INFO: {len(result['orphaned_in_doc'])} doc entry(s) for flags not in code:")
        for f in result["orphaned_in_doc"]:
            print(f"  - {f}")
        print("")
    if not (result["undocumented"] or result["incomplete"]):
        print("PASS: every code flag is fully documented.")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--repo", default=".", help="Path to repo root (default: .)")
    ap.add_argument("--flag-doc", required=True, help="Path to markdown flag registry (e.g., docs/feature-flags.md)")
    ap.add_argument("--format", choices=["text", "json"], default="text")
    args = ap.parse_args()

    result = audit(os.path.abspath(args.repo), args.flag_doc)
    if args.format == "json":
        print(json.dumps(result, indent=2))
    else:
        render_text(result)
    if "error" in result:
        return 2
    if result["undocumented"] or result["incomplete"]:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
