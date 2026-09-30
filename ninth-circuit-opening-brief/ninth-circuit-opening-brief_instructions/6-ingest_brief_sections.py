#!/usr/bin/env python3
"""
Ingest a tagged brief draft into brief_data/sections.json without touching case_info.
Tags use `=== SECTION NAME ===` headings. Content under each tag is copied verbatim
into sections.json. No rewriting, no styling changes.

Example input snippet:

=== INTRODUCTION ===
Your intro text...

=== ARGUMENT ===
Your argument text (may include markdown headings, lists, quotes)...

Run:
  python ingest_brief_sections.py --input pasted_brief.txt
"""

import argparse
import json
import re
from pathlib import Path
from typing import Dict, List, Tuple

# Map tag -> sections.json path
SECTION_MAP: Dict[str, str] = {
    "DISCLOSURE STATEMENT": "disclosure_statement",
    "INTRODUCTION": "introduction",
    "JURISDICTIONAL STATEMENT": "jurisdictional_statement",
    "STATUTORY [AND REGULATORY] AUTHORITIES": "statutory_authorities",
    "STATUTORY AND REGULATORY AUTHORITIES": "statutory_authorities",
    "ISSUES PRESENTED": "issues_presented",
    "STATEMENT OF THE CASE": "statement_of_case",
    "SUMMARY OF THE ARGUMENT": "summary_of_argument",
    "STANDARD OF REVIEW": "standard_of_review",
    "ARGUMENT": "argument",
    "ARGUMENT I": "argument_i",
    "ARGUMENT II": "argument_ii",
    "ARGUMENT III": "argument_iii",
    "CONCLUSION": "conclusion",
    "STATEMENT OF RELATED CASES": "related_cases",
    "ADDENDUM": "addendum",
}

TAG_PATTERN = re.compile(r"^===\s*(.+?)\s*===\s*$")


def parse_sections(text: str) -> List[Tuple[str, str]]:
    """Parse tagged sections from input text."""
    lines = text.splitlines()
    current_tag = None
    buffer: List[str] = []
    sections: List[Tuple[str, str]] = []

    def flush():
        nonlocal buffer, current_tag
        if current_tag is not None:
            content = "\n".join(buffer).strip()
            sections.append((current_tag, content))
        buffer = []

    for line in lines:
        m = TAG_PATTERN.match(line)
        if m:
            flush()
            current_tag = m.group(1).strip()
        else:
            buffer.append(line)
    flush()
    return sections


def load_sections_json(path: Path) -> Dict:
    if path.exists():
        with path.open("r", encoding="utf-8") as f:
            return json.load(f)
    # Initialize minimal structure if missing
    return {"case_info": {}, "sections": {}}


def save_sections_json(path: Path, data: Dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=4)


def main() -> None:
    parser = argparse.ArgumentParser(description="Ingest tagged brief into sections.json")
    parser.add_argument("--input", required=True, help="Path to tagged brief text/markdown file")
    parser.add_argument(
        "--sections-json",
        default="brief_data/sections.json",
        help="Path to sections.json (default: brief_data/sections.json)",
    )
    parser.add_argument(
        "--backup",
        action="store_true",
        help="Write a .bak copy of sections.json before modifying",
    )
    args = parser.parse_args()

    input_path = Path(args.input)
    sections_path = Path(args.sections_json)

    if not input_path.exists():
        raise SystemExit(f"Input file not found: {input_path}")

    text = input_path.read_text(encoding="utf-8")
    parsed = parse_sections(text)

    data = load_sections_json(sections_path)
    data.setdefault("sections", {})

    if args.backup and sections_path.exists():
        backup_path = sections_path.with_suffix(sections_path.suffix + ".bak")
        backup_path.write_text(sections_path.read_text(encoding="utf-8"), encoding="utf-8")

    applied = []
    skipped = []

    for tag, content in parsed:
        key = SECTION_MAP.get(tag.upper())
        if not key:
            skipped.append(tag)
            continue
        data["sections"].setdefault(key, {})
        data["sections"][key]["text"] = content
        applied.append(tag)

    save_sections_json(sections_path, data)

    print("Updated sections.json")
    if applied:
        print("Applied tags:")
        for t in applied:
            print(f"  - {t}")
    if skipped:
        print("Skipped (unrecognized tags):")
        for t in skipped:
            print(f"  - {t}")
    print("Done.")


if __name__ == "__main__":
    main()
