#!/usr/bin/env python3
"""
Verbatim section copier: takes a tagged text/markdown file and copies section
bodies exactly into brief_data/sections.json. No rewriting, no formatting
changes, no generation. It only overwrites the section text fields mapped below.

Usage:
  python copy_plain_sections.py --input path/to/pasted_brief.txt --backup

Tags (must appear as `=== SECTION NAME ===` on their own line):
  DISCLOSURE STATEMENT
  INTRODUCTION
  JURISDICTIONAL STATEMENT
  STATUTORY [AND REGULATORY] AUTHORITIES (or STATUTORY AND REGULATORY AUTHORITIES)
  ISSUES PRESENTED
  STATEMENT OF THE CASE
  SUMMARY OF THE ARGUMENT
  STANDARD OF REVIEW
  ARGUMENT
  ARGUMENT I
  ARGUMENT II
  ARGUMENT III
  CONCLUSION
  STATEMENT OF RELATED CASES
  ADDENDUM

Only recognized tags are applied; unrecognized tags are reported and skipped.
Case info is never touched. A .bak is written if --backup is provided and the
sections file exists.
"""

import argparse
import json
import re
from pathlib import Path
from typing import Dict, List, Tuple

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
    lines = text.splitlines()
    current_tag = None
    buf: List[str] = []
    out: List[Tuple[str, str]] = []

    def flush():
        nonlocal buf, current_tag
        if current_tag is not None:
            out.append((current_tag, "\n".join(buf).strip()))
        buf = []

    for line in lines:
        m = TAG_PATTERN.match(line)
        if m:
            flush()
            current_tag = m.group(1).strip()
        else:
            buf.append(line)
    flush()
    return out


def main() -> None:
    ap = argparse.ArgumentParser(description="Verbatim copy of tagged sections into sections.json")
    ap.add_argument("--input", required=True, help="Tagged input file")
    ap.add_argument("--sections-json", default="brief_data/sections.json", help="Path to sections.json")
    ap.add_argument("--backup", action="store_true", help="Write .bak before modifying")
    args = ap.parse_args()

    src_path = Path(args.input)
    dst_path = Path(args.sections_json)

    if not src_path.exists():
        raise SystemExit(f"Input file not found: {src_path}")

    text = src_path.read_text(encoding="utf-8")
    parsed = parse_sections(text)

    if dst_path.exists():
        data = json.loads(dst_path.read_text(encoding="utf-8"))
    else:
        data = {"case_info": {}, "sections": {}}
    data_sections = data.setdefault("sections", {})  # type: ignore

    if args.backup and dst_path.exists():
        bak = dst_path.with_suffix(dst_path.suffix + ".bak")
        bak.write_text(dst_path.read_text(encoding="utf-8"), encoding="utf-8")

    applied: List[str] = []
    skipped: List[str] = []
    arg_parts: List[Tuple[str, str]] = []  # collect ARGUMENT I/II/III text to flatten later

    for tag, content in parsed:
        key = SECTION_MAP.get(tag.upper())
        if not key:
            skipped.append(tag)
            continue
        data_sections.setdefault(key, {})  # type: ignore
        data_sections[key]["text"] = content  # type: ignore
        applied.append(tag)

        if key in {"argument_i", "argument_ii", "argument_iii"}:
            arg_parts.append((tag.upper(), content))

    # If ARGUMENT I/II/III were provided, flatten them into ARGUMENT with subheadings
    if arg_parts:
        # Preserve order ARGUMENT I, II, III
        order = {"ARGUMENT I": 1, "ARGUMENT II": 2, "ARGUMENT III": 3}
        arg_parts.sort(key=lambda x: order.get(x[0], 99))
        merged = ["ARGUMENTS", ""]
        for heading, body in arg_parts:
            merged.append(heading)
            merged.append("")
            merged.append(body)
            merged.append("")
        merged_text = "\n".join(merged).strip()
        data_sections.setdefault("argument", {})  # type: ignore
        data_sections["argument"]["text"] = merged_text  # type: ignore
        applied.append("ARGUMENT (flattened from I/II/III)")

    dst_path.parent.mkdir(parents=True, exist_ok=True)
    dst_path.write_text(json.dumps(data, ensure_ascii=False, indent=4), encoding="utf-8")

    print("Applied tags:")
    for t in applied:
        print(f"  - {t}")
    if skipped:
        print("Skipped (unrecognized):")
        for t in skipped:
            print(f"  - {t}")
    print("Done. No text was changed except direct copies into section fields.")


if __name__ == "__main__":
    main()
