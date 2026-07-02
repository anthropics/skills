#!/usr/bin/env python3
"""
check_orphans.py - Detect lines at risk of orphan word wrap.

Part of the document-typography skill.

Reads a text file (one rule/line per row) or a JSON array of strings,
and checks each against configurable character limits.

Usage:
    python check_orphans.py rules.txt
    python check_orphans.py rules.txt --max1 68 --max2 136 --danger 6
    python check_orphans.py rules.json

The danger zone: max1 < length <= max1 + danger
These lines wrap with 1-6 orphan words on the next line.

Good lines are either:
    <= max1 chars (fits on one line)
    > max1 + danger chars (fills two lines well)
"""

import argparse
import json
import sys


def check_orphans(lines, max1=68, max2=136, danger=6):
    """Check lines for orphan risks.
    
    Returns list of (line_num, length, text, issue).
    """
    issues = []
    for i, line in enumerate(lines, 1):
        text = line.strip()
        if not text:
            continue
        length = len(text)

        if max1 < length <= max1 + danger:
            issues.append((i, length, text, "1-LINE ORPHAN"))
        elif max2 < length <= max2 + danger:
            issues.append((i, length, text, "2-LINE ORPHAN"))

    return issues


def load_lines(filepath):
    """Load lines from .txt or .json file."""
    if filepath.endswith('.json'):
        with open(filepath, 'r') as f:
            data = json.load(f)
        if isinstance(data, list):
            return [str(item) for item in data]
        raise ValueError("JSON file must contain an array of strings")
    else:
        with open(filepath, 'r') as f:
            return f.readlines()


def main():
    parser = argparse.ArgumentParser(
        description="Check for orphan word wrap risks in document lines"
    )
    parser.add_argument("file", help="Text file (.txt) or JSON array (.json)")
    parser.add_argument("--max1", type=int, default=68,
                        help="Max chars for single line (default: 68)")
    parser.add_argument("--max2", type=int, default=136,
                        help="Max chars for two full lines (default: 136)")
    parser.add_argument("--danger", type=int, default=6,
                        help="Orphan danger zone width in chars (default: 6)")
    args = parser.parse_args()

    lines = load_lines(args.file)
    issues = check_orphans(lines, args.max1, args.max2, args.danger)

    total = sum(1 for l in lines if l.strip())
    if not issues:
        print(f"All {total} lines OK (max1={args.max1}, max2={args.max2})")
    else:
        print(f"Found {len(issues)} orphan risks out of {total} lines:\n")
        for line_num, length, text, issue in issues:
            print(f"  Line {line_num:3d} ({length} chars) {issue}")
            print(f"    {text[:80]}{'...' if len(text) > 80 else ''}")
            print()

    return len(issues)


if __name__ == "__main__":
    sys.exit(0 if main() == 0 else 1)
