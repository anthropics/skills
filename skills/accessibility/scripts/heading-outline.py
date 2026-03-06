#!/usr/bin/env python3
"""
Heading Outline Checker

Extract heading hierarchy from HTML and flag accessibility issues:
skipped levels, missing h1, multiple h1s, empty headings.

No dependencies — stdlib only.

Usage:
    python3 heading-outline.py index.html
    python3 heading-outline.py --format json page.html
"""

import argparse
import json
import os
import re
import sys
from html.parser import HTMLParser


class HeadingExtractor(HTMLParser):
    def __init__(self):
        super().__init__()
        self.headings = []
        self.issues = []
        self._in_heading = False
        self._current_level = 0
        self._current_text = ""
        self._current_line = 0
        self._current_attrs = {}

    def handle_starttag(self, tag, attrs):
        if re.match(r'^h[1-6]$', tag):
            self._in_heading = True
            self._current_level = int(tag[1])
            self._current_text = ""
            self._current_line = self.getpos()[0]
            self._current_attrs = dict(attrs)

    def handle_data(self, data):
        if self._in_heading:
            self._current_text += data

    def handle_endtag(self, tag):
        if re.match(r'^h[1-6]$', tag) and self._in_heading:
            self._in_heading = False
            text = self._current_text.strip()
            self.headings.append({
                "level": self._current_level,
                "text": text,
                "line": self._current_line,
                "id": self._current_attrs.get("id", ""),
            })

    def analyze(self):
        if not self.headings:
            self.issues.append({
                "severity": "error",
                "issue": "No headings found",
                "fix": "Add at least an <h1> for the page title"
            })
            return

        # Check for h1
        h1s = [h for h in self.headings if h["level"] == 1]
        if len(h1s) == 0:
            self.issues.append({
                "severity": "error",
                "issue": "No <h1> element found",
                "fix": "Every page should have exactly one <h1> as the main title"
            })
        elif len(h1s) > 1:
            lines = [str(h["line"]) for h in h1s]
            self.issues.append({
                "severity": "warning",
                "issue": f"Multiple <h1> elements found (lines {', '.join(lines)})",
                "fix": "Use only one <h1> per page for the main title"
            })

        # Check for skipped levels
        prev_level = 0
        for h in self.headings:
            if h["level"] > prev_level + 1 and prev_level > 0:
                self.issues.append({
                    "severity": "error",
                    "issue": f"Skipped heading level: h{prev_level} -> h{h['level']} "
                             f"(line {h['line']})",
                    "fix": f"Use h{prev_level + 1} instead, or add the missing intermediate level"
                })
            prev_level = h["level"]

            # Check for empty headings
            if not h["text"]:
                self.issues.append({
                    "severity": "error",
                    "issue": f"Empty <h{h['level']}> at line {h['line']}",
                    "fix": "Headings must have text content for screen readers"
                })

        # First heading should be h1
        if self.headings and self.headings[0]["level"] != 1:
            self.issues.append({
                "severity": "warning",
                "issue": f"First heading is <h{self.headings[0]['level']}>, not <h1>",
                "fix": "The first heading on the page should be <h1>"
            })


def audit_file(filepath):
    with open(filepath, "r", encoding="utf-8", errors="replace") as f:
        content = f.read()

    extractor = HeadingExtractor()
    extractor.feed(content)
    extractor.analyze()
    return extractor.headings, extractor.issues


def main():
    parser = argparse.ArgumentParser(
        description="Extract and validate heading hierarchy in HTML files."
    )
    parser.add_argument("files", nargs="+", help="HTML files to audit")
    parser.add_argument("--format", choices=["text", "json"], default="text")
    args = parser.parse_args()

    all_results = {}
    total_issues = 0

    for filepath in args.files:
        if not os.path.isfile(filepath):
            print(f"Warning: {filepath} not found, skipping", file=sys.stderr)
            continue
        headings, issues = audit_file(filepath)
        all_results[filepath] = {"headings": headings, "issues": issues}
        total_issues += len(issues)

    if args.format == "json":
        print(json.dumps(all_results, indent=2))
    else:
        for filepath, result in all_results.items():
            headings = result["headings"]
            issues = result["issues"]
            print(f"\n{'='*60}")
            print(f"  {filepath} — Heading Outline")
            print(f"{'='*60}")

            for h in headings:
                indent = "  " * h["level"]
                id_str = f' #{h["id"]}' if h["id"] else ""
                text = h["text"][:60] + "..." if len(h["text"]) > 60 else h["text"]
                print(f"  {indent}h{h['level']}: {text}{id_str}  (line {h['line']})")

            if issues:
                print(f"\n  Issues ({len(issues)}):")
                for issue in issues:
                    icon = {"error": "ERR", "warning": "WRN"}[issue["severity"]]
                    print(f"    [{icon}] {issue['issue']}")
                    print(f"          {issue['fix']}")
            else:
                print("\n  No issues found.")
            print()

    sys.exit(1 if total_issues > 0 else 0)


if __name__ == "__main__":
    main()
