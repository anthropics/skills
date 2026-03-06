#!/usr/bin/env python3
"""
Link Text Audit

Find inaccessible link text: "click here", "read more", "here", empty links,
links with only an image but no alt text, and links with title but no text.
These are barriers for screen reader users who navigate by link list.

No dependencies — stdlib only.

Usage:
    python3 link-text-audit.py index.html
    python3 link-text-audit.py --format json page.html
"""

import argparse
import json
import os
import re
import sys
from html.parser import HTMLParser


VAGUE_LINK_PATTERNS = [
    re.compile(r'^click\s+here\.?$', re.I),
    re.compile(r'^here\.?$', re.I),
    re.compile(r'^read\s+more\.?$', re.I),
    re.compile(r'^more\.?$', re.I),
    re.compile(r'^learn\s+more\.?$', re.I),
    re.compile(r'^link\.?$', re.I),
    re.compile(r'^this\.?$', re.I),
    re.compile(r'^page\.?$', re.I),
    re.compile(r'^info\.?$', re.I),
    re.compile(r'^details\.?$', re.I),
]


class LinkAuditor(HTMLParser):
    def __init__(self):
        super().__init__()
        self.issues = []
        self.stats = {"total_links": 0, "good": 0, "issues": 0}
        self._in_link = False
        self._link_text = ""
        self._link_attrs = {}
        self._link_line = 0
        self._link_has_img = False
        self._link_img_alt = None

    def handle_starttag(self, tag, attrs):
        attrs_dict = dict(attrs)

        if tag == "a" and "href" in attrs_dict:
            self._in_link = True
            self._link_text = ""
            self._link_attrs = attrs_dict
            self._link_line = self.getpos()[0]
            self._link_has_img = False
            self._link_img_alt = None
            self.stats["total_links"] += 1

        if tag == "img" and self._in_link:
            self._link_has_img = True
            self._link_img_alt = attrs_dict.get("alt", None)

    def handle_data(self, data):
        if self._in_link:
            self._link_text += data

    def handle_endtag(self, tag):
        if tag != "a" or not self._in_link:
            return

        self._in_link = False
        text = self._link_text.strip()
        href = self._link_attrs.get("href", "")
        aria_label = self._link_attrs.get("aria-label", "")
        title = self._link_attrs.get("title", "")
        line = self._link_line

        # Skip anchors and javascript
        if href.startswith("#") or href.startswith("javascript:"):
            return

        accessible_name = text or aria_label

        # Empty link
        if not accessible_name and not self._link_has_img:
            self.stats["issues"] += 1
            self.issues.append({
                "line": line, "href": href, "severity": "error",
                "issue": "Empty link — no text content",
                "fix": "Add descriptive text or aria-label"
            })
            return

        # Image-only link without alt
        if not text and self._link_has_img:
            if not self._link_img_alt:
                self.stats["issues"] += 1
                self.issues.append({
                    "line": line, "href": href, "severity": "error",
                    "issue": "Image-only link with no alt text",
                    "fix": "Add alt text to the image describing the link destination"
                })
                return
            accessible_name = self._link_img_alt

        # Vague link text
        if accessible_name:
            for pattern in VAGUE_LINK_PATTERNS:
                if pattern.match(accessible_name):
                    self.stats["issues"] += 1
                    self.issues.append({
                        "line": line, "href": href, "severity": "warning",
                        "issue": f'Vague link text: "{accessible_name}"',
                        "fix": "Use descriptive text that makes sense out of context "
                               "(screen readers list all links on a page)"
                    })
                    return

        # Title used as only source of info
        if not text and not aria_label and title:
            self.stats["issues"] += 1
            self.issues.append({
                "line": line, "href": href, "severity": "warning",
                "issue": f'Link relies on title attribute only: "{title}"',
                "fix": "Title is not reliably announced — add visible text or aria-label"
            })
            return

        self.stats["good"] += 1


def audit_file(filepath):
    with open(filepath, "r", encoding="utf-8", errors="replace") as f:
        content = f.read()
    auditor = LinkAuditor()
    auditor.feed(content)
    return auditor.issues, auditor.stats


def main():
    parser = argparse.ArgumentParser(
        description="Audit link text for screen reader accessibility."
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
        issues, stats = audit_file(filepath)
        all_results[filepath] = {"issues": issues, "stats": stats}
        total_issues += len(issues)

    if args.format == "json":
        print(json.dumps(all_results, indent=2))
    else:
        for filepath, result in all_results.items():
            stats = result["stats"]
            issues = result["issues"]
            print(f"\n{'='*60}")
            print(f"  {filepath}")
            print(f"  Links: {stats['total_links']}  Good: {stats['good']}  "
                  f"Issues: {stats['issues']}")
            print(f"{'='*60}")
            for issue in issues:
                icon = {"error": "ERR", "warning": "WRN"}[issue["severity"]]
                print(f"  [{icon}] Line {issue['line']}: {issue['issue']}")
                print(f"        href: {issue['href']}")
                print(f"        fix: {issue['fix']}")
            if not issues:
                print("  No issues found.")
            print()

    sys.exit(1 if total_issues > 0 else 0)


if __name__ == "__main__":
    main()
