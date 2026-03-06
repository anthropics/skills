#!/usr/bin/env python3
"""
Alt Text Audit

Scan HTML files for missing, empty, or low-quality alt text on images.
Flags: missing alt attributes, empty alt on non-decorative images,
suspicious alt text ("image", "photo", "untitled", filename patterns).

No dependencies — stdlib only.

Usage:
    python3 alt-text-audit.py index.html
    python3 alt-text-audit.py src/**/*.html
    python3 alt-text-audit.py --format json page.html
"""

import argparse
import json
import os
import re
import sys
from html.parser import HTMLParser


SUSPICIOUS_PATTERNS = [
    re.compile(r'^image\s*\d*$', re.I),
    re.compile(r'^photo\s*\d*$', re.I),
    re.compile(r'^img\s*\d*$', re.I),
    re.compile(r'^picture\s*\d*$', re.I),
    re.compile(r'^untitled', re.I),
    re.compile(r'^screenshot', re.I),
    re.compile(r'^DSC[_\d]', re.I),
    re.compile(r'^IMG[_\d]', re.I),
    re.compile(r'\.(jpe?g|png|gif|webp|svg|bmp)$', re.I),
    re.compile(r'^https?://', re.I),
    re.compile(r'^\s*$'),
]


class ImageAuditor(HTMLParser):
    def __init__(self):
        super().__init__()
        self.issues = []
        self.stats = {"total_images": 0, "missing_alt": 0, "empty_alt": 0,
                      "suspicious_alt": 0, "decorative": 0, "good": 0}
        self._line = 1

    def handle_starttag(self, tag, attrs):
        if tag != "img":
            return

        self.stats["total_images"] += 1
        attrs_dict = dict(attrs)
        line = self.getpos()[0]
        src = attrs_dict.get("src", "(no src)")

        if "alt" not in attrs_dict:
            self.stats["missing_alt"] += 1
            self.issues.append({
                "line": line, "src": src, "severity": "error",
                "issue": "Missing alt attribute",
                "fix": 'Add alt="description" or alt="" if decorative'
            })
            return

        alt = attrs_dict["alt"]

        if alt == "":
            role = attrs_dict.get("role", "")
            aria_hidden = attrs_dict.get("aria-hidden", "")
            if role == "presentation" or aria_hidden == "true":
                self.stats["decorative"] += 1
                return
            # Empty alt without explicit decorative markers — might be intentional
            self.stats["empty_alt"] += 1
            self.issues.append({
                "line": line, "src": src, "severity": "warning",
                "issue": "Empty alt text without role='presentation'",
                "fix": "If decorative, add role='presentation'. If meaningful, add description."
            })
            return

        for pattern in SUSPICIOUS_PATTERNS:
            if pattern.search(alt):
                self.stats["suspicious_alt"] += 1
                self.issues.append({
                    "line": line, "src": src, "severity": "warning",
                    "issue": f'Suspicious alt text: "{alt}"',
                    "fix": "Replace with a meaningful description of the image content"
                })
                return

        if len(alt) > 300:
            self.issues.append({
                "line": line, "src": src, "severity": "info",
                "issue": f"Alt text is very long ({len(alt)} chars)",
                "fix": "Consider using aria-describedby for long descriptions"
            })

        self.stats["good"] += 1


def audit_file(filepath):
    with open(filepath, "r", encoding="utf-8", errors="replace") as f:
        content = f.read()

    auditor = ImageAuditor()
    auditor.feed(content)
    return auditor.issues, auditor.stats


def main():
    parser = argparse.ArgumentParser(
        description="Audit HTML files for alt text accessibility issues."
    )
    parser.add_argument("files", nargs="+", help="HTML files to audit")
    parser.add_argument("--format", choices=["text", "json"], default="text",
                        help="Output format (default: text)")
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
            print(f"  Images: {stats['total_images']}  Good: {stats['good']}  "
                  f"Decorative: {stats['decorative']}")
            print(f"  Missing: {stats['missing_alt']}  Empty: {stats['empty_alt']}  "
                  f"Suspicious: {stats['suspicious_alt']}")
            print(f"{'='*60}")
            for issue in issues:
                icon = {"error": "ERR", "warning": "WRN", "info": "INF"}[issue["severity"]]
                print(f"  [{icon}] Line {issue['line']}: {issue['issue']}")
                print(f"        src: {issue['src']}")
                print(f"        fix: {issue['fix']}")
            if not issues:
                print("  No issues found.")
            print()

    sys.exit(1 if total_issues > 0 else 0)


if __name__ == "__main__":
    main()
