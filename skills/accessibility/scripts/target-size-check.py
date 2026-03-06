#!/usr/bin/env python3
"""
Target Size Checker

Scan HTML and inline CSS for interactive elements that may be undersized.
Checks for explicit width/height values on buttons, links, inputs, and
elements with interactive ARIA roles.

WCAG 2.5.8 (Level AA): 24x24px minimum
WCAG 2.5.5 (Level AAA): 44x44px minimum
Mobile best practice: 48x48px minimum

No dependencies — stdlib only.

Usage:
    python3 target-size-check.py index.html
    python3 target-size-check.py --threshold 44 page.html
    python3 target-size-check.py --format json page.html
"""

import argparse
import json
import os
import re
import sys
from html.parser import HTMLParser


INTERACTIVE_TAGS = {"a", "button", "input", "select", "textarea", "summary"}
INTERACTIVE_ROLES = {
    "button", "link", "checkbox", "radio", "tab", "menuitem",
    "switch", "slider", "option", "combobox",
}


def parse_px(value: str) -> float:
    """Extract pixel value from CSS value string."""
    match = re.match(r'(\d+(?:\.\d+)?)\s*px', value.strip())
    return float(match.group(1)) if match else -1


class TargetSizeChecker(HTMLParser):
    def __init__(self, threshold=24):
        super().__init__()
        self.threshold = threshold
        self.elements = []
        self.issues = []

    def handle_starttag(self, tag, attrs):
        attrs_dict = dict(attrs)
        role = attrs_dict.get("role", "")
        line = self.getpos()[0]

        is_interactive = tag in INTERACTIVE_TAGS or role in INTERACTIVE_ROLES
        if not is_interactive:
            return

        # Check inline style for width/height
        style = attrs_dict.get("style", "")
        width = -1
        height = -1

        if style:
            w_match = re.search(r'(?:min-)?width:\s*(\d+(?:\.\d+)?px)', style)
            h_match = re.search(r'(?:min-)?height:\s*(\d+(?:\.\d+)?px)', style)
            if w_match:
                width = parse_px(w_match.group(1))
            if h_match:
                height = parse_px(h_match.group(1))

        # Check explicit width/height attributes
        if "width" in attrs_dict:
            w = parse_px(attrs_dict["width"] + "px")
            if w > 0:
                width = w
        if "height" in attrs_dict:
            h = parse_px(attrs_dict["height"] + "px")
            if h > 0:
                height = h

        # Check size attribute on inputs
        if tag == "input":
            input_type = attrs_dict.get("type", "text")
            if input_type in ("checkbox", "radio") and width < 0:
                # Default browser checkbox/radio is ~13x13px — likely undersized
                self.issues.append({
                    "line": line, "severity": "warning",
                    "element": f'<input type="{input_type}">',
                    "issue": f"Default {input_type} is ~13x13px (below {self.threshold}px)",
                    "fix": f"Style with min-width/min-height: {self.threshold}px, "
                           f"or wrap in a <label> with adequate padding"
                })
                return

        # Build description
        desc = f"<{tag}"
        if role:
            desc += f' role="{role}"'
        ident = attrs_dict.get("id", "") or attrs_dict.get("class", "")[:25]
        if ident:
            desc += f" ({ident})"
        desc += ">"

        element = {
            "line": line, "tag": tag, "role": role,
            "width": width, "height": height,
            "description": desc,
        }
        self.elements.append(element)

        # Flag undersized if we can detect it
        if width > 0 and width < self.threshold:
            self.issues.append({
                "line": line, "severity": "warning",
                "element": desc,
                "issue": f"Width {width}px is below {self.threshold}px minimum",
                "fix": f"Set min-width: {self.threshold}px (48px for mobile)"
            })
        if height > 0 and height < self.threshold:
            self.issues.append({
                "line": line, "severity": "warning",
                "element": desc,
                "issue": f"Height {height}px is below {self.threshold}px minimum",
                "fix": f"Set min-height: {self.threshold}px (48px for mobile)"
            })


def audit_file(filepath, threshold):
    with open(filepath, "r", encoding="utf-8", errors="replace") as f:
        content = f.read()
    checker = TargetSizeChecker(threshold)
    checker.feed(content)
    return checker.elements, checker.issues


def main():
    parser = argparse.ArgumentParser(
        description="Check interactive element target sizes for WCAG compliance."
    )
    parser.add_argument("files", nargs="+", help="HTML files to check")
    parser.add_argument("--threshold", type=int, default=24,
                        help="Minimum size in px (default: 24 for WCAG AA, 44 for AAA)")
    parser.add_argument("--format", choices=["text", "json"], default="text")
    args = parser.parse_args()

    all_results = {}
    total_issues = 0

    for filepath in args.files:
        if not os.path.isfile(filepath):
            print(f"Warning: {filepath} not found, skipping", file=sys.stderr)
            continue
        elements, issues = audit_file(filepath, args.threshold)
        all_results[filepath] = {
            "elements": len(elements), "issues": issues,
            "threshold": args.threshold
        }
        total_issues += len(issues)

    if args.format == "json":
        print(json.dumps(all_results, indent=2))
    else:
        for filepath, result in all_results.items():
            issues = result["issues"]
            print(f"\n{'='*60}")
            print(f"  {filepath} — Target Size Check ({result['threshold']}px threshold)")
            print(f"  Interactive elements: {result['elements']}  Issues: {len(issues)}")
            print(f"{'='*60}")
            for issue in issues:
                icon = {"error": "ERR", "warning": "WRN"}[issue["severity"]]
                print(f"  [{icon}] Line {issue['line']}: {issue['issue']}")
                print(f"        {issue['element']}")
                print(f"        fix: {issue['fix']}")
            if not issues:
                print("  No issues detected.")
                print("  Note: This tool only checks inline styles and HTML attributes.")
                print("  External CSS sizing is not detected — test manually or with")
                print("  browser DevTools (inspect element > computed size).")
            print()

    sys.exit(1 if total_issues > 0 else 0)


if __name__ == "__main__":
    main()
