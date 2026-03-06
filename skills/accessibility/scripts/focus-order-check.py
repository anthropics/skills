#!/usr/bin/env python3
"""
Focus Order Checker

Extract all focusable/interactive elements from HTML and flag focus order issues:
positive tabindex values (bad practice), missing tabindex on custom interactive
elements, and elements with tabindex > 0 that override natural DOM order.

No dependencies — stdlib only.

Usage:
    python3 focus-order-check.py index.html
    python3 focus-order-check.py --format json page.html
"""

import argparse
import json
import os
import re
import sys
from html.parser import HTMLParser


# Elements that are natively focusable
FOCUSABLE_ELEMENTS = {
    "a", "button", "input", "select", "textarea", "details", "summary"
}

# ARIA roles that imply interactivity
INTERACTIVE_ROLES = {
    "button", "link", "checkbox", "radio", "tab", "menuitem",
    "menuitemcheckbox", "menuitemradio", "option", "switch",
    "slider", "spinbutton", "textbox", "combobox", "searchbox",
    "listbox", "grid", "gridcell", "tree", "treeitem",
}


class FocusOrderExtractor(HTMLParser):
    def __init__(self):
        super().__init__()
        self.elements = []
        self.issues = []

    def handle_starttag(self, tag, attrs):
        attrs_dict = dict(attrs)
        line = self.getpos()[0]
        role = attrs_dict.get("role", "")
        tabindex = attrs_dict.get("tabindex", None)
        disabled = "disabled" in attrs_dict
        aria_disabled = attrs_dict.get("aria-disabled", "") == "true"
        aria_hidden = attrs_dict.get("aria-hidden", "") == "true"

        is_native_focusable = tag in FOCUSABLE_ELEMENTS
        is_interactive_role = role in INTERACTIVE_ROLES
        has_click = any(k.startswith("on") for k in attrs_dict)
        has_tabindex = tabindex is not None

        if not (is_native_focusable or is_interactive_role or has_tabindex or has_click):
            return

        # Build description
        desc_parts = [f"<{tag}"]
        if role:
            desc_parts.append(f'role="{role}"')
        if has_tabindex:
            desc_parts.append(f'tabindex="{tabindex}"')
        text_hint = attrs_dict.get("aria-label", "") or attrs_dict.get("id", "") or \
                    attrs_dict.get("name", "") or attrs_dict.get("class", "")
        if text_hint:
            desc_parts.append(f'({text_hint[:30]})')
        desc = " ".join(desc_parts) + ">"

        self.elements.append({
            "line": line,
            "tag": tag,
            "role": role,
            "tabindex": int(tabindex) if tabindex is not None else None,
            "disabled": disabled or aria_disabled,
            "aria_hidden": aria_hidden,
            "description": desc,
        })

    def analyze(self):
        for el in self.elements:
            # Positive tabindex
            if el["tabindex"] is not None and el["tabindex"] > 0:
                self.issues.append({
                    "line": el["line"], "severity": "error",
                    "element": el["description"],
                    "issue": f"Positive tabindex ({el['tabindex']}) overrides natural DOM order",
                    "fix": "Use tabindex='0' to add to natural order, or restructure DOM. "
                           "Positive tabindex creates unpredictable focus order."
                })

            # Interactive role without focusability
            if el["role"] in INTERACTIVE_ROLES and el["tag"] not in FOCUSABLE_ELEMENTS:
                if el["tabindex"] is None:
                    self.issues.append({
                        "line": el["line"], "severity": "error",
                        "element": el["description"],
                        "issue": f"Interactive role '{el['role']}' on non-focusable <{el['tag']}>",
                        "fix": f"Add tabindex='0' or use a native <button>/<a> instead"
                    })

            # Click handler on non-focusable without tabindex
            if el["tag"] not in FOCUSABLE_ELEMENTS and el["tabindex"] is None and \
               not el["role"]:
                self.issues.append({
                    "line": el["line"], "severity": "warning",
                    "element": el["description"],
                    "issue": "Event handler on non-focusable element without tabindex or role",
                    "fix": "Use a <button> element, or add tabindex='0' and role='button'"
                })

            # aria-hidden on focusable
            if el["aria_hidden"] and el["tabindex"] != -1:
                self.issues.append({
                    "line": el["line"], "severity": "error",
                    "element": el["description"],
                    "issue": "Focusable element is aria-hidden='true'",
                    "fix": "Hidden elements must not be focusable. Add tabindex='-1' or "
                           "remove aria-hidden."
                })


def audit_file(filepath):
    with open(filepath, "r", encoding="utf-8", errors="replace") as f:
        content = f.read()
    extractor = FocusOrderExtractor()
    extractor.feed(content)
    extractor.analyze()
    return extractor.elements, extractor.issues


def main():
    parser = argparse.ArgumentParser(
        description="Check focus order and interactive element accessibility."
    )
    parser.add_argument("files", nargs="+", help="HTML files to check")
    parser.add_argument("--format", choices=["text", "json"], default="text")
    parser.add_argument("--show-all", action="store_true",
                        help="Show all focusable elements, not just issues")
    args = parser.parse_args()

    all_results = {}
    total_issues = 0

    for filepath in args.files:
        if not os.path.isfile(filepath):
            print(f"Warning: {filepath} not found, skipping", file=sys.stderr)
            continue
        elements, issues = audit_file(filepath)
        all_results[filepath] = {"elements": elements, "issues": issues}
        total_issues += len(issues)

    if args.format == "json":
        print(json.dumps(all_results, indent=2))
    else:
        for filepath, result in all_results.items():
            elements = result["elements"]
            issues = result["issues"]
            print(f"\n{'='*60}")
            print(f"  {filepath} — Focus Order Check")
            print(f"  Interactive elements: {len(elements)}  Issues: {len(issues)}")
            print(f"{'='*60}")

            if args.show_all:
                print("\n  Focus order (DOM order):")
                for i, el in enumerate(elements, 1):
                    ti = f"tabindex={el['tabindex']}" if el["tabindex"] is not None else "natural"
                    flag = " DISABLED" if el["disabled"] else ""
                    flag += " HIDDEN" if el["aria_hidden"] else ""
                    print(f"  {i:3}. Line {el['line']:4} {el['description']}  [{ti}]{flag}")

            if issues:
                print(f"\n  Issues ({len(issues)}):")
                for issue in issues:
                    icon = {"error": "ERR", "warning": "WRN"}[issue["severity"]]
                    print(f"    [{icon}] Line {issue['line']}: {issue['issue']}")
                    print(f"          {issue['element']}")
                    print(f"          {issue['fix']}")
            else:
                print("\n  No issues found.")
            print()

    sys.exit(1 if total_issues > 0 else 0)


if __name__ == "__main__":
    main()
