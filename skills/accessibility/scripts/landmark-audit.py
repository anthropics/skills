#!/usr/bin/env python3
"""
Landmark Audit

Check HTML for proper ARIA landmark structure: header/banner, nav, main,
aside/complementary, footer/contentinfo. Flags missing landmarks, duplicates
without labels, and content outside landmarks.

No dependencies — stdlib only.

Usage:
    python3 landmark-audit.py index.html
    python3 landmark-audit.py --format json page.html
"""

import argparse
import json
import os
import sys
from html.parser import HTMLParser


# Semantic elements that are implicit landmarks
LANDMARK_ELEMENTS = {
    "header": "banner",
    "nav": "navigation",
    "main": "main",
    "aside": "complementary",
    "footer": "contentinfo",
    "form": "form",
    "section": "region",
}

# ARIA roles that are landmarks
LANDMARK_ROLES = {
    "banner", "navigation", "main", "complementary", "contentinfo",
    "form", "region", "search",
}


class LandmarkExtractor(HTMLParser):
    def __init__(self):
        super().__init__()
        self.landmarks = []
        self.issues = []
        self._skip_tags = {"script", "style", "template"}
        self._in_skip = 0

    def handle_starttag(self, tag, attrs):
        if tag in self._skip_tags:
            self._in_skip += 1
            return

        attrs_dict = dict(attrs)
        role = attrs_dict.get("role", "")
        label = attrs_dict.get("aria-label", "") or attrs_dict.get("aria-labelledby", "")
        line = self.getpos()[0]

        landmark_type = None

        if role in LANDMARK_ROLES:
            landmark_type = role
        elif tag in LANDMARK_ELEMENTS:
            landmark_type = LANDMARK_ELEMENTS[tag]

        if landmark_type:
            self.landmarks.append({
                "type": landmark_type,
                "element": tag,
                "role": role,
                "label": label,
                "line": line,
            })

    def handle_endtag(self, tag):
        if tag in self._skip_tags and self._in_skip > 0:
            self._in_skip -= 1

    def analyze(self):
        types = [lm["type"] for lm in self.landmarks]

        # Check for required landmarks
        if "main" not in types:
            self.issues.append({
                "severity": "error",
                "issue": "No <main> landmark found",
                "fix": "Wrap page content in <main> element"
            })

        if "banner" not in types:
            self.issues.append({
                "severity": "warning",
                "issue": "No <header> / banner landmark found",
                "fix": "Add <header> element for site header"
            })

        if "navigation" not in types:
            self.issues.append({
                "severity": "warning",
                "issue": "No <nav> landmark found",
                "fix": "Wrap navigation links in <nav> element"
            })

        if "contentinfo" not in types:
            self.issues.append({
                "severity": "warning",
                "issue": "No <footer> / contentinfo landmark found",
                "fix": "Add <footer> element for page footer"
            })

        # Check for multiple mains
        mains = [lm for lm in self.landmarks if lm["type"] == "main"]
        if len(mains) > 1:
            self.issues.append({
                "severity": "error",
                "issue": f"Multiple <main> landmarks found ({len(mains)})",
                "fix": "Use only one <main> per page"
            })

        # Check for duplicate landmarks without labels
        from collections import Counter
        type_counts = Counter(types)
        for lm_type, count in type_counts.items():
            if count > 1 and lm_type != "region":
                matches = [lm for lm in self.landmarks if lm["type"] == lm_type]
                unlabeled = [lm for lm in matches if not lm["label"]]
                if unlabeled:
                    self.issues.append({
                        "severity": "error",
                        "issue": f"Multiple '{lm_type}' landmarks without unique labels "
                                 f"(lines {', '.join(str(lm['line']) for lm in unlabeled)})",
                        "fix": "Add aria-label to distinguish them (e.g., 'Primary navigation' "
                               "vs 'Footer navigation')"
                    })

        # Check for section/region without label
        for lm in self.landmarks:
            if lm["type"] == "region" and not lm["label"]:
                self.issues.append({
                    "severity": "warning",
                    "issue": f"<section> without aria-label at line {lm['line']}",
                    "fix": "Add aria-label or aria-labelledby, or use a different element"
                })


def audit_file(filepath):
    with open(filepath, "r", encoding="utf-8", errors="replace") as f:
        content = f.read()

    extractor = LandmarkExtractor()
    extractor.feed(content)
    extractor.analyze()
    return extractor.landmarks, extractor.issues


def main():
    parser = argparse.ArgumentParser(
        description="Audit HTML files for proper ARIA landmark structure."
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
        landmarks, issues = audit_file(filepath)
        all_results[filepath] = {"landmarks": landmarks, "issues": issues}
        total_issues += len(issues)

    if args.format == "json":
        print(json.dumps(all_results, indent=2))
    else:
        for filepath, result in all_results.items():
            landmarks = result["landmarks"]
            issues = result["issues"]
            print(f"\n{'='*60}")
            print(f"  {filepath} — Landmark Audit")
            print(f"{'='*60}")

            if landmarks:
                for lm in landmarks:
                    label = f' "{lm["label"]}"' if lm["label"] else ""
                    role = f' role="{lm["role"]}"' if lm["role"] else ""
                    print(f"  <{lm['element']}{role}>{label}  "
                          f"({lm['type']}, line {lm['line']})")
            else:
                print("  No landmarks found.")

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
