#!/usr/bin/env python3
"""
Timing and Auto-Advancing Content Audit

Scan HTML and inline JavaScript for timing patterns that may be accessibility
barriers: setTimeout, setInterval, CSS animations, auto-playing media,
meta refresh, and marquee elements.

WCAG 2.2.1 (Level A): Timing Adjustable — users must be able to turn off,
adjust, or extend time limits.
WCAG 2.2.2 (Level A): Pause, Stop, Hide — auto-updating content must have
pause/stop/hide controls.

No dependencies — stdlib only.

Usage:
    python3 timing-audit.py index.html
    python3 timing-audit.py --format json page.html
    python3 timing-audit.py app.js script.js
"""

import argparse
import json
import os
import re
import sys


TIMING_PATTERNS = [
    {
        "pattern": re.compile(r'setTimeout\s*\(', re.I),
        "severity": "info",
        "issue": "setTimeout detected",
        "fix": "Ensure this doesn't create a time limit. If it does, provide a way "
               "to extend or disable the timeout.",
    },
    {
        "pattern": re.compile(r'setInterval\s*\(', re.I),
        "severity": "warning",
        "issue": "setInterval detected (auto-advancing content)",
        "fix": "Auto-updating content needs pause/stop controls (WCAG 2.2.2). "
               "Provide a visible pause button.",
    },
    {
        "pattern": re.compile(r'autoplay', re.I),
        "severity": "warning",
        "issue": "Autoplay attribute detected",
        "fix": "Auto-playing media should have visible pause/stop controls. "
               "Consider removing autoplay or adding muted attribute for video.",
    },
    {
        "pattern": re.compile(r'<meta[^>]*http-equiv\s*=\s*["\']refresh["\']', re.I),
        "severity": "error",
        "issue": "Meta refresh / auto-redirect detected",
        "fix": "Automatic page redirects violate WCAG 2.2.1. Use server-side "
               "redirects or provide a manual link.",
    },
    {
        "pattern": re.compile(r'<marquee', re.I),
        "severity": "error",
        "issue": "<marquee> element detected",
        "fix": "Marquee is deprecated and inaccessible. Use CSS animation with "
               "prefers-reduced-motion support and a pause button.",
    },
    {
        "pattern": re.compile(r'animation-duration|animation-name|@keyframes', re.I),
        "severity": "info",
        "issue": "CSS animation detected",
        "fix": "Wrap in @media (prefers-reduced-motion: reduce) to disable for "
               "users who prefer reduced motion.",
    },
    {
        "pattern": re.compile(r'transition-duration|transition:', re.I),
        "severity": "info",
        "issue": "CSS transition detected",
        "fix": "Set transition-duration: 0.01ms in prefers-reduced-motion media query.",
    },
    {
        "pattern": re.compile(r'\.carousel|\.slider|\.slideshow|swiper', re.I),
        "severity": "warning",
        "issue": "Carousel/slider pattern detected",
        "fix": "Auto-advancing carousels need: pause button, keyboard controls, "
               "aria-live region for slide changes.",
    },
    {
        "pattern": re.compile(r'requestAnimationFrame\s*\(', re.I),
        "severity": "info",
        "issue": "requestAnimationFrame detected",
        "fix": "Continuous animations should check prefers-reduced-motion and provide "
               "a way to pause.",
    },
    {
        "pattern": re.compile(r'\.scrollIntoView|scroll-behavior:\s*smooth', re.I),
        "severity": "info",
        "issue": "Smooth scrolling detected",
        "fix": "Smooth scrolling should respect prefers-reduced-motion. Use "
               "scroll-behavior: auto as fallback.",
    },
]


def audit_file(filepath):
    with open(filepath, "r", encoding="utf-8", errors="replace") as f:
        lines = f.readlines()

    issues = []
    has_reduced_motion = False

    for i, line_content in enumerate(lines, 1):
        if "prefers-reduced-motion" in line_content:
            has_reduced_motion = True

        for tp in TIMING_PATTERNS:
            if tp["pattern"].search(line_content):
                issues.append({
                    "line": i,
                    "severity": tp["severity"],
                    "issue": tp["issue"],
                    "fix": tp["fix"],
                    "code": line_content.strip()[:80],
                })

    # Check if animations exist but no reduced motion support
    has_animations = any(
        i["issue"].startswith("CSS animation") or i["issue"].startswith("CSS transition")
        for i in issues
    )
    if has_animations and not has_reduced_motion:
        issues.insert(0, {
            "line": 0,
            "severity": "error",
            "issue": "Animations/transitions found but no prefers-reduced-motion support",
            "fix": "Add @media (prefers-reduced-motion: reduce) { ... } to disable "
                   "animations for users who need it",
            "code": "",
        })

    return issues, has_reduced_motion


def main():
    parser = argparse.ArgumentParser(
        description="Audit HTML/JS/CSS for timing and animation accessibility issues."
    )
    parser.add_argument("files", nargs="+", help="Files to audit (HTML, JS, CSS)")
    parser.add_argument("--format", choices=["text", "json"], default="text")
    args = parser.parse_args()

    all_results = {}
    total_issues = 0

    for filepath in args.files:
        if not os.path.isfile(filepath):
            print(f"Warning: {filepath} not found, skipping", file=sys.stderr)
            continue
        issues, has_reduced_motion = audit_file(filepath)
        all_results[filepath] = {
            "issues": issues,
            "has_reduced_motion_support": has_reduced_motion
        }
        total_issues += len(issues)

    if args.format == "json":
        print(json.dumps(all_results, indent=2))
    else:
        for filepath, result in all_results.items():
            issues = result["issues"]
            motion = "Yes" if result["has_reduced_motion_support"] else "No"
            print(f"\n{'='*60}")
            print(f"  {filepath} — Timing & Animation Audit")
            print(f"  Potential issues: {len(issues)}  "
                  f"prefers-reduced-motion: {motion}")
            print(f"{'='*60}")
            for issue in issues:
                icon = {"error": "ERR", "warning": "WRN", "info": "INF"}[issue["severity"]]
                print(f"  [{icon}] Line {issue['line']}: {issue['issue']}")
                if issue["code"]:
                    print(f"        code: {issue['code']}")
                print(f"        fix: {issue['fix']}")
            if not issues:
                print("  No timing issues detected.")
            print()

    sys.exit(1 if total_issues > 0 else 0)


if __name__ == "__main__":
    main()
