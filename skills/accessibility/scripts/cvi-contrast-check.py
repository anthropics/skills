#!/usr/bin/env python3
"""
CVI and Low Vision Contrast Checker

Check color pairs against specialized contrast requirements for:
- CVI (Cortical Visual Impairment): needs very high contrast, yellow-on-black preferred
- Low vision: needs enhanced contrast (WCAG AAA: 7:1)
- Photophobia: needs muted, low-brightness combinations

Extends the standard WCAG contrast checker with clinical guidance.

No dependencies — stdlib only.

Usage:
    python3 cvi-contrast-check.py "#ffff00" "#000000"
    python3 cvi-contrast-check.py --preset cvi
    python3 cvi-contrast-check.py --preset photophobia
    python3 cvi-contrast-check.py --check-theme theme.css
"""

import argparse
import json
import re
import sys


def hex_to_rgb(hex_color: str) -> tuple:
    hex_color = hex_color.lstrip("#")
    if len(hex_color) == 3:
        hex_color = "".join(c * 2 for c in hex_color)
    if len(hex_color) != 6:
        raise ValueError(f"Invalid hex color: #{hex_color}")
    return (int(hex_color[0:2], 16), int(hex_color[2:4], 16), int(hex_color[4:6], 16))


def relative_luminance(r: int, g: int, b: int) -> float:
    def linearize(c):
        s = c / 255.0
        return s / 12.92 if s <= 0.04045 else ((s + 0.055) / 1.055) ** 2.4
    return 0.2126 * linearize(r) + 0.7152 * linearize(g) + 0.0722 * linearize(b)


def contrast_ratio(color1: str, color2: str) -> float:
    l1 = relative_luminance(*hex_to_rgb(color1))
    l2 = relative_luminance(*hex_to_rgb(color2))
    lighter = max(l1, l2)
    darker = min(l1, l2)
    return (lighter + 0.05) / (darker + 0.05)


def brightness(hex_color: str) -> float:
    """Perceived brightness (0-255) using ITU-R BT.601."""
    r, g, b = hex_to_rgb(hex_color)
    return 0.299 * r + 0.587 * g + 0.114 * b


CVI_PRESETS = {
    "cvi": {
        "name": "CVI (Cortical Visual Impairment)",
        "description": "High contrast with preferred CVI color combinations",
        "pairs": [
            ("#ffff00", "#000000", "Yellow on black (primary CVI choice)"),
            ("#ffffff", "#000000", "White on black"),
            ("#00ffff", "#000000", "Cyan on black"),
            ("#ff0000", "#000000", "Red on black (high salience)"),
            ("#ffff00", "#0000aa", "Yellow on dark blue"),
        ],
        "min_ratio": 10.0,
        "guidance": [
            "CVI users need very high contrast (10:1+ recommended)",
            "Yellow on black is the most commonly preferred combination",
            "Limit displays to 3-5 items — visual clutter is a major barrier",
            "Use solid backgrounds — no gradients, patterns, or background images",
            "Large, bold text with generous spacing",
        ]
    },
    "photophobia": {
        "name": "Photophobia / Light Sensitivity",
        "description": "Low-brightness combinations that reduce eye strain",
        "pairs": [
            ("#8b949e", "#0d1117", "Muted gray on very dark (GitHub Dark)"),
            ("#c9d1d9", "#161b22", "Light gray on dark background"),
            ("#4a6fa5", "#0d1117", "Muted blue on very dark"),
            ("#a0a0a0", "#1a1a2e", "Gray on dark navy"),
            ("#b0b0b0", "#121212", "Soft gray on near-black"),
        ],
        "min_ratio": 4.5,
        "guidance": [
            "Avoid pure white (#ffffff) backgrounds — maximum ~85% brightness",
            "Keep text brightness moderate — not pure white either",
            "Avoid saturated colors — use muted, desaturated tones",
            "Provide a dark mode or low-light theme option",
            "Never auto-flash or pulse UI elements",
        ]
    },
    "deuteranopia": {
        "name": "Deuteranopia (Red-Green Color Blindness)",
        "description": "Safe color pairs for the most common color blindness (~8% of males)",
        "pairs": [
            ("#0077bb", "#ffffff", "Blue on white (safe primary)"),
            ("#ff8c00", "#000000", "Orange on black (instead of green)"),
            ("#ffff00", "#000000", "Yellow on black"),
            ("#0077bb", "#ff8c00", "Blue vs orange (safe differentiator)"),
            ("#ffffff", "#cc3311", "White on red-orange (distinguishable)"),
        ],
        "min_ratio": 4.5,
        "guidance": [
            "Never use red/green as the only differentiator",
            "Blue and orange are safe primary differentiators",
            "Always pair color with icons, patterns, or text labels",
            "Test with a deuteranopia simulator (Chrome DevTools > Rendering)",
        ]
    }
}


def check_pair(fg: str, bg: str, label: str = "") -> dict:
    ratio = contrast_ratio(fg, bg)
    fg_bright = brightness(fg)
    bg_bright = brightness(bg)

    return {
        "fg": fg, "bg": bg, "label": label,
        "ratio": round(ratio, 2),
        "fg_brightness": round(fg_bright, 1),
        "bg_brightness": round(bg_bright, 1),
        "wcag_aa": ratio >= 4.5,
        "wcag_aaa": ratio >= 7.0,
        "cvi_safe": ratio >= 10.0,
    }


def extract_colors_from_css(filepath: str) -> list:
    """Extract color pairs from CSS custom properties or common patterns."""
    with open(filepath, "r", encoding="utf-8", errors="replace") as f:
        content = f.read()

    hex_pattern = re.compile(r'#(?:[0-9a-fA-F]{3}){1,2}')
    colors = list(set(hex_pattern.findall(content)))
    return colors


def main():
    parser = argparse.ArgumentParser(
        description="Check color contrast for CVI, low vision, and color blindness."
    )
    parser.add_argument("colors", nargs="*", help="Two hex colors (fg bg)")
    parser.add_argument("--preset", choices=list(CVI_PRESETS.keys()),
                        help="Check a preset color scheme")
    parser.add_argument("--check-theme", help="Extract and check colors from a CSS file")
    parser.add_argument("--format", choices=["text", "json"], default="text")
    args = parser.parse_args()

    results = []

    if args.preset:
        preset = CVI_PRESETS[args.preset]
        for fg, bg, label in preset["pairs"]:
            results.append(check_pair(fg, bg, label))

        if args.format == "json":
            print(json.dumps({"preset": preset["name"], "results": results,
                              "guidance": preset["guidance"]}, indent=2))
        else:
            print(f"\n  {preset['name']}")
            print(f"  {preset['description']}")
            print(f"  Minimum recommended ratio: {preset['min_ratio']}:1")
            print(f"  {'='*56}")
            for r in results:
                status = "PASS" if r["ratio"] >= preset["min_ratio"] else "FAIL"
                print(f"  [{status}] {r['ratio']:5.1f}:1  {r['fg']} on {r['bg']}"
                      f"  — {r['label']}")
            print(f"\n  Guidance:")
            for tip in preset["guidance"]:
                print(f"    - {tip}")
            print()

    elif len(args.colors) == 2:
        fg, bg = args.colors
        result = check_pair(fg, bg)
        if args.format == "json":
            print(json.dumps(result, indent=2))
        else:
            print(f"\n  Foreground: {fg} (brightness: {result['fg_brightness']})")
            print(f"  Background: {bg} (brightness: {result['bg_brightness']})")
            print(f"  Contrast Ratio: {result['ratio']}:1\n")
            print(f"    WCAG AA  (4.5:1):  {'PASS' if result['wcag_aa'] else 'FAIL'}")
            print(f"    WCAG AAA (7.0:1):  {'PASS' if result['wcag_aaa'] else 'FAIL'}")
            print(f"    CVI Safe (10:1+):  {'PASS' if result['cvi_safe'] else 'FAIL'}")
            print()

    elif args.check_theme:
        colors = extract_colors_from_css(args.check_theme)
        if len(colors) < 2:
            print("Not enough colors found in file.", file=sys.stderr)
            sys.exit(1)
        print(f"\n  Colors found in {args.check_theme}: {', '.join(colors[:20])}")
        print(f"  Checking all pairs...\n")
        failing = []
        for i, c1 in enumerate(colors):
            for c2 in colors[i+1:]:
                r = check_pair(c1, c2)
                if not r["wcag_aa"]:
                    failing.append(r)
        if failing:
            print(f"  Failing pairs ({len(failing)}):")
            for f in failing[:20]:
                print(f"    {f['ratio']:5.1f}:1  {f['fg']} / {f['bg']}")
        else:
            print("  All color pairs pass WCAG AA.")
        print()

    else:
        parser.print_help()
        sys.exit(1)


if __name__ == "__main__":
    main()
