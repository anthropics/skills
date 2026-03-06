#!/usr/bin/env python3
"""
WCAG Contrast Ratio Checker

Calculate contrast ratios between two colors and check WCAG 2.1 compliance.
Uses the W3C relative luminance formula. No dependencies — stdlib only.

Usage:
    python3 contrast-checker.py "#ffffff" "#000000"
    python3 contrast-checker.py --fg "#333333" --bg "#f5f5f5"
    python3 contrast-checker.py --help
"""

import argparse
import sys


def hex_to_rgb(hex_color: str) -> tuple[int, int, int]:
    """Convert hex color string to RGB tuple."""
    hex_color = hex_color.lstrip("#")
    if len(hex_color) == 3:
        hex_color = "".join(c * 2 for c in hex_color)
    if len(hex_color) != 6:
        raise ValueError(f"Invalid hex color: #{hex_color}")
    return (
        int(hex_color[0:2], 16),
        int(hex_color[2:4], 16),
        int(hex_color[4:6], 16),
    )


def relative_luminance(r: int, g: int, b: int) -> float:
    """
    Calculate relative luminance per WCAG 2.1.
    https://www.w3.org/TR/WCAG21/#dfn-relative-luminance
    """

    def linearize(c: int) -> float:
        s = c / 255.0
        return s / 12.92 if s <= 0.04045 else ((s + 0.055) / 1.055) ** 2.4

    return 0.2126 * linearize(r) + 0.7152 * linearize(g) + 0.0722 * linearize(b)


def contrast_ratio(color1: str, color2: str) -> float:
    """
    Calculate contrast ratio between two hex colors.
    Returns a value between 1.0 (no contrast) and 21.0 (max contrast).
    """
    l1 = relative_luminance(*hex_to_rgb(color1))
    l2 = relative_luminance(*hex_to_rgb(color2))
    lighter = max(l1, l2)
    darker = min(l1, l2)
    return (lighter + 0.05) / (darker + 0.05)


def check_wcag(ratio: float) -> dict:
    """Check WCAG 2.1 compliance at various levels."""
    return {
        "normal_text_aa": ratio >= 4.5,       # Level AA, normal text
        "normal_text_aaa": ratio >= 7.0,      # Level AAA, normal text
        "large_text_aa": ratio >= 3.0,        # Level AA, large text (18px+ or 14px+ bold)
        "large_text_aaa": ratio >= 4.5,       # Level AAA, large text
        "ui_components_aa": ratio >= 3.0,     # Level AA, UI components and graphics
    }


def main():
    parser = argparse.ArgumentParser(
        description="Check WCAG 2.1 contrast ratio between two colors."
    )
    parser.add_argument(
        "colors",
        nargs="*",
        help="Two hex colors (e.g., '#ffffff' '#000000')",
    )
    parser.add_argument("--fg", help="Foreground (text) color in hex")
    parser.add_argument("--bg", help="Background color in hex")

    args = parser.parse_args()

    if args.fg and args.bg:
        fg, bg = args.fg, args.bg
    elif len(args.colors) == 2:
        fg, bg = args.colors
    else:
        parser.print_help()
        sys.exit(1)

    try:
        ratio = contrast_ratio(fg, bg)
    except ValueError as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)

    results = check_wcag(ratio)

    print(f"\nForeground: {fg}")
    print(f"Background: {bg}")
    print(f"Contrast Ratio: {ratio:.2f}:1\n")

    def status(passed: bool) -> str:
        return "PASS" if passed else "FAIL"

    print(f"  Normal text (AA  >= 4.5:1):  {status(results['normal_text_aa'])}")
    print(f"  Normal text (AAA >= 7.0:1):  {status(results['normal_text_aaa'])}")
    print(f"  Large text  (AA  >= 3.0:1):  {status(results['large_text_aa'])}")
    print(f"  Large text  (AAA >= 4.5:1):  {status(results['large_text_aaa'])}")
    print(f"  UI components (AA >= 3.0:1): {status(results['ui_components_aa'])}")
    print()

    if not results["normal_text_aa"]:
        print("Suggestion: Increase contrast by darkening the text or lightening the background.")


if __name__ == "__main__":
    main()
