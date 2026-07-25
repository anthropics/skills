#!/usr/bin/env python3
"""WCAG 2.2 Color Contrast Checker.

Checks foreground/background color pairs against WCAG 2.2 contrast ratio
thresholds for normal text, large text, and UI components. Supports hex,
rgb(), and named CSS colors.

Usage:
    python contrast_checker.py "#ffffff" "#000000"
    python contrast_checker.py --suggest "#336699"
    python contrast_checker.py --batch styles.css
    python contrast_checker.py --demo
"""

import argparse
import json
import re
import sys

# ---------------------------------------------------------------------------
# Named CSS colors (25 common ones)
# ---------------------------------------------------------------------------
NAMED_COLORS = {
    "black": (0, 0, 0),
    "white": (255, 255, 255),
    "red": (255, 0, 0),
    "green": (0, 128, 0),
    "blue": (0, 0, 255),
    "yellow": (255, 255, 0),
    "cyan": (0, 255, 255),
    "magenta": (255, 0, 255),
    "gray": (128, 128, 128),
    "grey": (128, 128, 128),
    "orange": (255, 165, 0),
    "purple": (128, 0, 128),
    "pink": (255, 192, 203),
    "brown": (165, 42, 42),
    "navy": (0, 0, 128),
    "teal": (0, 128, 128),
    "olive": (128, 128, 0),
    "maroon": (128, 0, 0),
    "lime": (0, 255, 0),
    "aqua": (0, 255, 255),
    "silver": (192, 192, 192),
    "gold": (255, 215, 0),
    "coral": (255, 127, 80),
    "salmon": (250, 128, 114),
    "tomato": (255, 99, 71),
}

# WCAG thresholds: (label, required_ratio)
WCAG_THRESHOLDS = [
    ("AA Normal Text", 4.5),
    ("AA Large Text", 3.0),
    ("AA UI Components", 3.0),
    ("AAA Normal Text", 7.0),
    ("AAA Large Text", 4.5),
]


# ---------------------------------------------------------------------------
# Color parsing
# ---------------------------------------------------------------------------
def parse_color(color_str: str) -> tuple:
    """Parse a color string into an (R, G, B) tuple.

    Accepts:
      - #RRGGBB or #RGB hex
      - rgb(r, g, b)  with values 0-255
      - Named CSS colors
    """
    s = color_str.strip().lower()

    # Named color
    if s in NAMED_COLORS:
        return NAMED_COLORS[s]

    # Hex: #RGB or #RRGGBB
    hex_match = re.match(r"^#([0-9a-f]{3}|[0-9a-f]{6})$", s)
    if hex_match:
        h = hex_match.group(1)
        if len(h) == 3:
            r, g, b = int(h[0] * 2, 16), int(h[1] * 2, 16), int(h[2] * 2, 16)
        else:
            r, g, b = int(h[0:2], 16), int(h[2:4], 16), int(h[4:6], 16)
        return (r, g, b)

    # rgb(r, g, b)
    rgb_match = re.match(r"^rgb\(\s*(\d{1,3})\s*,\s*(\d{1,3})\s*,\s*(\d{1,3})\s*\)$", s)
    if rgb_match:
        r, g, b = int(rgb_match.group(1)), int(rgb_match.group(2)), int(rgb_match.group(3))
        if not all(0 <= c <= 255 for c in (r, g, b)):
            raise ValueError(f"RGB values must be 0-255, got rgb({r},{g},{b})")
        return (r, g, b)

    raise ValueError(
        f"Invalid color format: '{color_str}'. "
        "Use #RRGGBB, #RGB, rgb(r,g,b), or a named color."
    )


def color_to_hex(rgb: tuple) -> str:
    """Convert an (R, G, B) tuple to #RRGGBB."""
    return f"#{rgb[0]:02x}{rgb[1]:02x}{rgb[2]:02x}"


# ---------------------------------------------------------------------------
# WCAG luminance and contrast
# ---------------------------------------------------------------------------
def relative_luminance(rgb: tuple) -> float:
    """Calculate relative luminance per WCAG 2.2 (sRGB).

    https://www.w3.org/TR/WCAG22/#dfn-relative-luminance
    """
    channels = []
    for c in rgb:
        s = c / 255.0
        channels.append(s / 12.92 if s <= 0.04045 else ((s + 0.055) / 1.055) ** 2.4)
    return 0.2126 * channels[0] + 0.7152 * channels[1] + 0.0722 * channels[2]


def contrast_ratio(rgb1: tuple, rgb2: tuple) -> float:
    """Return the WCAG contrast ratio between two colors (>= 1.0)."""
    l1 = relative_luminance(rgb1)
    l2 = relative_luminance(rgb2)
    lighter = max(l1, l2)
    darker = min(l1, l2)
    return (lighter + 0.05) / (darker + 0.05)


def evaluate_contrast(ratio: float) -> list:
    """Return pass/fail results for each WCAG threshold."""
    results = []
    for label, threshold in WCAG_THRESHOLDS:
        results.append({
            "level": label,
            "required": threshold,
            "ratio": round(ratio, 2),
            "pass": ratio >= threshold,
        })
    return results


# ---------------------------------------------------------------------------
# Suggest accessible backgrounds
# ---------------------------------------------------------------------------
def suggest_backgrounds(fg_rgb: tuple, target_ratio: float = 4.5, count: int = 8) -> list:
    """Given a foreground color, suggest background colors passing AA normal text.

    Strategy: walk luminance in both directions (lighter / darker) from the
    foreground and collect the first colors that meet the target ratio.
    """
    suggestions = []

    # Try a spread of grays and tinted variants
    candidates = []
    for v in range(0, 256, 1):
        candidates.append((v, v, v))  # grays

    # Also try tinted versions toward the complement
    fr, fg, fb = fg_rgb
    for v in range(0, 256, 2):
        candidates.append((v, min(255, v + 20), min(255, v + 40)))
        candidates.append((min(255, v + 40), v, min(255, v + 20)))
        candidates.append((min(255, v + 20), min(255, v + 40), v))

    seen = set()
    scored = []
    for c in candidates:
        cr = contrast_ratio(fg_rgb, c)
        if cr >= target_ratio and c not in seen:
            seen.add(c)
            scored.append((cr, c))

    # Sort by ratio closest to target (prefer minimal-change backgrounds)
    scored.sort(key=lambda x: x[0])
    for cr, c in scored[:count]:
        suggestions.append({"hex": color_to_hex(c), "rgb": list(c), "ratio": round(cr, 2)})
    return suggestions


# ---------------------------------------------------------------------------
# Batch CSS parsing
# ---------------------------------------------------------------------------
_COLOR_RE = re.compile(
    r"(#[0-9a-fA-F]{3,6}|rgb\(\s*\d{1,3}\s*,\s*\d{1,3}\s*,\s*\d{1,3}\s*\))"
)


def extract_css_pairs(css_text: str) -> list:
    """Extract color / background-color pairs from CSS declarations.

    Returns a list of dicts with selector, foreground, and background strings.
    """
    pairs = []
    # Split into rule blocks
    block_re = re.compile(r"([^{}]+)\{([^}]+)\}", re.DOTALL)
    for m in block_re.finditer(css_text):
        selector = m.group(1).strip()
        body = m.group(2)

        fg = bg = None
        # Match color: ... (but not background-color)
        fg_match = re.search(
            r"(?<![-])color\s*:\s*([^;]+);", body, re.IGNORECASE
        )
        bg_match = re.search(
            r"background(?:-color)?\s*:\s*([^;]+);", body, re.IGNORECASE
        )

        if fg_match:
            val = fg_match.group(1).strip()
            c = _COLOR_RE.search(val)
            if c:
                fg = c.group(1)
            elif val.lower() in NAMED_COLORS:
                fg = val.lower()

        if bg_match:
            val = bg_match.group(1).strip()
            c = _COLOR_RE.search(val)
            if c:
                bg = c.group(1)
            elif val.lower() in NAMED_COLORS:
                bg = val.lower()

        if fg and bg:
            pairs.append({"selector": selector, "foreground": fg, "background": bg})

    return pairs


# ---------------------------------------------------------------------------
# Output formatting
# ---------------------------------------------------------------------------
def format_result_human(fg_str: str, bg_str: str, ratio: float, results: list) -> str:
    """Format a contrast check result for the terminal."""
    lines = [
        f"Foreground : {fg_str}",
        f"Background : {bg_str}",
        f"Contrast   : {ratio:.2f}:1",
        "",
    ]
    for r in results:
        status = "PASS" if r["pass"] else "FAIL"
        lines.append(f"  [{status}] {r['level']:20s}  (requires {r['required']}:1)")
    return "\n".join(lines)


def format_suggestions_human(fg_str: str, suggestions: list) -> str:
    """Format suggested backgrounds for the terminal."""
    lines = [f"Foreground: {fg_str}", "Suggested accessible backgrounds (AA Normal Text):"]
    if not suggestions:
        lines.append("  No suggestions found.")
    for s in suggestions:
        lines.append(f"  {s['hex']}  ratio={s['ratio']}:1")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Demo
# ---------------------------------------------------------------------------
DEMO_PAIRS = [
    ("#ffffff", "#000000"),
    ("#336699", "#ffffff"),
    ("#ff6600", "#ffffff"),
    ("navy", "white"),
    ("rgb(100,100,100)", "#eeeeee"),
]


def run_demo(as_json: bool) -> None:
    """Run demo checks and print results."""
    all_results = []
    for fg_str, bg_str in DEMO_PAIRS:
        fg_rgb = parse_color(fg_str)
        bg_rgb = parse_color(bg_str)
        ratio = contrast_ratio(fg_rgb, bg_rgb)
        results = evaluate_contrast(ratio)
        entry = {
            "foreground": fg_str,
            "background": bg_str,
            "foreground_hex": color_to_hex(fg_rgb),
            "background_hex": color_to_hex(bg_rgb),
            "ratio": round(ratio, 2),
            "results": results,
        }
        all_results.append(entry)

    if as_json:
        print(json.dumps({"demo": True, "checks": all_results}, indent=2))
    else:
        print("=" * 60)
        print("WCAG 2.2 Contrast Checker - Demo")
        print("=" * 60)
        for entry in all_results:
            print()
            print(
                format_result_human(
                    entry["foreground"], entry["background"],
                    entry["ratio"], entry["results"],
                )
            )
        print()
        print("-" * 60)
        print("Suggestion demo for foreground #336699:")
        suggestions = suggest_backgrounds(parse_color("#336699"))
        print(format_suggestions_human("#336699", suggestions))


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------
def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="WCAG 2.2 Color Contrast Checker. "
        "Checks foreground/background pairs against AA and AAA thresholds.",
        epilog="Examples:\n"
        "  %(prog)s '#ffffff' '#000000'\n"
        "  %(prog)s --suggest '#336699'\n"
        "  %(prog)s --batch styles.css\n"
        "  %(prog)s --demo\n",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument(
        "foreground",
        nargs="?",
        help="Foreground (text) color: #RRGGBB, #RGB, rgb(r,g,b), or named color",
    )
    parser.add_argument(
        "background",
        nargs="?",
        help="Background color: #RRGGBB, #RGB, rgb(r,g,b), or named color",
    )
    parser.add_argument(
        "--suggest",
        metavar="COLOR",
        help="Suggest accessible background colors for the given foreground color",
    )
    parser.add_argument(
        "--batch",
        metavar="CSS_FILE",
        help="Extract color pairs from a CSS file and check each",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        dest="json_output",
        help="Output results as JSON",
    )
    parser.add_argument(
        "--demo",
        action="store_true",
        help="Show example output with sample color pairs",
    )
    parser.add_argument(
        "--sample",
        action="store_true",
        help="Run with embedded sample color pairs (alias for --demo)",
    )
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()

    # --demo / --sample mode
    if args.demo or args.sample:
        run_demo(args.json_output)
        return 0

    # --suggest mode
    if args.suggest:
        try:
            fg_rgb = parse_color(args.suggest)
        except ValueError as exc:
            print(f"Error: {exc}", file=sys.stderr)
            return 1

        suggestions = suggest_backgrounds(fg_rgb)
        if args.json_output:
            print(json.dumps({
                "foreground": args.suggest,
                "foreground_hex": color_to_hex(fg_rgb),
                "suggestions": suggestions,
            }, indent=2))
        else:
            print(format_suggestions_human(args.suggest, suggestions))
        return 0

    # --batch mode
    if args.batch:
        try:
            with open(args.batch, "r", encoding="utf-8") as fh:
                css_text = fh.read()
        except FileNotFoundError:
            print(f"Error: file not found: {args.batch}", file=sys.stderr)
            return 1
        except OSError as exc:
            print(f"Error reading file: {exc}", file=sys.stderr)
            return 1

        pairs = extract_css_pairs(css_text)
        if not pairs:
            msg = "No color/background-color pairs found in the CSS file."
            if args.json_output:
                print(json.dumps({"batch": args.batch, "pairs": [], "message": msg}, indent=2))
            else:
                print(msg)
            return 0

        all_results = []
        has_failure = False
        for pair in pairs:
            try:
                fg_rgb = parse_color(pair["foreground"])
                bg_rgb = parse_color(pair["background"])
            except ValueError as exc:
                entry = {
                    "selector": pair["selector"],
                    "foreground": pair["foreground"],
                    "background": pair["background"],
                    "error": str(exc),
                }
                all_results.append(entry)
                continue

            ratio = contrast_ratio(fg_rgb, bg_rgb)
            results = evaluate_contrast(ratio)
            if not results[0]["pass"]:  # AA Normal Text
                has_failure = True
            entry = {
                "selector": pair["selector"],
                "foreground": pair["foreground"],
                "background": pair["background"],
                "foreground_hex": color_to_hex(fg_rgb),
                "background_hex": color_to_hex(bg_rgb),
                "ratio": round(ratio, 2),
                "results": results,
            }
            all_results.append(entry)

        if args.json_output:
            print(json.dumps({"batch": args.batch, "pairs": all_results}, indent=2))
        else:
            print(f"Batch check: {args.batch}")
            print("=" * 60)
            for entry in all_results:
                print(f"\nSelector: {entry['selector']}")
                if "error" in entry:
                    print(f"  Error: {entry['error']}")
                else:
                    print(
                        format_result_human(
                            entry["foreground"], entry["background"],
                            entry["ratio"], entry["results"],
                        )
                    )
            print()
            summary_pass = sum(1 for e in all_results if "ratio" in e and e["results"][0]["pass"])
            summary_total = sum(1 for e in all_results if "ratio" in e)
            print(f"Summary: {summary_pass}/{summary_total} pairs pass AA Normal Text")

        return 1 if has_failure else 0

    # Default: check a single pair
    if not args.foreground or not args.background:
        parser.error(
            "Provide foreground and background colors, or use --suggest, --batch, or --demo."
        )

    try:
        fg_rgb = parse_color(args.foreground)
    except ValueError as exc:
        print(f"Error (foreground): {exc}", file=sys.stderr)
        return 1

    try:
        bg_rgb = parse_color(args.background)
    except ValueError as exc:
        print(f"Error (background): {exc}", file=sys.stderr)
        return 1

    ratio = contrast_ratio(fg_rgb, bg_rgb)
    results = evaluate_contrast(ratio)

    if args.json_output:
        print(json.dumps({
            "foreground": args.foreground,
            "background": args.background,
            "foreground_hex": color_to_hex(fg_rgb),
            "background_hex": color_to_hex(bg_rgb),
            "ratio": round(ratio, 2),
            "results": results,
        }, indent=2))
    else:
        print(format_result_human(args.foreground, args.background, ratio, results))

    return 0 if results[0]["pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
