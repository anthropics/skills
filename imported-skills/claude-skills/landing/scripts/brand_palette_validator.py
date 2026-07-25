#!/usr/bin/env python3
"""brand_palette_validator.py — Validate brand HEX colors + derive full palette.

Stdlib-only. Validates user-provided brand overrides (primary + accent + optional bg)
and:

  1. Confirms each HEX is well-formed
  2. Checks WCAG AA contrast between text and bg
  3. Generates the full derived palette (--*-mid, --*-glow, --text-muted, etc.)
     using algorithmic lighten/darken in HSL space

Used during landing's Phase 0 Q3 (brand overrides) to validate input before
proceeding to generation. If validation FAILs, the skill re-asks Q3 with
specific guidance.

NO LLM CALLS. Pure color-math + WCAG formula.

Usage:
    python brand_palette_validator.py --primary "#FF6B35" --accent "#2EC4B6" --bg "#011627"
    python brand_palette_validator.py --primary "#0A1628" --output json
    python brand_palette_validator.py --sample
"""

import argparse
import colorsys
import json
import re
import sys
from typing import Any, Dict, List, Optional, Tuple


HEX_RE = re.compile(r"^#?([0-9a-fA-F]{6})$")


def parse_hex(hex_str: str) -> Tuple[int, int, int]:
    """Parse #RRGGBB or RRGGBB to (R, G, B) ints 0-255."""
    m = HEX_RE.match(hex_str.strip())
    if not m:
        raise ValueError(f"Invalid HEX '{hex_str}'. Expected #RRGGBB or RRGGBB (6 hex chars).")
    h = m.group(1)
    return (int(h[0:2], 16), int(h[2:4], 16), int(h[4:6], 16))


def rgb_to_hex(rgb: Tuple[int, int, int]) -> str:
    return "#{:02X}{:02X}{:02X}".format(*rgb)


def relative_luminance(rgb: Tuple[int, int, int]) -> float:
    """Per WCAG 2.2 — sRGB-linearized luminance."""
    def linearize(channel: int) -> float:
        c = channel / 255.0
        return c / 12.92 if c <= 0.03928 else ((c + 0.055) / 1.055) ** 2.4
    r, g, b = rgb
    return 0.2126 * linearize(r) + 0.7152 * linearize(g) + 0.0722 * linearize(b)


def contrast_ratio(rgb1: Tuple[int, int, int], rgb2: Tuple[int, int, int]) -> float:
    """WCAG contrast ratio between two colors."""
    l1 = relative_luminance(rgb1)
    l2 = relative_luminance(rgb2)
    lighter, darker = max(l1, l2), min(l1, l2)
    return (lighter + 0.05) / (darker + 0.05)


def lighten_hsl(rgb: Tuple[int, int, int], pct: float) -> Tuple[int, int, int]:
    """Lighten in HSL space by pct (0-1 = 0-100%)."""
    r, g, b = (c / 255.0 for c in rgb)
    h, l, s = colorsys.rgb_to_hls(r, g, b)
    l = min(1.0, l + pct)
    r2, g2, b2 = colorsys.hls_to_rgb(h, l, s)
    return (int(r2 * 255), int(g2 * 255), int(b2 * 255))


def darken_hsl(rgb: Tuple[int, int, int], pct: float) -> Tuple[int, int, int]:
    return lighten_hsl(rgb, -pct)


def shift_hue(rgb: Tuple[int, int, int], degrees: float) -> Tuple[int, int, int]:
    """Rotate hue by degrees (0-360)."""
    r, g, b = (c / 255.0 for c in rgb)
    h, l, s = colorsys.rgb_to_hls(r, g, b)
    h = (h + degrees / 360.0) % 1.0
    r2, g2, b2 = colorsys.hls_to_rgb(h, l, s)
    return (int(r2 * 255), int(g2 * 255), int(b2 * 255))


def rgba_str(rgb: Tuple[int, int, int], alpha: float) -> str:
    return f"rgba({rgb[0]}, {rgb[1]}, {rgb[2]}, {alpha})"


def derive_palette(
    primary: Tuple[int, int, int],
    accent: Optional[Tuple[int, int, int]] = None,
    bg: Optional[Tuple[int, int, int]] = None,
    text: Optional[Tuple[int, int, int]] = None,
) -> Dict[str, str]:
    """Derive the full --* palette from a partial input.

    If accent is None: derive by lighten + saturate (option 1 from brand_system_design.md).
    If bg is None: derive as primary lightened 8% (--navy-mid pattern).
    If text is None: default to off-white (#F7F7F2).
    """
    if accent is None:
        accent = lighten_hsl(primary, 0.3)
    if bg is None:
        bg = lighten_hsl(primary, 0.08)
    if text is None:
        text = (247, 247, 242)  # #F7F7F2

    accent_glow = rgba_str(accent, 0.12)
    card_bg = rgba_str(accent, 0.06)
    card_border = rgba_str(accent, 0.15)
    text_muted = rgba_str(text, 0.68)

    return {
        "--navy":         rgb_to_hex(primary),
        "--navy-mid":     rgb_to_hex(bg),
        "--teal":         rgb_to_hex(accent),
        "--teal-glow":    accent_glow,
        "--off-white":    rgb_to_hex(text),
        "--text-muted":   text_muted,
        "--card-bg":      card_bg,
        "--card-border":  card_border,
    }


def validate(
    primary: str,
    accent: Optional[str] = None,
    bg: Optional[str] = None,
    text: Optional[str] = None,
) -> Dict[str, Any]:
    findings: List[Dict[str, str]] = []

    def add(rule: str, level: str, message: str) -> None:
        findings.append({"rule": rule, "level": level, "message": message})

    # Parse all provided HEX
    try:
        primary_rgb = parse_hex(primary)
        add("primary-hex", "PASS", f"Primary parsed: {primary} = RGB{primary_rgb}")
    except ValueError as e:
        add("primary-hex", "FAIL", str(e))
        return finalize(findings, {})

    accent_rgb = None
    if accent:
        try:
            accent_rgb = parse_hex(accent)
            add("accent-hex", "PASS", f"Accent parsed: {accent} = RGB{accent_rgb}")
        except ValueError as e:
            add("accent-hex", "FAIL", str(e))
            return finalize(findings, {})

    bg_rgb = None
    if bg:
        try:
            bg_rgb = parse_hex(bg)
            add("bg-hex", "PASS", f"Bg parsed: {bg} = RGB{bg_rgb}")
        except ValueError as e:
            add("bg-hex", "FAIL", str(e))
            return finalize(findings, {})

    text_rgb = None
    if text:
        try:
            text_rgb = parse_hex(text)
            add("text-hex", "PASS", f"Text parsed: {text} = RGB{text_rgb}")
        except ValueError as e:
            add("text-hex", "FAIL", str(e))
            return finalize(findings, {})

    # Derive full palette
    palette = derive_palette(primary_rgb, accent_rgb, bg_rgb, text_rgb)

    # WCAG contrast checks
    text_rgb_final = text_rgb or (247, 247, 242)
    bg_rgb_final = bg_rgb or lighten_hsl(primary_rgb, 0.08)
    primary_for_text_check = primary_rgb  # body text on primary bg

    text_on_primary = contrast_ratio(text_rgb_final, primary_for_text_check)
    text_on_bg_mid = contrast_ratio(text_rgb_final, bg_rgb_final)

    add(
        "wcag-text-on-primary",
        "PASS" if text_on_primary >= 4.5 else ("WARN" if text_on_primary >= 3.0 else "FAIL"),
        f"Text on primary bg contrast: {text_on_primary:.2f}:1 (need 4.5:1 body / 3:1 large)",
    )
    add(
        "wcag-text-on-bg-mid",
        "PASS" if text_on_bg_mid >= 4.5 else ("WARN" if text_on_bg_mid >= 3.0 else "FAIL"),
        f"Text on bg-mid contrast: {text_on_bg_mid:.2f}:1 (need 4.5:1 body / 3:1 large)",
    )

    # CTA accent visibility (against primary bg)
    accent_rgb_final = accent_rgb or lighten_hsl(primary_rgb, 0.3)
    accent_on_primary = contrast_ratio(accent_rgb_final, primary_rgb)
    add(
        "wcag-cta-on-primary",
        "PASS" if accent_on_primary >= 3.0 else "WARN",
        f"Accent (CTA bg) on primary bg contrast: {accent_on_primary:.2f}:1 (need 3:1 for CTA visibility)",
    )

    return finalize(findings, palette)


def finalize(findings: List[Dict[str, str]], palette: Dict[str, str]) -> Dict[str, Any]:
    counts = {"PASS": 0, "WARN": 0, "FAIL": 0}
    for f in findings:
        counts[f["level"]] += 1
    if counts["FAIL"] > 0:
        verdict = "FAIL"
    elif counts["WARN"] > 0:
        verdict = "WARN"
    else:
        verdict = "PASS"
    return {"verdict": verdict, "counts": counts, "findings": findings, "derived_palette": palette}


def render_human(result: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append(f"Brand palette validation verdict: {result['verdict']}")
    c = result["counts"]
    out.append(f"  PASS: {c['PASS']}  WARN: {c['WARN']}  FAIL: {c['FAIL']}")
    out.append("")
    out.append("Findings:")
    for f in result["findings"]:
        marker = {"PASS": "[ok]", "WARN": "[warn]", "FAIL": "[FAIL]"}[f["level"]]
        out.append(f"  {marker} {f['rule']}: {f['message']}")
    if result["derived_palette"]:
        out.append("")
        out.append("Derived palette (use in :root CSS):")
        for k, v in result["derived_palette"].items():
            out.append(f"  {k:<18s} {v}")
    return "\n".join(out)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--primary", help="Primary HEX color (e.g., #FF6B35)")
    parser.add_argument("--accent", help="Accent HEX color (optional)")
    parser.add_argument("--bg", help="Background HEX color (optional)")
    parser.add_argument("--text", help="Text HEX color (optional; default #F7F7F2)")
    parser.add_argument("--sample", action="store_true", help="Validate sample palette")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    if args.sample:
        result = validate("#FF6B35", "#2EC4B6", "#011627")
    elif args.primary:
        result = validate(args.primary, args.accent, args.bg, args.text)
    else:
        parser.print_help(); return 0

    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_human(result))
    return 0 if result["verdict"] != "FAIL" else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
