#!/usr/bin/env python3
"""brand_palette_validator.py - Validate brand HEX colors + derive 12-token palette.

Stdlib-only. Validates the brand primary + optional accent/bg/text the user supplies
during onboarding, then derives the full 12-CSS-custom-property palette consumed by
every markdown-html converter (md-document, md-review, md-slides).

Pipeline:
  1. Parse + verify each HEX is well-formed
  2. WCAG 2.2 contrast checks (text-on-bg, accent-on-bg, link-on-bg)
  3. Derive missing tokens algorithmically (lighten/darken in HSL, hue-shift for accent)
  4. Emit the 12-token palette as a JSON dict ready to inject into onboard.py config

Forked from marketing/landing/skills/landing/scripts/brand_palette_validator.py
(WCAG math + HSL color manipulation + derive_palette shape) and adapted: 12 tokens
instead of 8, document-reading focus (longer reading sessions → tighter contrast
floors), no "card" semantics, dedicated --md-link / --md-link-hover / --md-success
/ --md-warn / --md-code-bg tokens for document/review/slides use cases.

NO LLM CALLS. Pure color-math + WCAG formula.

Usage:
    python brand_palette_validator.py --primary "#0A1628" --accent "#00D4AA" --output json
    python brand_palette_validator.py --primary "#FF6B35" --output human
    python brand_palette_validator.py --sample
"""

from __future__ import annotations

import argparse
import colorsys
import json
import re
import sys
from typing import Any

HEX_RE = re.compile(r"^#?([0-9a-fA-F]{6})$")


def parse_hex(hex_str: str) -> tuple[int, int, int]:
    m = HEX_RE.match(hex_str.strip())
    if not m:
        raise ValueError(f"Invalid HEX '{hex_str}'. Expected #RRGGBB or RRGGBB (6 hex chars).")
    h = m.group(1)
    return (int(h[0:2], 16), int(h[2:4], 16), int(h[4:6], 16))


def rgb_to_hex(rgb: tuple[int, int, int]) -> str:
    return "#{:02X}{:02X}{:02X}".format(*rgb)


def relative_luminance(rgb: tuple[int, int, int]) -> float:
    """Per WCAG 2.2 — sRGB-linearized luminance."""
    def linearize(channel: int) -> float:
        c = channel / 255.0
        return c / 12.92 if c <= 0.03928 else ((c + 0.055) / 1.055) ** 2.4
    r, g, b = rgb
    return 0.2126 * linearize(r) + 0.7152 * linearize(g) + 0.0722 * linearize(b)


def contrast_ratio(rgb1: tuple[int, int, int], rgb2: tuple[int, int, int]) -> float:
    l1 = relative_luminance(rgb1)
    l2 = relative_luminance(rgb2)
    lighter, darker = max(l1, l2), min(l1, l2)
    return (lighter + 0.05) / (darker + 0.05)


def lighten_hsl(rgb: tuple[int, int, int], pct: float) -> tuple[int, int, int]:
    r, g, b = (c / 255.0 for c in rgb)
    h, l, s = colorsys.rgb_to_hls(r, g, b)
    l = min(1.0, max(0.0, l + pct))
    r2, g2, b2 = colorsys.hls_to_rgb(h, l, s)
    return (int(r2 * 255), int(g2 * 255), int(b2 * 255))


def darken_hsl(rgb: tuple[int, int, int], pct: float) -> tuple[int, int, int]:
    return lighten_hsl(rgb, -pct)


def shift_hue(rgb: tuple[int, int, int], degrees: float) -> tuple[int, int, int]:
    r, g, b = (c / 255.0 for c in rgb)
    h, l, s = colorsys.rgb_to_hls(r, g, b)
    h = (h + degrees / 360.0) % 1.0
    r2, g2, b2 = colorsys.hls_to_rgb(h, l, s)
    return (int(r2 * 255), int(g2 * 255), int(b2 * 255))


def rgba_str(rgb: tuple[int, int, int], alpha: float) -> str:
    return f"rgba({rgb[0]}, {rgb[1]}, {rgb[2]}, {alpha})"


def is_dark(rgb: tuple[int, int, int]) -> bool:
    return relative_luminance(rgb) < 0.18


def _ensure_link_contrast(
    link: tuple[int, int, int],
    bg: tuple[int, int, int],
    target: float = 4.5,
) -> tuple[int, int, int]:
    """Iteratively adjust link luminance toward the target contrast on bg.

    Documents have long reading sessions and lots of links — the WCAG AA
    4.5:1 floor matters. Walk the luminance up or down (depending on which
    direction increases contrast) until we hit the target or saturate.
    """
    bg_lum = relative_luminance(bg)
    # If bg is dark we lighten the link; if bg is light we darken it.
    step = 0.04 if bg_lum < 0.5 else -0.04
    result = link
    for _ in range(20):
        if contrast_ratio(result, bg) >= target:
            return result
        nxt = lighten_hsl(result, step)
        if nxt == result:
            break
        result = nxt
    return result


def derive_palette(
    primary: tuple[int, int, int],
    accent: tuple[int, int, int] | None = None,
    bg: tuple[int, int, int] | None = None,
    text: tuple[int, int, int] | None = None,
) -> dict[str, str]:
    """Derive the 12-token --md-* palette from a partial input.

    Interpretation rule: `primary` is the user's *brand-identity* color
    (CTA / accent / link emphasis), not necessarily the background. Three
    branches based on primary luminance:

    1. **Dark primary** (luminance < 0.18, e.g. navy #0A1628): assume the
       user wants a dark-themed document — bg = primary, text = off-white,
       accent = a hue-shifted lighter derivative.
    2. **Light/vibrant primary** (luminance ≥ 0.18, e.g. orange #FF6B35):
       use a near-neutral document bg (#FAFAFA with a hint of primary hue
       for warmth), text = near-black, accent = primary itself.
    3. **Explicit overrides** (bg, text supplied by user) win unconditionally.

    Link contrast on bg is then iteratively enforced to WCAG AA 4.5:1 by
    walking link luminance toward the target. Documents have long reading
    sessions and lots of links — the floor matters.
    """
    # Resolve bg first (it anchors every other contrast decision)
    if bg is None:
        if is_dark(primary):
            bg = primary
        else:
            # Near-neutral light document bg with a faint warmth from primary's hue
            r, g, b = (c / 255.0 for c in primary)
            h, _, _ = colorsys.rgb_to_hls(r, g, b)
            r2, g2, b2 = colorsys.hls_to_rgb(h, 0.97, 0.04)
            bg = (int(r2 * 255), int(g2 * 255), int(b2 * 255))

    if text is None:
        text = (247, 247, 242) if is_dark(bg) else (16, 24, 32)

    if accent is None:
        if is_dark(primary):
            accent = lighten_hsl(shift_hue(primary, 160), 0.45)
        else:
            accent = primary

    surface = lighten_hsl(bg, 0.06 if is_dark(bg) else -0.03)
    border = lighten_hsl(bg, 0.12 if is_dark(bg) else -0.08)
    text_muted = rgba_str(text, 0.68)
    accent_soft = rgba_str(accent, 0.14)
    code_bg = lighten_hsl(bg, 0.04 if is_dark(bg) else -0.04)

    link = _ensure_link_contrast(accent, bg, target=4.5)
    link_hover = lighten_hsl(link, 0.08 if is_dark(bg) else -0.06)
    # Success/warn derived from fixed hue anchors (green-ish / amber-ish), then
    # luminance-matched to bg so they remain readable as inline labels.
    green = (16, 168, 92)
    amber = (200, 124, 16)
    success = green if is_dark(bg) else darken_hsl(green, 0.08)
    warn = amber if is_dark(bg) else darken_hsl(amber, 0.04)

    return {
        "--md-bg":          rgb_to_hex(bg),
        "--md-surface":     rgb_to_hex(surface),
        "--md-border":      rgb_to_hex(border),
        "--md-text":        rgb_to_hex(text),
        "--md-text-muted":  text_muted,
        "--md-accent":      rgb_to_hex(accent),
        "--md-accent-soft": accent_soft,
        "--md-code-bg":     rgb_to_hex(code_bg),
        "--md-link":        rgb_to_hex(link),
        "--md-link-hover":  rgb_to_hex(link_hover),
        "--md-success":     rgb_to_hex(success),
        "--md-warn":        rgb_to_hex(warn),
    }


def validate(
    primary: str,
    accent: str | None = None,
    bg: str | None = None,
    text: str | None = None,
) -> dict[str, Any]:
    findings: list[dict[str, str]] = []

    def add(rule: str, level: str, message: str) -> None:
        findings.append({"rule": rule, "level": level, "message": message})

    try:
        primary_rgb = parse_hex(primary)
        add("primary-hex", "PASS", f"Primary parsed: {primary} = RGB{primary_rgb}")
    except ValueError as e:
        add("primary-hex", "FAIL", str(e))
        return finalize(findings, {})

    accent_rgb: tuple[int, int, int] | None = None
    if accent:
        try:
            accent_rgb = parse_hex(accent)
            add("accent-hex", "PASS", f"Accent parsed: {accent} = RGB{accent_rgb}")
        except ValueError as e:
            add("accent-hex", "FAIL", str(e))
            return finalize(findings, {})

    bg_rgb: tuple[int, int, int] | None = None
    if bg:
        try:
            bg_rgb = parse_hex(bg)
            add("bg-hex", "PASS", f"Bg parsed: {bg} = RGB{bg_rgb}")
        except ValueError as e:
            add("bg-hex", "FAIL", str(e))
            return finalize(findings, {})

    text_rgb: tuple[int, int, int] | None = None
    if text:
        try:
            text_rgb = parse_hex(text)
            add("text-hex", "PASS", f"Text parsed: {text} = RGB{text_rgb}")
        except ValueError as e:
            add("text-hex", "FAIL", str(e))
            return finalize(findings, {})

    palette = derive_palette(primary_rgb, accent_rgb, bg_rgb, text_rgb)

    bg_final = parse_hex(palette["--md-bg"])
    text_final = parse_hex(palette["--md-text"])
    accent_final = parse_hex(palette["--md-accent"])
    link_final = parse_hex(palette["--md-link"])

    text_on_bg = contrast_ratio(text_final, bg_final)
    accent_on_bg = contrast_ratio(accent_final, bg_final)
    link_on_bg = contrast_ratio(link_final, bg_final)

    add(
        "wcag-text-on-bg",
        "PASS" if text_on_bg >= 4.5 else ("WARN" if text_on_bg >= 3.0 else "FAIL"),
        f"Body text on bg contrast: {text_on_bg:.2f}:1 (need 4.5:1 for body, WCAG AA)",
    )
    add(
        "wcag-accent-on-bg",
        "PASS" if accent_on_bg >= 3.0 else "WARN",
        f"Accent (UI/CTA) on bg contrast: {accent_on_bg:.2f}:1 (need 3:1 for non-text UI)",
    )
    add(
        "wcag-link-on-bg",
        "PASS" if link_on_bg >= 4.5 else ("WARN" if link_on_bg >= 3.0 else "FAIL"),
        f"Link on bg contrast: {link_on_bg:.2f}:1 (need 4.5:1, links are body-text-equivalent)",
    )

    return finalize(findings, palette)


def finalize(findings: list[dict[str, str]], palette: dict[str, str]) -> dict[str, Any]:
    counts = {"PASS": 0, "WARN": 0, "FAIL": 0}
    for f in findings:
        counts[f["level"]] = counts.get(f["level"], 0) + 1
    if counts["FAIL"] > 0:
        verdict = "FAIL"
    elif counts["WARN"] > 0:
        verdict = "WARN"
    else:
        verdict = "PASS"
    return {"verdict": verdict, "counts": counts, "findings": findings, "derived_palette": palette}


def render_human(result: dict[str, Any]) -> str:
    out: list[str] = []
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
        out.append("Derived 12-token palette (use in :root CSS):")
        for k, v in result["derived_palette"].items():
            out.append(f"  {k:<20s} {v}")
    return "\n".join(out)


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--primary", help="Primary HEX color (e.g., #0A1628)")
    parser.add_argument("--accent", help="Accent HEX color (optional; derived if missing)")
    parser.add_argument("--bg", help="Background HEX color (optional; derived if missing)")
    parser.add_argument("--text", help="Text HEX color (optional; derived if missing)")
    parser.add_argument("--sample", action="store_true", help="Validate built-in sample palette")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    if args.sample:
        result = validate("#0A1628", "#00D4AA")
    elif args.primary:
        result = validate(args.primary, args.accent, args.bg, args.text)
    else:
        parser.print_help()
        return 0

    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_human(result))
    return 0 if result["verdict"] != "FAIL" else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
