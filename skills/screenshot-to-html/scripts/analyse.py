#!/usr/bin/env python3
"""
analyse.py — Sample UI colors and detect layout bounds from a product screenshot.

Usage:
    python3 analyse.py <image_path>

Output:
    JSON with sampled colors, suggested crop bounds, and detected accent colors.
"""

import sys
import json
import numpy as np
from PIL import Image, ImageEnhance
from collections import defaultdict


def hex_color(px):
    return "#{:02x}{:02x}{:02x}".format(int(px[0]), int(px[1]), int(px[2]))


def brightness(px):
    return int(px[0]) + int(px[1]) + int(px[2])


def is_blue(px):
    r, g, b = int(px[0]), int(px[1]), int(px[2])
    return b > 80 and b > r + 20 and b > g + 10

def is_amber(px):
    r, g, b = int(px[0]), int(px[1]), int(px[2])
    return r > 160 and g > 120 and b < 60

def is_green(px):
    r, g, b = int(px[0]), int(px[1]), int(px[2])
    return g > 150 and g > r + 40 and b < 100

def is_red(px):
    r, g, b = int(px[0]), int(px[1]), int(px[2])
    return r > 140 and g < 80 and b < 80


def detect_sidebar_width(arr):
    """Detect sidebar by finding where the main content background starts."""
    h, w = arr.shape[:2]
    # Sample a vertical strip and look for a color shift
    mid_y = h // 2
    bg = arr[mid_y, w // 2]
    for x in range(0, min(300, w)):
        px = arr[mid_y, x]
        if abs(int(px[0]) - int(bg[0])) > 15:
            continue
        # Check if it's been consistent for 10px
        if x > 10:
            strip = arr[mid_y, max(0,x-10):x]
            diffs = [abs(int(p[0]) - int(bg[0])) for p in strip]
            if all(d < 15 for d in diffs):
                return x
    return 0


def detect_topbar_height(arr):
    """Detect top bar height by finding where it ends."""
    h, w = arr.shape[:2]
    mid_x = w // 2
    bg = arr[h // 2, mid_x]
    for y in range(0, min(100, h)):
        px = arr[y, mid_x]
        if brightness(px) > 200:  # bright pixel = likely topbar text/icon
            continue
        if y > 10:
            return y
    return 44  # sensible default


def sample_region_colors(arr, y1, y2, x1, x2, step=8):
    """Find all non-trivially-dark colors in a region."""
    colors = defaultdict(int)
    for y in range(y1, y2, step):
        for x in range(x1, x2, step):
            px = arr[y, x]
            b = brightness(px)
            if b > 120:
                colors[hex_color(px)] += 1
    return sorted(colors.items(), key=lambda kv: -kv[1])


def find_accent_colors(arr, y1, y2, x1, x2):
    """Scan region for blue, amber, green, red accent pixels."""
    accents = {"blue": None, "amber": None, "green": None, "red": None}
    for y in range(y1, y2, 2):
        for x in range(x1, x2, 2):
            px = arr[y, x]
            if accents["blue"] is None and is_blue(px):
                accents["blue"] = hex_color(px)
            if accents["amber"] is None and is_amber(px):
                accents["amber"] = hex_color(px)
            if accents["green"] is None and is_green(px):
                accents["green"] = hex_color(px)
            if accents["red"] is None and is_red(px):
                accents["red"] = hex_color(px)
        if all(v is not None for v in accents.values()):
            break
    return accents


def main():
    if len(sys.argv) < 2:
        print("Usage: python3 analyse.py <image_path>", file=sys.stderr)
        sys.exit(1)

    path = sys.argv[1]
    img = Image.open(path)
    arr = np.array(img).astype(int)
    h, w = arr.shape[:2]

    result = {}

    # Image dimensions
    result["dimensions"] = {"width": w, "height": h}

    # Detect chrome (sidebar + topbar)
    sidebar_w = detect_sidebar_width(arr)
    topbar_h = detect_topbar_height(arr)
    result["suggested_crop"] = {
        "left": sidebar_w,
        "top": topbar_h,
        "right": w - 18,   # trim scrollbar
        "bottom": h - 10,
        "note": "Adjust right/bottom if scrollbar or footer chrome is visible"
    }

    # Sample main background color
    # Use a point well inside the content area
    cx, cy = (sidebar_w + w) // 2, (topbar_h + h) // 2
    bg_px = arr[cy, cx]
    result["colors"] = {}
    result["colors"]["bg"] = hex_color(bg_px)

    # Panel color — slightly different from bg, scan for subtle variation
    # Sample at 20% in from sidebar
    panel_x = sidebar_w + (w - sidebar_w) // 5
    panel_y = topbar_h + 60
    result["colors"]["bg_panel"] = hex_color(arr[panel_y, panel_x])

    # Text — find near-white pixels (headings)
    bright_cols = sample_region_colors(arr, topbar_h, topbar_h + 200, sidebar_w, w, step=4)
    text_candidates = [c for c, n in bright_cols if all(int(c[i:i+2], 16) > 200 for i in (1,3,5))]
    result["colors"]["text_primary"] = text_candidates[0] if text_candidates else "#e2e0eb"

    # Secondary text — medium brightness
    mid_candidates = [c for c, n in bright_cols if 100 < max(int(c[i:i+2],16) for i in (1,3,5)) < 180]
    result["colors"]["text_secondary"] = mid_candidates[0] if mid_candidates else "#9090a0"

    # Accent colors — scan full content area
    accents = find_accent_colors(arr, topbar_h, h, sidebar_w, w)
    result["colors"].update(accents)

    # Border color (estimate from bg)
    bg_r = int(bg_px[0])
    border_r = min(255, bg_r + 20)
    result["colors"]["border"] = f"rgba({border_r},{border_r},{border_r+4},0.08)"
    result["colors"]["grey_track"] = f"#{max(0,bg_r+25):02x}{max(0,bg_r+25):02x}{max(0,bg_r+28):02x}"

    # Tag background estimates (based on accent colors)
    def accent_bg(hex_col, alpha=0.15):
        if hex_col is None:
            return None
        r = int(hex_col[1:3], 16)
        g = int(hex_col[3:5], 16)
        b = int(hex_col[5:7], 16)
        return f"rgba({r},{g},{b},{alpha})"

    result["colors"]["tag_blue_bg"]  = accent_bg(accents.get("blue"),  0.20)
    result["colors"]["tag_amber_bg"] = accent_bg(accents.get("amber"), 0.14)
    result["colors"]["tag_green_bg"] = accent_bg(accents.get("green"), 0.14)
    result["colors"]["tag_red_bg"]   = accent_bg(accents.get("red"),   0.14)

    # Summary guidance
    result["guidance"] = {
        "css_variables": "Use result['colors'] values directly in :root CSS variables.",
        "bar_chart": "Calculate bar height as: value / max_value * chart_height_px. Keep labels outside overflow:hidden container.",
        "presentation_frame": f"Use accent color '{accents.get('blue', '#375788')}' for the radial glow behind the dashboard.",
        "crop": f"Remove sidebar (~{sidebar_w}px) and topbar (~{topbar_h}px) for clean marketing crop."
    }

    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
