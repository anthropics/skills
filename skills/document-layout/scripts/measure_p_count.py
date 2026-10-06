#!/usr/bin/env python3
"""
measure_p_count.py - Measure how many capital P's fit on one line.

The 'P-count' method: count how many 'P' characters fit within the
available text width. P is wider than most letters but not as extreme
as M or W, giving a practical safe maximum that balances safety with
usable space.

Character width comparison (Georgia 11pt):
  W: widest  → ultra-conservative limit
  M: wider   → very conservative (wastes ~35% of space)
  P: wide    → practical safe limit (this script)
  e/a/o: avg → what typical text uses
  i/l: narrow → only narrow text reaches this

Uses Pillow to measure the exact pixel width of 'P' in the target font,
then divides the available page width by it.

Usage:
    python measure_p_count.py
    python measure_p_count.py --font "Georgia" --size 11 --indent 620
    python measure_p_count.py --font "Calibri" --size 11 --indent 0
"""

import argparse
import os
import subprocess
from PIL import ImageFont

# A4 dimensions
A4_WIDTH_MM = 210
DEFAULT_MARGIN_MM = 25.4  # 1 inch
DXA_PER_MM = 1440 / 25.4  # ~56.69

# Common font file locations on Ubuntu
FONT_PATHS = {
    "georgia": "/usr/share/fonts/truetype/msttcorefonts/Georgia.ttf",
    "arial": "/usr/share/fonts/truetype/msttcorefonts/Arial.ttf",
    "calibri": "/usr/share/fonts/truetype/vista/calibri.ttf",
    "times new roman": "/usr/share/fonts/truetype/msttcorefonts/Times_New_Roman.ttf",
    "verdana": "/usr/share/fonts/truetype/msttcorefonts/Verdana.ttf",
    "courier new": "/usr/share/fonts/truetype/msttcorefonts/cour.ttf",
    "liberation serif": "/usr/share/fonts/truetype/liberation/LiberationSerif-Regular.ttf",
    "liberation sans": "/usr/share/fonts/truetype/liberation/LiberationSans-Regular.ttf",
    "dejavu sans": "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
    "dejavu serif": "/usr/share/fonts/truetype/dejavu/DejaVuSerif.ttf",
}


def find_font(font_name, size_pt):
    """Try to load the font, falling back to system search."""
    key = font_name.lower()
    if key in FONT_PATHS and os.path.exists(FONT_PATHS[key]):
        return ImageFont.truetype(FONT_PATHS[key], size_pt)

    try:
        result = subprocess.run(
            ["fc-match", "--format=%{file}", font_name],
            capture_output=True, text=True
        )
        if result.returncode == 0 and result.stdout.strip():
            path = result.stdout.strip()
            if os.path.exists(path):
                return ImageFont.truetype(path, size_pt)
    except FileNotFoundError:
        pass

    for root, dirs, files in os.walk('/usr/share/fonts/'):
        for f in files:
            if font_name.lower().replace(' ', '') in f.lower().replace(' ', ''):
                try:
                    return ImageFont.truetype(os.path.join(root, f), size_pt)
                except Exception:
                    continue

    print(f"Warning: Could not find '{font_name}', using default font")
    return ImageFont.load_default()


def measure_p_count(font_name="Georgia", size_pt=11,
                     margin_mm=DEFAULT_MARGIN_MM, indent_dxa=620,
                     page_width_mm=A4_WIDTH_MM):
    """Calculate how many 'P' characters fit on one text line."""
    content_width_mm = page_width_mm - (2 * margin_mm)
    indent_mm = indent_dxa / DXA_PER_MM
    text_width_mm = content_width_mm - indent_mm
    text_width_pt = text_width_mm * (72 / 25.4)

    font = find_font(font_name, size_pt)

    # Measure key characters
    measurements = {}
    for char in ['M', 'W', 'P', 'e', 'a', 'o', 't', 'i', 'l']:
        bbox = font.getbbox(char)
        measurements[char] = bbox[2] - bbox[0]

    # Average lowercase width
    bbox_avg = font.getbbox('abcdefghijklmnopqrstuvwxyz')
    avg_char_width = (bbox_avg[2] - bbox_avg[0]) / 26

    p_width = measurements['P']
    p_count = int(text_width_pt / p_width)
    m_count = int(text_width_pt / measurements['M'])
    avg_count = int(text_width_pt / avg_char_width)

    details = {
        'font': font_name,
        'size_pt': size_pt,
        'page_width_mm': page_width_mm,
        'margin_mm': margin_mm,
        'indent_dxa': indent_dxa,
        'text_width_mm': round(text_width_mm, 1),
        'text_width_pt': round(text_width_pt, 1),
        'p_width_pt': round(p_width, 2),
        'm_width_pt': round(measurements['M'], 2),
        'avg_char_width_pt': round(avg_char_width, 2),
        'p_count': p_count,
        'm_count': m_count,
        'avg_char_count': avg_count,
        'measurements': measurements,
    }

    return p_count, p_width, text_width_pt, details


def main():
    parser = argparse.ArgumentParser(
        description="Measure how many P's fit on one line (practical safe max)"
    )
    parser.add_argument("--font", default="Georgia",
                        help="Font name (default: Georgia)")
    parser.add_argument("--size", type=int, default=11,
                        help="Font size in pt (default: 11)")
    parser.add_argument("--margin", type=float, default=DEFAULT_MARGIN_MM,
                        help="Page margin in mm (default: 25.4 = 1 inch)")
    parser.add_argument("--indent", type=int, default=620,
                        help="Hanging indent in DXA (default: 620)")
    parser.add_argument("--width", type=float, default=A4_WIDTH_MM,
                        help="Page width in mm (default: 210 = A4)")
    args = parser.parse_args()

    p_count, p_width, text_width, details = measure_p_count(
        font_name=args.font,
        size_pt=args.size,
        margin_mm=args.margin,
        indent_dxa=args.indent,
        page_width_mm=args.width
    )

    print(f"=== P-Count Line Width Measurement ===")
    print(f"")
    print(f"  Font:          {details['font']} {details['size_pt']}pt")
    print(f"  Page:          {details['page_width_mm']}mm wide, {details['margin_mm']}mm margins")
    print(f"  Indent:        {details['indent_dxa']} DXA")
    print(f"  Text width:    {details['text_width_mm']}mm ({details['text_width_pt']}pt)")
    print(f"")
    print(f"  Character widths:")
    for char in ['W', 'M', 'P', 'e', 'a', 'o', 't', 'i']:
        w = details['measurements'][char]
        count = int(text_width / w)
        marker = " ← safe limit" if char == 'P' else ""
        print(f"    {char}: {w:.1f}pt → {count} chars/line{marker}")
    print(f"    avg: {details['avg_char_width_pt']}pt → {details['avg_char_count']} chars/line")
    print(f"")
    print(f"  *** P-count (safe max): {p_count} characters ***")
    print(f"  M-count (conservative): {details['m_count']} characters")
    print(f"  Avg-count (reference):  {details['avg_char_count']} characters")
    print(f"")
    print(f"Rule: keep every line <= {p_count} chars.")
    print(f"If longer, ensure it fills two lines well (>= {p_count + 8} chars)")
    print(f"with the sentence break near position {p_count}.")


if __name__ == "__main__":
    main()
