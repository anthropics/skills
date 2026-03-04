#!/usr/bin/env python3
"""
measure_m_count.py - Measure how many capital M's fit on one line.

The 'M-count' method: count how many 'M' characters (the widest glyph
in most fonts) fit within the available text width. This gives a safe
maximum character count per line — any real text will be narrower.

Uses Pillow to measure the exact pixel width of 'M' in the target font,
then divides the available page width by it.

Usage:
    python measure_m_count.py
    python measure_m_count.py --font "Georgia" --size 11 --indent 620
    python measure_m_count.py --font "Calibri" --size 11 --indent 0
"""

import argparse
from PIL import ImageFont
import subprocess
import os


# A4 dimensions
A4_WIDTH_MM = 210
DEFAULT_MARGIN_MM = 25.4  # 1 inch

# Conversion: 1 inch = 72 points = 25.4mm = 1440 DXA (twentieths of a point)
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
    # Try direct mapping
    key = font_name.lower()
    if key in FONT_PATHS and os.path.exists(FONT_PATHS[key]):
        return ImageFont.truetype(FONT_PATHS[key], size_pt)
    
    # Try fc-match (fontconfig)
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
    
    # Try common paths with variations
    for ext in ['.ttf', '.otf']:
        for dir in ['/usr/share/fonts/truetype/', '/usr/share/fonts/']:
            for root, dirs, files in os.walk(dir):
                for f in files:
                    if font_name.lower().replace(' ', '') in f.lower().replace(' ', ''):
                        path = os.path.join(root, f)
                        try:
                            return ImageFont.truetype(path, size_pt)
                        except:
                            continue
    
    print(f"Warning: Could not find '{font_name}', using default font")
    return ImageFont.load_default()


def measure_m_count(font_name="Georgia", size_pt=11, 
                     margin_mm=DEFAULT_MARGIN_MM, indent_dxa=620,
                     page_width_mm=A4_WIDTH_MM):
    """
    Calculate how many 'M' characters fit on one text line.
    
    Returns: (m_count, m_width_px, available_width_px, details_dict)
    """
    # Calculate available text width in mm
    content_width_mm = page_width_mm - (2 * margin_mm)
    indent_mm = indent_dxa / DXA_PER_MM
    text_width_mm = content_width_mm - indent_mm
    
    # Convert to pixels at 72 DPI (1 point = 1 pixel at 72 DPI)
    # Font sizes in points map directly to pixels at 72 DPI
    text_width_pt = text_width_mm * (72 / 25.4)
    
    # Load font and measure 'M'
    font = find_font(font_name, size_pt)
    
    # Measure width of single 'M'
    bbox = font.getbbox('M')
    m_width = bbox[2] - bbox[0]
    
    # Also measure some reference strings for comparison
    bbox_avg = font.getbbox('abcdefghijklmnopqrstuvwxyz')
    avg_char_width = (bbox_avg[2] - bbox_avg[0]) / 26
    
    # How many M's fit?
    m_count = int(text_width_pt / m_width)
    
    # How many average chars fit? (for reference)
    avg_count = int(text_width_pt / avg_char_width)
    
    details = {
        'font': font_name,
        'size_pt': size_pt,
        'page_width_mm': page_width_mm,
        'margin_mm': margin_mm,
        'indent_dxa': indent_dxa,
        'content_width_mm': content_width_mm,
        'indent_mm': round(indent_mm, 1),
        'text_width_mm': round(text_width_mm, 1),
        'text_width_pt': round(text_width_pt, 1),
        'm_width_pt': round(m_width, 2),
        'avg_char_width_pt': round(avg_char_width, 2),
        'm_count': m_count,
        'avg_char_count': avg_count,
    }
    
    return m_count, m_width, text_width_pt, details


def main():
    parser = argparse.ArgumentParser(
        description="Measure how many M's fit on one line (safe max char count)"
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

    m_count, m_width, text_width, details = measure_m_count(
        font_name=args.font,
        size_pt=args.size,
        margin_mm=args.margin,
        indent_dxa=args.indent,
        page_width_mm=args.width
    )

    print(f"=== M-Count Line Width Measurement ===")
    print(f"")
    print(f"  Font:          {details['font']} {details['size_pt']}pt")
    print(f"  Page:          {details['page_width_mm']}mm wide, {details['margin_mm']}mm margins")
    print(f"  Indent:        {details['indent_dxa']} DXA ({details['indent_mm']}mm)")
    print(f"  Text width:    {details['text_width_mm']}mm ({details['text_width_pt']}pt)")
    print(f"")
    print(f"  M width:       {details['m_width_pt']}pt")
    print(f"  Avg char:      {details['avg_char_width_pt']}pt")
    print(f"")
    print(f"  *** M-count (safe max): {m_count} characters ***")
    print(f"  Avg-count (reference):  {details['avg_char_count']} characters")
    print(f"")
    print(f"Rule: keep every line <= {m_count} chars.")
    print(f"If longer, ensure it fills two lines well (>= {m_count + 10} chars)")
    print(f"with the sentence break near position {m_count}.")


if __name__ == "__main__":
    main()
