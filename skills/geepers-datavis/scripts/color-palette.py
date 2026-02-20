#!/usr/bin/env python3
"""
Color Palette Generator for Data Visualization

Generates colorblind-safe, perceptually uniform color palettes.

Usage:
    python color-palette.py --type sequential --hue blue --steps 9
    python color-palette.py --type categorical --count 6 --colorblind-safe
    python color-palette.py --type diverging --low red --high blue
    python color-palette.py --preset war-regions
    python color-palette.py --preset corporate

Author: Luke Steuber
"""

import argparse
import json
import sys
from typing import List, Dict, Tuple

# Colorblind-safe categorical palette (Paul Tol's scheme)
COLORBLIND_SAFE = [
    '#332288',  # Indigo
    '#117733',  # Green
    '#44AA99',  # Teal
    '#88CCEE',  # Cyan
    '#DDCC77',  # Sand
    '#CC6677',  # Rose
    '#AA4499',  # Purple
    '#882255',  # Wine
]

# D3 categorical schemes
D3_CATEGORY10 = [
    '#1f77b4', '#ff7f0e', '#2ca02c', '#d62728', '#9467bd',
    '#8c564b', '#e377c2', '#7f7f7f', '#bcbd22', '#17becf'
]

# Project-specific presets from existing visualizations
PRESETS = {
    'war-regions': {
        'description': 'Forget Me Not war casualties by region',
        'colors': {
            'Europe': '#b91c1c',
            'Asia': '#d97706',
            'Middle East': '#1d4ed8',
            'Africa': '#15803d',
            'Americas': '#7e22ce',
        }
    },
    'corporate': {
        'description': 'Dow Jones corporate connections',
        'colors': {
            'Board': '#0077BB',
            'Executive': '#000000',
            'Government': '#D4AF37',
        }
    },
    'sentiment': {
        'description': 'Positive/negative sentiment diverging',
        'colors': {
            'Very Negative': '#b91c1c',
            'Negative': '#dc2626',
            'Neutral': '#6b7280',
            'Positive': '#16a34a',
            'Very Positive': '#15803d',
        }
    }
}

# Base hues for sequential palettes (HSL lightness variations)
BASE_HUES = {
    'blue': (210, 80),    # hue, saturation
    'green': (140, 70),
    'red': (0, 75),
    'orange': (30, 85),
    'purple': (270, 65),
    'teal': (175, 60),
    'gold': (45, 80),
    'gray': (0, 0),
}


def hsl_to_hex(h: float, s: float, l: float) -> str:
    """Convert HSL to hex color."""
    s = s / 100
    l = l / 100

    c = (1 - abs(2 * l - 1)) * s
    x = c * (1 - abs((h / 60) % 2 - 1))
    m = l - c / 2

    if 0 <= h < 60:
        r, g, b = c, x, 0
    elif 60 <= h < 120:
        r, g, b = x, c, 0
    elif 120 <= h < 180:
        r, g, b = 0, c, x
    elif 180 <= h < 240:
        r, g, b = 0, x, c
    elif 240 <= h < 300:
        r, g, b = x, 0, c
    else:
        r, g, b = c, 0, x

    r = int((r + m) * 255)
    g = int((g + m) * 255)
    b = int((b + m) * 255)

    return f'#{r:02x}{g:02x}{b:02x}'


def generate_sequential(hue: str, steps: int) -> List[str]:
    """Generate sequential palette from light to dark."""
    if hue not in BASE_HUES:
        print(f"Unknown hue '{hue}'. Available: {list(BASE_HUES.keys())}", file=sys.stderr)
        sys.exit(1)

    h, s = BASE_HUES[hue]
    colors = []

    # Lightness from 95% (very light) to 25% (dark)
    for i in range(steps):
        l = 95 - (70 * i / (steps - 1)) if steps > 1 else 50
        colors.append(hsl_to_hex(h, s, l))

    return colors


def generate_diverging(low_hue: str, high_hue: str, steps: int = 9) -> List[str]:
    """Generate diverging palette with neutral midpoint."""
    if steps % 2 == 0:
        steps += 1  # Ensure odd number for clear midpoint

    mid = steps // 2
    colors = []

    low_h, low_s = BASE_HUES.get(low_hue, (0, 75))
    high_h, high_s = BASE_HUES.get(high_hue, (210, 80))

    # Low end (dark to light)
    for i in range(mid):
        l = 30 + (35 * i / mid)
        colors.append(hsl_to_hex(low_h, low_s, l))

    # Midpoint (neutral gray)
    colors.append('#f5f5f5')

    # High end (light to dark)
    for i in range(mid):
        l = 65 - (35 * i / mid)
        colors.append(hsl_to_hex(high_h, high_s, l))

    return colors


def generate_categorical(count: int, colorblind_safe: bool = True) -> List[str]:
    """Generate categorical palette."""
    if colorblind_safe:
        if count > len(COLORBLIND_SAFE):
            print(f"Warning: Only {len(COLORBLIND_SAFE)} colorblind-safe colors available",
                  file=sys.stderr)
        return COLORBLIND_SAFE[:count]
    else:
        return D3_CATEGORY10[:count]


def output_palette(colors: List[str] | Dict[str, str], format: str, name: str = 'palette'):
    """Output palette in requested format."""
    if isinstance(colors, dict):
        color_list = list(colors.values())
        labels = list(colors.keys())
    else:
        color_list = colors
        labels = None

    if format == 'json':
        if labels:
            print(json.dumps(dict(zip(labels, color_list)), indent=2))
        else:
            print(json.dumps(color_list, indent=2))

    elif format == 'js':
        if labels:
            print(f"const {name} = {{")
            for label, color in zip(labels, color_list):
                print(f"  '{label}': '{color}',")
            print("};")
        else:
            print(f"const {name} = {json.dumps(color_list)};")

    elif format == 'css':
        print(":root {")
        if labels:
            for i, (label, color) in enumerate(zip(labels, color_list)):
                var_name = label.lower().replace(' ', '-').replace('_', '-')
                print(f"  --color-{var_name}: {color};")
        else:
            for i, color in enumerate(color_list):
                print(f"  --color-{name}-{i}: {color};")
        print("}")

    elif format == 'd3':
        print(f"const {name}Scale = d3.scaleOrdinal()")
        if labels:
            print(f"  .domain({json.dumps(labels)})")
        print(f"  .range({json.dumps(color_list)});")

    else:  # text
        if labels:
            for label, color in zip(labels, color_list):
                print(f"{label}: {color}")
        else:
            for color in color_list:
                print(color)


def print_swatches(colors: List[str] | Dict[str, str]):
    """Print color swatches using ANSI escape codes."""
    if isinstance(colors, dict):
        items = list(colors.items())
    else:
        items = [(f"Color {i+1}", c) for i, c in enumerate(colors)]

    print("\nColor Swatches:")
    print("-" * 40)

    for label, hex_color in items:
        # Convert hex to RGB for ANSI
        r = int(hex_color[1:3], 16)
        g = int(hex_color[3:5], 16)
        b = int(hex_color[5:7], 16)

        # ANSI true color escape sequence
        swatch = f"\033[48;2;{r};{g};{b}m    \033[0m"
        print(f"{swatch} {hex_color}  {label}")

    print("-" * 40)


def main():
    parser = argparse.ArgumentParser(
        description='Generate colorblind-safe palettes for data visualization',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s --type sequential --hue blue --steps 9
  %(prog)s --type categorical --count 6 --colorblind-safe
  %(prog)s --type diverging --low red --high blue --steps 11
  %(prog)s --preset war-regions --format css
  %(prog)s --list-presets
        """
    )

    parser.add_argument('--type', '-t',
                        choices=['sequential', 'categorical', 'diverging'],
                        help='Palette type')
    parser.add_argument('--hue',
                        choices=list(BASE_HUES.keys()),
                        help='Base hue for sequential palette')
    parser.add_argument('--low',
                        choices=list(BASE_HUES.keys()),
                        help='Low-end hue for diverging palette')
    parser.add_argument('--high',
                        choices=list(BASE_HUES.keys()),
                        help='High-end hue for diverging palette')
    parser.add_argument('--steps', '-s', type=int, default=9,
                        help='Number of steps in palette (default: 9)')
    parser.add_argument('--count', '-c', type=int, default=8,
                        help='Number of colors for categorical (default: 8)')
    parser.add_argument('--colorblind-safe', '-cb', action='store_true',
                        help='Use colorblind-safe palette')
    parser.add_argument('--preset', '-p',
                        choices=list(PRESETS.keys()),
                        help='Use a project preset')
    parser.add_argument('--list-presets', action='store_true',
                        help='List available presets')
    parser.add_argument('--format', '-f',
                        choices=['text', 'json', 'js', 'css', 'd3'],
                        default='text',
                        help='Output format (default: text)')
    parser.add_argument('--name', '-n', default='palette',
                        help='Variable name for js/d3 output')
    parser.add_argument('--no-swatches', action='store_true',
                        help='Skip printing color swatches')

    args = parser.parse_args()

    # List presets
    if args.list_presets:
        print("Available presets:")
        for name, preset in PRESETS.items():
            print(f"\n  {name}:")
            print(f"    {preset['description']}")
            for label, color in preset['colors'].items():
                print(f"      {label}: {color}")
        return

    # Generate palette
    colors = None

    if args.preset:
        colors = PRESETS[args.preset]['colors']
    elif args.type == 'sequential':
        if not args.hue:
            parser.error("--type sequential requires --hue")
        colors = generate_sequential(args.hue, args.steps)
    elif args.type == 'categorical':
        colors = generate_categorical(args.count, args.colorblind_safe)
    elif args.type == 'diverging':
        if not args.low or not args.high:
            parser.error("--type diverging requires --low and --high")
        colors = generate_diverging(args.low, args.high, args.steps)
    else:
        parser.error("Must specify --type or --preset")

    # Output
    output_palette(colors, args.format, args.name)

    if not args.no_swatches and args.format == 'text':
        print_swatches(colors)


if __name__ == '__main__':
    main()
