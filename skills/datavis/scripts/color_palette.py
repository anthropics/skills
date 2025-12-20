#!/usr/bin/env python3
"""
Color Palette Generator for Data Visualization

Generates accessible, perceptually uniform color palettes for:
- Categorical data (distinct colors)
- Sequential data (light to dark)
- Diverging data (two extremes meeting at neutral)

All palettes can be filtered for colorblind accessibility.
"""

import argparse
import colorsys
import json
from dataclasses import dataclass


@dataclass
class Color:
    r: int
    g: int
    b: int

    @property
    def hex(self) -> str:
        return f"#{self.r:02x}{self.g:02x}{self.b:02x}"

    @property
    def rgb(self) -> str:
        return f"rgb({self.r}, {self.g}, {self.b})"

    @property
    def hsl(self) -> tuple:
        h, l, s = colorsys.rgb_to_hls(self.r / 255, self.g / 255, self.b / 255)
        return (h * 360, s * 100, l * 100)

    @classmethod
    def from_hex(cls, hex_str: str) -> "Color":
        hex_str = hex_str.lstrip("#")
        return cls(
            r=int(hex_str[0:2], 16), g=int(hex_str[2:4], 16), b=int(hex_str[4:6], 16)
        )


# Colorblind-safe palettes from research
WONG_PALETTE = [
    "#000000",
    "#E69F00",
    "#56B4E9",
    "#009E73",
    "#F0E442",
    "#0072B2",
    "#D55E00",
    "#CC79A7",
]

OKABE_ITO_PALETTE = [
    "#E69F00",
    "#56B4E9",
    "#009E73",
    "#F0E442",
    "#0072B2",
    "#D55E00",
    "#CC79A7",
    "#000000",
]

TABLEAU_10 = [
    "#4e79a7",
    "#f28e2b",
    "#e15759",
    "#76b7b2",
    "#59a14f",
    "#edc948",
    "#b07aa1",
    "#ff9da7",
    "#9c755f",
    "#bab0ab",
]


def interpolate_color(c1: Color, c2: Color, t: float) -> Color:
    """Linear interpolation between two colors in LAB-like space."""
    # Simple RGB interpolation (could use LAB for better results)
    return Color(
        r=int(c1.r + (c2.r - c1.r) * t),
        g=int(c1.g + (c2.g - c1.g) * t),
        b=int(c1.b + (c2.b - c1.b) * t),
    )


def generate_categorical(count: int, colorblind_safe: bool = False) -> list:
    """Generate distinct colors for categorical data."""
    if colorblind_safe:
        # Use research-backed colorblind-safe palette
        palette = WONG_PALETTE if count <= 8 else OKABE_ITO_PALETTE
        return palette[:count]
    else:
        # Use Tableau 10 or generate via hue spacing
        if count <= 10:
            return TABLEAU_10[:count]
        else:
            # Generate evenly spaced hues
            colors = []
            for i in range(count):
                hue = i / count
                r, g, b = colorsys.hls_to_rgb(hue, 0.5, 0.7)
                colors.append(f"#{int(r*255):02x}{int(g*255):02x}{int(b*255):02x}")
            return colors


def generate_sequential(
    steps: int, hue: int = 220, colorblind_safe: bool = False
) -> list:
    """Generate a sequential palette (light to dark)."""
    if colorblind_safe:
        # Viridis-inspired palette (perceptually uniform, colorblind-safe)
        viridis = [
            "#fde725",
            "#90d743",
            "#35b779",
            "#21918c",
            "#31688e",
            "#443983",
            "#440154",
        ]
        if steps <= len(viridis):
            indices = [int(i * (len(viridis) - 1) / (steps - 1)) for i in range(steps)]
            return [viridis[i] for i in indices]

    # Generate sequential palette from light to dark
    colors = []
    for i in range(steps):
        lightness = 0.9 - (i / (steps - 1)) * 0.7  # 0.9 to 0.2
        r, g, b = colorsys.hls_to_rgb(hue / 360, lightness, 0.6)
        colors.append(f"#{int(r*255):02x}{int(g*255):02x}{int(b*255):02x}")
    return colors


def generate_diverging(steps: int, colorblind_safe: bool = False) -> list:
    """Generate a diverging palette (two extremes meeting at neutral)."""
    if steps % 2 == 0:
        steps += 1  # Diverging palettes work best with odd count

    if colorblind_safe:
        # Purple-Orange (colorblind-safe diverging)
        low_hue = 280  # Purple
        high_hue = 30  # Orange
    else:
        low_hue = 240  # Blue
        high_hue = 10  # Red

    mid_point = steps // 2
    colors = []

    # First half (low to neutral)
    for i in range(mid_point):
        lightness = 0.3 + (i / mid_point) * 0.6
        r, g, b = colorsys.hls_to_rgb(low_hue / 360, lightness, 0.6)
        colors.append(f"#{int(r*255):02x}{int(g*255):02x}{int(b*255):02x}")

    # Middle (neutral)
    colors.append("#f7f7f7")

    # Second half (neutral to high)
    for i in range(mid_point):
        lightness = 0.9 - (i / mid_point) * 0.6
        r, g, b = colorsys.hls_to_rgb(high_hue / 360, lightness, 0.6)
        colors.append(f"#{int(r*255):02x}{int(g*255):02x}{int(b*255):02x}")

    return colors


def check_contrast(c1: Color, c2: Color) -> float:
    """Calculate WCAG contrast ratio between two colors."""

    def luminance(c: Color) -> float:
        def adjust(val):
            val = val / 255
            return val / 12.92 if val <= 0.03928 else ((val + 0.055) / 1.055) ** 2.4

        return 0.2126 * adjust(c.r) + 0.7152 * adjust(c.g) + 0.0722 * adjust(c.b)

    l1 = luminance(c1)
    l2 = luminance(c2)
    lighter = max(l1, l2)
    darker = min(l1, l2)
    return (lighter + 0.05) / (darker + 0.05)


def output_palette(colors: list, format: str = "all"):
    """Output palette in requested format."""
    if format == "json":
        print(json.dumps(colors, indent=2))
    elif format == "css":
        print(":root {")
        for i, color in enumerate(colors):
            print(f"  --color-{i + 1}: {color};")
        print("}")
    elif format == "d3":
        print("const colors = d3.scaleOrdinal()")
        print(f"  .range({json.dumps(colors)});")
    else:
        # All formats
        print("=== HEX ===")
        print(json.dumps(colors, indent=2))
        print("\n=== CSS Variables ===")
        print(":root {")
        for i, color in enumerate(colors):
            print(f"  --color-{i + 1}: {color};")
        print("}")
        print("\n=== D3.js ===")
        print(f"const colors = {json.dumps(colors)};")
        print("\n=== Contrast Check (vs white) ===")
        white = Color(255, 255, 255)
        for color in colors:
            c = Color.from_hex(color)
            ratio = check_contrast(c, white)
            status = "PASS" if ratio >= 4.5 else "FAIL (need 4.5:1)"
            print(f"  {color}: {ratio:.2f}:1 {status}")


def main():
    parser = argparse.ArgumentParser(
        description="Generate accessible color palettes for data visualization"
    )
    parser.add_argument(
        "--type",
        "-t",
        choices=["categorical", "sequential", "diverging"],
        default="categorical",
        help="Palette type (default: categorical)",
    )
    parser.add_argument(
        "--count", "-n", type=int, default=5, help="Number of colors (default: 5)"
    )
    parser.add_argument(
        "--colorblind-safe",
        "-c",
        action="store_true",
        help="Generate colorblind-safe palette",
    )
    parser.add_argument(
        "--hue",
        type=int,
        default=220,
        help="Base hue for sequential palette (0-360, default: 220 blue)",
    )
    parser.add_argument(
        "--format",
        "-f",
        choices=["json", "css", "d3", "all"],
        default="all",
        help="Output format (default: all)",
    )
    parser.add_argument(
        "--steps", "-s", type=int, help="Alias for --count (for sequential/diverging)"
    )

    args = parser.parse_args()
    count = args.steps or args.count

    if args.type == "categorical":
        colors = generate_categorical(count, args.colorblind_safe)
    elif args.type == "sequential":
        colors = generate_sequential(count, args.hue, args.colorblind_safe)
    elif args.type == "diverging":
        colors = generate_diverging(count, args.colorblind_safe)

    output_palette(colors, args.format)


if __name__ == "__main__":
    main()
