#!/usr/bin/env python3
"""
Pixel Art Sprite Sheet Generator

Generates sprite sheets programmatically from JSON specifications.
Useful for creating templates, placeholders, or simple geometric sprites.

Usage:
    python generate_sprite.py --preset slime --output slime.png
    python generate_sprite.py --spec spec.json --output sprite.png
    python generate_sprite.py --demo  # Creates demo sprite sheet
"""

import argparse
import json
import sys
from pathlib import Path

try:
    from PIL import Image, ImageDraw
except ImportError:
    print("Pillow required. Install with: pip install Pillow")
    sys.exit(1)


# Color palettes
PALETTES = {
    "grayscale": ["#FFFFFF", "#AAAAAA", "#555555", "#000000"],
    "gameboy": ["#9BBC0F", "#8BAC0F", "#306230", "#0F380F"],
    "warm": ["#FFFFFF", "#FFD59E", "#E07038", "#5C3018"],
    "cool": ["#FFFFFF", "#88D8FF", "#3898DC", "#1C4A6E"],
    "forest": ["#E8F0C8", "#88C070", "#389050", "#183028"],
    "fire": ["#FFF8C0", "#F8B830", "#E05010", "#582010"],
    "slime": ["#FFFFFF", "#88D8FF", "#3898DC", "#1C4A6E"],
}

MAGENTA = "#FF00FF"


def hex_to_rgb(hex_color: str) -> tuple:
    """Convert hex color to RGB tuple."""
    hex_color = hex_color.lstrip("#")
    return tuple(int(hex_color[i:i+2], 16) for i in (0, 2, 4))


def create_canvas(width: int, height: int, bg_color: str = MAGENTA) -> Image.Image:
    """Create a new canvas with background color."""
    return Image.new("RGB", (width, height), hex_to_rgb(bg_color))


def draw_slime(draw: ImageDraw, x: int, y: int, cell_size: int,
               palette: list, frame: int = 0) -> None:
    """Draw a slime blob sprite."""
    colors = [hex_to_rgb(c) for c in palette]
    outline, shadow, main, highlight = colors[3], colors[2], colors[1], colors[0]

    # Squash/stretch based on frame
    squash = [0, 2, 0, -2][frame % 4]  # Height adjustment

    cx, cy = x + cell_size // 2, y + cell_size // 2

    # Base blob (main body)
    base_w = cell_size // 2
    base_h = cell_size // 3 - squash
    top = cy - base_h // 2 + squash

    # Draw body ellipse approximation with pixels
    for py in range(cell_size):
        for px in range(cell_size):
            dx = (x + px) - cx
            dy = (y + py) - (cy + squash)

            # Ellipse equation
            if (dx * dx) / (base_w * base_w / 4) + (dy * dy) / (base_h * base_h / 4) <= 1:
                # Inside body
                if (dx * dx) / (base_w * base_w / 4) + (dy * dy) / (base_h * base_h / 4) > 0.7:
                    draw.point((x + px, y + py), fill=outline)
                elif dy < -base_h // 4:
                    draw.point((x + px, y + py), fill=highlight)
                elif dy > base_h // 4:
                    draw.point((x + px, y + py), fill=shadow)
                else:
                    draw.point((x + px, y + py), fill=main)

    # Eyes
    eye_y = cy - 2 + squash
    draw.point((cx - 3, eye_y), fill=outline)
    draw.point((cx + 2, eye_y), fill=outline)


def draw_blob(draw: ImageDraw, x: int, y: int, cell_size: int,
              palette: list, frame: int = 0) -> None:
    """Draw a simple blob/ball sprite."""
    colors = [hex_to_rgb(c) for c in palette]

    cx, cy = x + cell_size // 2, y + cell_size // 2
    radius = cell_size // 3

    # Bounce based on frame
    bounce = [0, -1, -2, -1][frame % 4]
    cy += bounce

    # Draw circular blob
    for py in range(-radius, radius + 1):
        for px in range(-radius, radius + 1):
            dist = (px * px + py * py) ** 0.5
            if dist <= radius:
                if dist > radius - 2:
                    color = colors[3]  # Outline
                elif px + py < -radius // 2:
                    color = colors[0]  # Highlight
                elif px + py > radius // 2:
                    color = colors[2]  # Shadow
                else:
                    color = colors[1]  # Main
                draw.point((cx + px, cy + py), fill=color)

    # Eyes
    draw.point((cx - 2, cy - 2), fill=colors[3])
    draw.point((cx + 2, cy - 2), fill=colors[3])


def draw_placeholder(draw: ImageDraw, x: int, y: int, cell_size: int,
                     palette: list, frame: int = 0) -> None:
    """Draw a placeholder sprite (colored square with frame number)."""
    colors = [hex_to_rgb(c) for c in palette]

    margin = 4
    draw.rectangle(
        [x + margin, y + margin, x + cell_size - margin, y + cell_size - margin],
        fill=colors[1],
        outline=colors[3]
    )

    # Frame indicator
    indicator_x = x + cell_size // 2
    indicator_y = y + cell_size // 2
    draw.rectangle(
        [indicator_x - 2, indicator_y - 2, indicator_x + 2, indicator_y + 2],
        fill=colors[frame % len(colors)]
    )


SPRITE_TYPES = {
    "slime": draw_slime,
    "blob": draw_blob,
    "placeholder": draw_placeholder,
}


def generate_sprite_sheet(
    sprite_type: str = "slime",
    palette_name: str = "cool",
    cell_size: int = 32,
    frames: int = 4,
    rows: int = 1,
    output_path: str = "sprite.png"
) -> str:
    """Generate a complete sprite sheet."""

    palette = PALETTES.get(palette_name, PALETTES["grayscale"])
    draw_func = SPRITE_TYPES.get(sprite_type, draw_placeholder)

    width = cell_size * frames
    height = cell_size * rows

    img = create_canvas(width, height)
    draw = ImageDraw.Draw(img)

    for row in range(rows):
        for frame in range(frames):
            x = frame * cell_size
            y = row * cell_size
            draw_func(draw, x, y, cell_size, palette, frame)

    img.save(output_path)
    return output_path


def generate_from_spec(spec: dict, output_path: str) -> str:
    """Generate sprite sheet from a specification dictionary."""

    cell_w = spec.get("cell_width", 32)
    cell_h = spec.get("cell_height", 32)
    cols = spec.get("columns", 4)
    rows = spec.get("rows", 1)
    palette = spec.get("palette", PALETTES["grayscale"])
    sprite_type = spec.get("sprite_type", "placeholder")

    width = cell_w * cols
    height = cell_h * rows

    img = create_canvas(width, height)
    draw = ImageDraw.Draw(img)

    draw_func = SPRITE_TYPES.get(sprite_type, draw_placeholder)

    for row in range(rows):
        for col in range(cols):
            x = col * cell_w
            y = row * cell_h
            frame = row * cols + col
            draw_func(draw, x, y, min(cell_w, cell_h), palette, frame)

    img.save(output_path)
    return output_path


def create_demo() -> str:
    """Create the default demo sprite sheet."""
    return generate_sprite_sheet(
        sprite_type="slime",
        palette_name="cool",
        cell_size=32,
        frames=4,
        rows=1,
        output_path="demo_slime.png"
    )


def main():
    parser = argparse.ArgumentParser(
        description="Generate pixel art sprite sheets"
    )
    parser.add_argument(
        "--preset",
        choices=["slime", "blob", "placeholder"],
        help="Use a built-in sprite preset"
    )
    parser.add_argument(
        "--palette",
        choices=list(PALETTES.keys()),
        default="cool",
        help="Color palette to use"
    )
    parser.add_argument(
        "--spec",
        type=str,
        help="JSON specification file"
    )
    parser.add_argument(
        "--output", "-o",
        type=str,
        default="sprite.png",
        help="Output file path"
    )
    parser.add_argument(
        "--size",
        type=int,
        default=32,
        help="Cell size in pixels"
    )
    parser.add_argument(
        "--frames",
        type=int,
        default=4,
        help="Number of animation frames"
    )
    parser.add_argument(
        "--rows",
        type=int,
        default=1,
        help="Number of animation rows"
    )
    parser.add_argument(
        "--demo",
        action="store_true",
        help="Generate demo sprite sheet"
    )

    args = parser.parse_args()

    if args.demo:
        output = create_demo()
        print(f"Demo sprite sheet created: {output}")
        return

    if args.spec:
        with open(args.spec) as f:
            spec = json.load(f)
        output = generate_from_spec(spec, args.output)
    elif args.preset:
        output = generate_sprite_sheet(
            sprite_type=args.preset,
            palette_name=args.palette,
            cell_size=args.size,
            frames=args.frames,
            rows=args.rows,
            output_path=args.output
        )
    else:
        # Default: create slime demo
        output = generate_sprite_sheet(
            sprite_type="slime",
            palette_name=args.palette,
            cell_size=args.size,
            frames=args.frames,
            rows=args.rows,
            output_path=args.output
        )

    print(f"Sprite sheet generated: {output}")
    print(f"  Size: {args.size * args.frames}x{args.size * args.rows} pixels")
    print(f"  Grid: {args.rows} row(s) x {args.frames} frame(s)")
    print(f"  Cell: {args.size}x{args.size} pixels")


if __name__ == "__main__":
    main()
