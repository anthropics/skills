#!/usr/bin/env python3
"""
Figma Design Token Extractor

Extracts colors, typography, spacing, shadows, gradients, and border-radius
from Figma API JSON data and outputs as CSS custom properties, Tailwind config,
JSON tokens, or SCSS variables.

Usage:
    python3 extract_tokens.py --input figma-data.json --format css
    python3 extract_tokens.py --input figma-data.json --format tailwind --output tailwind.config.js
    cat figma-data.json | python3 extract_tokens.py --format json

Part of the Figma Skill for Claude Code.
Requires: Python 3.8+ (stdlib only, no pip dependencies)
"""

import json
import sys
import argparse
import colorsys
import re
from pathlib import Path
from collections import OrderedDict


# ---------------------------------------------------------------------------
# Color helpers
# ---------------------------------------------------------------------------

def figma_color_to_hex(color: dict) -> str:
    """Convert Figma RGBA (0-1 floats) to #RRGGBB or #RRGGBBAA."""
    r = round(color.get("r", 0) * 255)
    g = round(color.get("g", 0) * 255)
    b = round(color.get("b", 0) * 255)
    a = color.get("a", 1)
    if a < 1:
        return f"#{r:02x}{g:02x}{b:02x}{round(a * 255):02x}"
    return f"#{r:02x}{g:02x}{b:02x}"


def figma_color_to_rgba(color: dict) -> str:
    """Convert Figma RGBA to rgba() CSS string."""
    r = round(color.get("r", 0) * 255)
    g = round(color.get("g", 0) * 255)
    b = round(color.get("b", 0) * 255)
    a = round(color.get("a", 1), 3)
    if a == 1:
        return f"rgb({r}, {g}, {b})"
    return f"rgba({r}, {g}, {b}, {a})"


def figma_color_to_hsl(color: dict) -> str:
    """Convert Figma RGBA to hsl() / hsla() CSS string."""
    r = color.get("r", 0)
    g = color.get("g", 0)
    b = color.get("b", 0)
    a = round(color.get("a", 1), 3)
    h, l, s = colorsys.rgb_to_hls(r, g, b)
    h = round(h * 360)
    s = round(s * 100, 1)
    l = round(l * 100, 1)
    if a < 1:
        return f"hsla({h}, {s}%, {l}%, {a})"
    return f"hsl({h}, {s}%, {l}%)"


def _slugify(name: str) -> str:
    """Convert a Figma layer name to a valid CSS/token identifier."""
    slug = re.sub(r"[^a-zA-Z0-9]+", "-", name.strip()).strip("-").lower()
    return slug or "unnamed"


# ---------------------------------------------------------------------------
# Extraction functions — walk the Figma JSON tree
# ---------------------------------------------------------------------------

def extract_colors(node: dict, prefix: str = "", collected: dict = None) -> dict:
    """Recursively extract solid fill colors from the node tree."""
    if collected is None:
        collected = OrderedDict()

    name = node.get("name", "")
    node_type = node.get("type", "")

    # Color styles defined at document level
    if node_type in ("RECTANGLE", "ELLIPSE", "FRAME", "COMPONENT", "INSTANCE", "VECTOR", "TEXT"):
        fills = node.get("fills", [])
        for fill in fills:
            if fill.get("type") == "SOLID" and fill.get("visible", True):
                color = fill.get("color", {})
                opacity = fill.get("opacity", color.get("a", 1))
                color_with_opacity = {**color, "a": opacity}
                token_name = _slugify(f"{prefix}{name}") if prefix else _slugify(name)
                if token_name and token_name not in collected:
                    collected[token_name] = {
                        "hex": figma_color_to_hex(color_with_opacity),
                        "rgba": figma_color_to_rgba(color_with_opacity),
                        "hsl": figma_color_to_hsl(color_with_opacity),
                        "figma": color_with_opacity,
                    }

    # Recurse into children
    for child in node.get("children", []):
        child_prefix = f"{prefix}{name}/" if name and node_type in ("FRAME", "GROUP", "SECTION", "PAGE", "COMPONENT_SET") else prefix
        extract_colors(child, child_prefix, collected)

    return collected


def extract_typography(node: dict, collected: dict = None) -> dict:
    """Recursively extract text styles (font, size, weight, line-height, letter-spacing)."""
    if collected is None:
        collected = OrderedDict()

    if node.get("type") == "TEXT":
        style = node.get("style", {})
        name = _slugify(node.get("name", "text"))
        if style and name not in collected:
            collected[name] = {
                "fontFamily": style.get("fontFamily", "sans-serif"),
                "fontSize": style.get("fontSize", 16),
                "fontWeight": style.get("fontWeight", 400),
                "lineHeight": _extract_line_height(style),
                "letterSpacing": _extract_letter_spacing(style),
                "textAlign": style.get("textAlignHorizontal", "LEFT").lower(),
                "textTransform": style.get("textCase", "ORIGINAL").lower(),
            }

    for child in node.get("children", []):
        extract_typography(child, collected)

    return collected


def _extract_line_height(style: dict):
    """Extract line-height from Figma text style."""
    lh = style.get("lineHeightPx")
    fs = style.get("fontSize", 16)
    if lh and fs:
        ratio = round(lh / fs, 3)
        return {"px": round(lh, 1), "ratio": ratio}
    unit = style.get("lineHeightUnit", "AUTO")
    if unit == "FONT_SIZE_%":
        pct = style.get("lineHeightPercentFontSize", 100)
        return {"px": round(fs * pct / 100, 1), "ratio": round(pct / 100, 3)}
    return {"px": round(fs * 1.5, 1), "ratio": 1.5}


def _extract_letter_spacing(style: dict):
    """Extract letter-spacing from Figma text style."""
    ls = style.get("letterSpacing", 0)
    fs = style.get("fontSize", 16)
    if ls and fs:
        return {"px": round(ls, 2), "em": round(ls / fs, 4)}
    return {"px": 0, "em": 0}


def extract_spacing(node: dict, collected: dict = None) -> dict:
    """Extract padding and gap values from auto-layout frames."""
    if collected is None:
        collected = OrderedDict()

    if node.get("type") in ("FRAME", "COMPONENT", "INSTANCE"):
        layout_mode = node.get("layoutMode")
        if layout_mode:
            name = _slugify(node.get("name", "frame"))
            pt = node.get("paddingTop", 0)
            pr = node.get("paddingRight", 0)
            pb = node.get("paddingBottom", 0)
            pl = node.get("paddingLeft", 0)
            gap = node.get("itemSpacing", 0)

            spacing_data = {}
            if any([pt, pr, pb, pl]):
                if pt == pr == pb == pl:
                    spacing_data["padding"] = pt
                else:
                    spacing_data["paddingTop"] = pt
                    spacing_data["paddingRight"] = pr
                    spacing_data["paddingBottom"] = pb
                    spacing_data["paddingLeft"] = pl
            if gap:
                spacing_data["gap"] = gap

            if spacing_data and name not in collected:
                collected[name] = spacing_data

    for child in node.get("children", []):
        extract_spacing(child, collected)

    return collected


def extract_border_radii(node: dict, collected: dict = None) -> dict:
    """Extract border-radius values from nodes."""
    if collected is None:
        collected = OrderedDict()

    cr = node.get("cornerRadius")
    rectangleCornerRadii = node.get("rectangleCornerRadii")
    if cr is not None or rectangleCornerRadii:
        name = _slugify(node.get("name", "element"))
        if name not in collected:
            if rectangleCornerRadii:
                collected[name] = {
                    "topLeft": rectangleCornerRadii[0],
                    "topRight": rectangleCornerRadii[1],
                    "bottomRight": rectangleCornerRadii[2],
                    "bottomLeft": rectangleCornerRadii[3],
                }
            elif cr is not None:
                collected[name] = {"all": cr}

    for child in node.get("children", []):
        extract_border_radii(child, collected)

    return collected


def extract_shadows(node: dict, collected: dict = None) -> dict:
    """Extract drop shadow and inner shadow effects."""
    if collected is None:
        collected = OrderedDict()

    effects = node.get("effects", [])
    for effect in effects:
        if effect.get("type") in ("DROP_SHADOW", "INNER_SHADOW") and effect.get("visible", True):
            name = _slugify(node.get("name", "shadow"))
            if name not in collected:
                color = effect.get("color", {})
                collected[name] = {
                    "type": "inset" if effect["type"] == "INNER_SHADOW" else "drop",
                    "x": effect.get("offset", {}).get("x", 0),
                    "y": effect.get("offset", {}).get("y", 0),
                    "blur": effect.get("radius", 0),
                    "spread": effect.get("spread", 0),
                    "color": figma_color_to_rgba(color),
                }

    for child in node.get("children", []):
        extract_shadows(child, collected)

    return collected


def extract_gradients(node: dict, collected: dict = None) -> dict:
    """Extract gradient fills from nodes."""
    if collected is None:
        collected = OrderedDict()

    fills = node.get("fills", [])
    for fill in fills:
        if fill.get("type") in ("GRADIENT_LINEAR", "GRADIENT_RADIAL", "GRADIENT_ANGULAR") and fill.get("visible", True):
            name = _slugify(node.get("name", "gradient"))
            if name not in collected:
                stops = []
                for stop in fill.get("gradientStops", []):
                    stops.append({
                        "color": figma_color_to_hex(stop.get("color", {})),
                        "position": round(stop.get("position", 0) * 100, 1),
                    })
                gradient_type = fill["type"].replace("GRADIENT_", "").lower()
                collected[name] = {
                    "type": gradient_type,
                    "stops": stops,
                }

    for child in node.get("children", []):
        extract_gradients(child, collected)

    return collected


def extract_all_tokens(data: dict) -> dict:
    """Extract all design tokens from Figma JSON data."""
    # Handle both full file responses and single node responses
    root = data.get("document", data)
    if "nodes" in data:
        # Response from get_figma_data with nodeId — merge all nodes
        nodes = data["nodes"]
        root = {"children": [v.get("document", v) for v in nodes.values()]}

    return {
        "colors": extract_colors(root),
        "typography": extract_typography(root),
        "spacing": extract_spacing(root),
        "borderRadius": extract_border_radii(root),
        "shadows": extract_shadows(root),
        "gradients": extract_gradients(root),
    }


# ---------------------------------------------------------------------------
# Output formatters
# ---------------------------------------------------------------------------

def format_css(tokens: dict) -> str:
    """Format tokens as CSS custom properties."""
    lines = ["/* Design Tokens — extracted from Figma */", "/* Generated by Figma Skill for Claude Code */", "", ":root {"]

    # Colors
    if tokens.get("colors"):
        lines.append("  /* Colors */")
        for name, val in tokens["colors"].items():
            lines.append(f"  --color-{name}: {val['hex']};")
        lines.append("")

    # Typography
    if tokens.get("typography"):
        lines.append("  /* Typography */")
        for name, val in tokens["typography"].items():
            lines.append(f"  --font-{name}-family: '{val['fontFamily']}', sans-serif;")
            lines.append(f"  --font-{name}-size: {val['fontSize']}px;")
            lines.append(f"  --font-{name}-weight: {val['fontWeight']};")
            lines.append(f"  --font-{name}-line-height: {val['lineHeight']['ratio']};")
            if val["letterSpacing"]["px"]:
                lines.append(f"  --font-{name}-letter-spacing: {val['letterSpacing']['px']}px;")
        lines.append("")

    # Spacing
    if tokens.get("spacing"):
        lines.append("  /* Spacing */")
        seen_values = set()
        for name, val in tokens["spacing"].items():
            for prop, px_val in val.items():
                if px_val and px_val not in seen_values:
                    lines.append(f"  --spacing-{px_val}: {px_val}px;")
                    seen_values.add(px_val)
        lines.append("")

    # Border Radius
    if tokens.get("borderRadius"):
        lines.append("  /* Border Radius */")
        seen_values = set()
        for name, val in tokens["borderRadius"].items():
            if "all" in val and val["all"] not in seen_values:
                lines.append(f"  --radius-{name}: {val['all']}px;")
                seen_values.add(val["all"])
            else:
                tl = val.get("topLeft", 0)
                tr = val.get("topRight", 0)
                br = val.get("bottomRight", 0)
                bl = val.get("bottomLeft", 0)
                lines.append(f"  --radius-{name}: {tl}px {tr}px {br}px {bl}px;")
        lines.append("")

    # Shadows
    if tokens.get("shadows"):
        lines.append("  /* Shadows */")
        for name, val in tokens["shadows"].items():
            inset = "inset " if val["type"] == "inset" else ""
            lines.append(f"  --shadow-{name}: {inset}{val['x']}px {val['y']}px {val['blur']}px {val['spread']}px {val['color']};")
        lines.append("")

    # Gradients
    if tokens.get("gradients"):
        lines.append("  /* Gradients */")
        for name, val in tokens["gradients"].items():
            stops_str = ", ".join(f"{s['color']} {s['position']}%" for s in val["stops"])
            if val["type"] == "linear":
                lines.append(f"  --gradient-{name}: linear-gradient(to right, {stops_str});")
            elif val["type"] == "radial":
                lines.append(f"  --gradient-{name}: radial-gradient(circle, {stops_str});")
            elif val["type"] == "angular":
                lines.append(f"  --gradient-{name}: conic-gradient({stops_str});")
        lines.append("")

    lines.append("}")
    return "\n".join(lines)


def format_tailwind(tokens: dict) -> str:
    """Format tokens as a Tailwind CSS config extend block."""
    lines = [
        "// Design Tokens — extracted from Figma",
        "// Generated by Figma Skill for Claude Code",
        "// Paste into tailwind.config.js > theme.extend",
        "",
        "module.exports = {",
        "  theme: {",
        "    extend: {",
    ]

    # Colors
    if tokens.get("colors"):
        lines.append("      colors: {")
        for name, val in tokens["colors"].items():
            lines.append(f"        '{name}': '{val['hex']}',")
        lines.append("      },")

    # Font families
    families = set()
    if tokens.get("typography"):
        lines.append("      fontFamily: {")
        for name, val in tokens["typography"].items():
            family = val["fontFamily"]
            if family not in families:
                slug = _slugify(family)
                lines.append(f"        '{slug}': ['{family}', 'sans-serif'],")
                families.add(family)
        lines.append("      },")

        # Font sizes
        lines.append("      fontSize: {")
        seen_sizes = set()
        for name, val in tokens["typography"].items():
            fs = val["fontSize"]
            if fs not in seen_sizes:
                lh = val["lineHeight"]["ratio"]
                lines.append(f"        '{name}': ['{fs}px', {{ lineHeight: '{lh}' }}],")
                seen_sizes.add(fs)
        lines.append("      },")

    # Border radius
    if tokens.get("borderRadius"):
        lines.append("      borderRadius: {")
        for name, val in tokens["borderRadius"].items():
            if "all" in val:
                lines.append(f"        '{name}': '{val['all']}px',")
        lines.append("      },")

    # Box shadow
    if tokens.get("shadows"):
        lines.append("      boxShadow: {")
        for name, val in tokens["shadows"].items():
            inset = "inset " if val["type"] == "inset" else ""
            lines.append(f"        '{name}': '{inset}{val['x']}px {val['y']}px {val['blur']}px {val['spread']}px {val['color']}',")
        lines.append("      },")

    lines.extend([
        "    },",
        "  },",
        "};",
    ])
    return "\n".join(lines)


def format_json(tokens: dict) -> str:
    """Format tokens as raw JSON."""
    # Simplify for JSON output — flatten figma internals
    output = {}
    if tokens.get("colors"):
        output["colors"] = {name: val["hex"] for name, val in tokens["colors"].items()}
    if tokens.get("typography"):
        output["typography"] = tokens["typography"]
    if tokens.get("spacing"):
        output["spacing"] = tokens["spacing"]
    if tokens.get("borderRadius"):
        output["borderRadius"] = tokens["borderRadius"]
    if tokens.get("shadows"):
        output["shadows"] = tokens["shadows"]
    if tokens.get("gradients"):
        output["gradients"] = tokens["gradients"]
    return json.dumps(output, indent=2)


def format_scss(tokens: dict) -> str:
    """Format tokens as SCSS variables."""
    lines = [
        "// Design Tokens — extracted from Figma",
        "// Generated by Figma Skill for Claude Code",
        "",
    ]

    if tokens.get("colors"):
        lines.append("// Colors")
        for name, val in tokens["colors"].items():
            lines.append(f"$color-{name}: {val['hex']};")
        lines.append("")

    if tokens.get("typography"):
        lines.append("// Typography")
        for name, val in tokens["typography"].items():
            lines.append(f"$font-{name}-family: '{val['fontFamily']}', sans-serif;")
            lines.append(f"$font-{name}-size: {val['fontSize']}px;")
            lines.append(f"$font-{name}-weight: {val['fontWeight']};")
            lines.append(f"$font-{name}-line-height: {val['lineHeight']['ratio']};")
        lines.append("")

    if tokens.get("shadows"):
        lines.append("// Shadows")
        for name, val in tokens["shadows"].items():
            inset = "inset " if val["type"] == "inset" else ""
            lines.append(f"$shadow-{name}: {inset}{val['x']}px {val['y']}px {val['blur']}px {val['spread']}px {val['color']};")
        lines.append("")

    if tokens.get("gradients"):
        lines.append("// Gradients")
        for name, val in tokens["gradients"].items():
            stops_str = ", ".join(f"{s['color']} {s['position']}%" for s in val["stops"])
            if val["type"] == "linear":
                lines.append(f"$gradient-{name}: linear-gradient(to right, {stops_str});")
            elif val["type"] == "radial":
                lines.append(f"$gradient-{name}: radial-gradient(circle, {stops_str});")
        lines.append("")

    return "\n".join(lines)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

FORMATTERS = {
    "css": format_css,
    "tailwind": format_tailwind,
    "json": format_json,
    "scss": format_scss,
}


def main():
    parser = argparse.ArgumentParser(
        description="Extract design tokens from Figma JSON data.",
        epilog="Part of the Figma Skill for Claude Code — https://github.com/figma-skill",
    )
    parser.add_argument(
        "--input", "-i",
        help="Path to Figma JSON file (or pipe via stdin)",
    )
    parser.add_argument(
        "--format", "-f",
        choices=list(FORMATTERS.keys()),
        default="css",
        help="Output format (default: css)",
    )
    parser.add_argument(
        "--output", "-o",
        help="Output file path (default: stdout)",
    )
    args = parser.parse_args()

    # Read input
    if args.input:
        path = Path(args.input)
        if not path.exists():
            print(f"Error: File not found: {args.input}", file=sys.stderr)
            sys.exit(1)
        data = json.loads(path.read_text(encoding="utf-8"))
    elif not sys.stdin.isatty():
        data = json.load(sys.stdin)
    else:
        parser.print_help()
        print("\nError: Provide --input file or pipe JSON via stdin.", file=sys.stderr)
        sys.exit(1)

    # Extract tokens
    tokens = extract_all_tokens(data)

    # Check if anything was extracted
    total = sum(len(v) for v in tokens.values())
    if total == 0:
        print("Warning: No design tokens found in the input data.", file=sys.stderr)
        print("Tip: Make sure the JSON contains Figma node data with fills, text styles, or effects.", file=sys.stderr)

    # Format output
    formatter = FORMATTERS[args.format]
    result = formatter(tokens)

    # Write output
    if args.output:
        out_path = Path(args.output)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(result, encoding="utf-8")
        print(f"Tokens written to {args.output} ({total} tokens, {args.format} format)", file=sys.stderr)
    else:
        print(result)


if __name__ == "__main__":
    main()
