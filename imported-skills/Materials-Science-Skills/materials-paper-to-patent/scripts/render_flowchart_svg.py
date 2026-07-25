#!/usr/bin/env python3
"""Render the main method flowchart as inline SVG for use as a DOCX figure."""

from __future__ import annotations

import argparse
import html
import sys
from pathlib import Path
from typing import Any

VIEWBOX_W = 800
VIEWBOX_H = 600
NODE_W = 220
NODE_H = 70
H_SPACING = 40
V_SPACING = 40
COLS = 3


def _layout(steps: list[dict[str, Any]]) -> list[dict[str, Any]]:
    nodes: list[dict[str, Any]] = []
    n = len(steps) or 1
    for index, step in enumerate(steps):
        col = index % COLS
        row = index // COLS
        kind = str(step.get("kind", "step"))
        if index == 0:
            kind = "start"
        if index == n - 1:
            kind = "end" if step.get("kind") == "end" else "result"
        nodes.append({
            "x": 60 + col * (NODE_W + H_SPACING),
            "y": 40 + row * (NODE_H + V_SPACING),
            "label": str(step.get("label", f"步骤{index + 1}"))[:24],
            "kind": kind,
        })
    return nodes


def _node(x: int, y: int, label: str, kind: str = "step") -> str:
    fill = {
        "start": "#e8f4ea",
        "step": "#eef2ff",
        "decision": "#fff7e6",
        "result": "#fde6e6",
        "end": "#e8eaf6",
    }.get(kind, "#eef2ff")
    stroke = "#1f2933"
    return (
        f'<rect x="{x}" y="{y}" width="{NODE_W}" height="{NODE_H}" '
        f'fill="{fill}" stroke="{stroke}" stroke-width="1.5" rx="6" ry="6"/>'
        f'<text x="{x + NODE_W // 2}" y="{y + NODE_H // 2 + 6}" '
        f'font-family="Microsoft YaHei, sans-serif" font-size="14" fill="#111" '
        f'text-anchor="middle">{html.escape(label)}</text>'
    )


def _arrow(x1: int, y1: int, x2: int, y2: int) -> str:
    return (
        f'<line x1="{x1}" y1="{y1}" x2="{x2}" y2="{y2}" '
        f'stroke="#1f2933" stroke-width="1.5" '
        f'marker-end="url(#arrow)"/>'
    )


def render_svg(steps: list[dict[str, Any]], title: str = "工艺流程图") -> str:
    nodes: list[str] = []
    arrows: list[str] = []
    layout = _layout(steps)
    for index, node in enumerate(layout):
        x = int(node["x"])
        y = int(node["y"])
        nodes.append(_node(x, y, str(node["label"]), str(node["kind"])))
        if index > 0:
            prev = layout[index - 1]
            px = int(prev["x"]) + NODE_W
            py = int(prev["y"]) + NODE_H // 2
            arrows.append(_arrow(px, py, x, y + NODE_H // 2))

    defs = (
        '<defs>'
        '<marker id="arrow" viewBox="0 0 10 10" refX="8" refY="5" '
        'markerWidth="8" markerHeight="8" orient="auto-start-reverse">'
        '<path d="M 0 0 L 10 5 L 0 10 z" fill="#1f2933"/>'
        '</marker>'
        '</defs>'
    )
    body = defs + "\n".join(nodes) + "\n" + "\n".join(arrows)
    return (
        f'<?xml version="1.0" encoding="UTF-8" standalone="no"?>\n'
        f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {VIEWBOX_W} {VIEWBOX_H}">\n'
        f'<text x="{VIEWBOX_W // 2}" y="24" font-family="Microsoft YaHei, sans-serif" '
        f'font-size="18" text-anchor="middle">{html.escape(title)}</text>\n'
        f'{body}\n'
        f'</svg>\n'
    )


def render_png(steps: list[dict[str, Any]], output: Path, title: str = "工艺流程图") -> None:
    from PIL import Image, ImageDraw, ImageFont

    image = Image.new("RGB", (VIEWBOX_W, VIEWBOX_H), "white")
    draw = ImageDraw.Draw(image)
    try:
        title_font = ImageFont.truetype("msyh.ttc", 22)
        body_font = ImageFont.truetype("msyh.ttc", 18)
    except OSError:
        title_font = ImageFont.load_default()
        body_font = ImageFont.load_default()

    fills = {
        "start": "#e8f4ea",
        "step": "#eef2ff",
        "decision": "#fff7e6",
        "result": "#fde6e6",
        "end": "#e8eaf6",
    }
    draw.text((VIEWBOX_W // 2, 18), title, fill="#111111", font=title_font, anchor="mm")
    layout = _layout(steps)
    for index, node in enumerate(layout):
        x = int(node["x"])
        y = int(node["y"])
        if index > 0:
            prev = layout[index - 1]
            start = (int(prev["x"]) + NODE_W, int(prev["y"]) + NODE_H // 2)
            end = (x, y + NODE_H // 2)
            draw.line([start, end], fill="#1f2933", width=2)
            draw.polygon(
                [(end[0], end[1]), (end[0] - 10, end[1] - 5), (end[0] - 10, end[1] + 5)],
                fill="#1f2933",
            )
        draw.rounded_rectangle(
            [x, y, x + NODE_W, y + NODE_H],
            radius=6,
            fill=fills.get(str(node["kind"]), "#eef2ff"),
            outline="#1f2933",
            width=2,
        )
        draw.text(
            (x + NODE_W // 2, y + NODE_H // 2),
            str(node["label"]),
            fill="#111111",
            font=body_font,
            anchor="mm",
        )
    output.parent.mkdir(parents=True, exist_ok=True)
    image.save(output)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("steps", type=Path, help="JSON file with steps: [{label, kind?}]")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--png-output", type=Path, help="Optional PNG output path")
    parser.add_argument("--title", default="工艺流程图")
    args = parser.parse_args()

    if not args.steps.exists():
        print(f"ERROR: steps file not found: {args.steps}", file=sys.stderr)
        return 2
    import json
    steps = json.loads(args.steps.read_text(encoding="utf-8"))
    if not isinstance(steps, list):
        print("ERROR: steps must be a list", file=sys.stderr)
        return 2
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(render_svg(steps, title=args.title), encoding="utf-8")
    if args.png_output:
        render_png(steps, args.png_output, title=args.title)
    print(args.output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
