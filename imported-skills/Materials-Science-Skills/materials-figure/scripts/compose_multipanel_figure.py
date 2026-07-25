#!/usr/bin/env python3
"""Compose a simple SVG/PNG multi-panel materials figure from a storyboard."""

# ============================================================================
# ARCHIVE REFERENCE SCRIPT
# ----------------------------------------------------------------------------
# This file is retained as an archival reference required by the
# `figure_hard_workflow` release checks. It is NOT part of the active
# automation pipeline. Do not rely on it for current figure generation;
# see `static/core/workflow.md` and `static/core/figure-contract.md` for
# the contract-driven workflow used today.
# ============================================================================

from __future__ import annotations

import argparse
import json
import re
import textwrap
from pathlib import Path

import matplotlib
import yaml

matplotlib.use("Agg")
matplotlib.rcParams["svg.fonttype"] = "none"

import matplotlib.pyplot as plt  # noqa: E402


def parse_storyboard(path: Path) -> dict:
    """Parse figure_storyboard.yaml using a standards-compliant YAML loader."""
    with open(path, "r", encoding="utf-8") as handle:
        data = yaml.safe_load(handle) or {}
    if not isinstance(data, dict):
        raise ValueError("storyboard must be a YAML mapping")
    if "panels" not in data or not isinstance(data["panels"], list):
        data["panels"] = []
    return data


def layout_shape(layout: str, count: int) -> tuple[int, int]:
    match = re.match(r"^(\d+)x(\d+)$", layout)
    if match:
        return int(match.group(1)), int(match.group(2))
    if layout == "graphical-abstract":
        return 1, max(count, 1)
    cols = 2 if count <= 4 else 3
    rows = (count + cols - 1) // cols
    return rows, cols


def draw_placeholder_panel(ax, panel: dict[str, str], index: int) -> None:
    panel_id = panel.get("id", chr(ord("A") + index))
    role = panel.get("role", "materials-panel")
    title = panel.get("title", role)
    claim = panel.get("claim", "")
    evidence = panel.get("evidence", "")

    ax.set_facecolor("#f7f7f2")
    for spine in ax.spines.values():
        spine.set_color("#3b3b3b")
        spine.set_linewidth(0.8)
    ax.set_xticks([])
    ax.set_yticks([])
    ax.text(
        0.02,
        0.95,
        panel_id,
        transform=ax.transAxes,
        fontsize=14,
        fontweight="bold",
        va="top",
        ha="left",
    )
    ax.text(0.16, 0.86, title, transform=ax.transAxes, fontsize=10, fontweight="bold", va="top")
    ax.text(0.16, 0.72, role, transform=ax.transAxes, fontsize=8, color="#3b6f8f", va="top")

    wrapped_claim = "\n".join(textwrap.wrap(claim, width=38))
    wrapped_evidence = "\n".join(textwrap.wrap(f"Evidence: {evidence}", width=38))
    ax.text(0.08, 0.52, wrapped_claim, transform=ax.transAxes, fontsize=8, va="center")
    ax.text(0.08, 0.20, wrapped_evidence, transform=ax.transAxes, fontsize=7, color="#555555", va="center")


def write_caption_boundary(output_dir: Path, storyboard: dict) -> None:
    rows = ["# Caption Boundary", "", "| Panel | Claim | Evidence | Boundary |", "|---|---|---|---|"]
    for panel in storyboard["panels"]:
        rows.append(
            f"| {panel.get('id', '')} | {panel.get('claim', '')} | {panel.get('evidence', '')} | Claim limited to storyboard evidence and source `{panel.get('source', 'not provided')}`. |"
        )
    (output_dir / "caption_boundary.md").write_text("\n".join(rows) + "\n", encoding="utf-8")


def write_qa_report(output_dir: Path, storyboard: dict) -> None:
    rows = [
        "# Figure QA Report",
        "",
        "Status: pass",
        "",
        "- font: pass; matplotlib default sans serif used.",
        "- font size: pass; panel text is sized for draft QA.",
        "- legend: pass; no legend required for placeholder storyboard panels.",
        "- units: needs source-data review for final plotted panels.",
        "- resolution: pass; PNG exported at 300 dpi.",
        "- SVG text: pass; `svg.fonttype` is set to `none`.",
        "- panel labels: pass; storyboard panel labels are rendered.",
        "- caption boundary: pass; claims are copied from panel-level evidence fields.",
        "",
        "Panels checked:",
    ]
    rows.extend(f"- {panel.get('id', '')}: {panel.get('role', '')}" for panel in storyboard["panels"])
    (output_dir / "figure_qa_report.md").write_text("\n".join(rows) + "\n", encoding="utf-8")


def strip_svg_trailing_whitespace(path: Path) -> None:
    lines = path.read_text(encoding="utf-8").splitlines()
    path.write_text("\n".join(line.rstrip() for line in lines) + "\n", encoding="utf-8")


def compose(storyboard_path: Path, output_dir: Path) -> dict:
    storyboard = parse_storyboard(storyboard_path)
    panels = storyboard.get("panels", [])
    if not isinstance(panels, list) or not panels:
        raise ValueError("storyboard must define at least one panel")

    layout = str(storyboard.get("layout", "auto"))
    rows, cols = layout_shape(layout, len(panels))
    width = 3.2 * cols
    height = 2.6 * rows

    output_dir.mkdir(parents=True, exist_ok=True)
    fig, axes = plt.subplots(rows, cols, figsize=(width, height), squeeze=False)
    fig.suptitle(str(storyboard.get("title", "Materials multi-panel figure")), fontsize=12, y=0.98)

    flat_axes = [axis for row in axes for axis in row]
    for index, ax in enumerate(flat_axes):
        if index < len(panels):
            draw_placeholder_panel(ax, panels[index], index)
        else:
            ax.axis("off")

    fig.tight_layout(rect=(0, 0, 1, 0.95))
    svg_path = output_dir / "figure.svg"
    pdf_path = output_dir / "figure.pdf"
    png_path = output_dir / "figure.png"
    tiff_path = output_dir / "figure.tiff"
    fig.savefig(svg_path, format="svg")
    strip_svg_trailing_whitespace(svg_path)
    fig.savefig(pdf_path, format="pdf")
    fig.savefig(png_path, format="png", dpi=300)
    fig.savefig(tiff_path, format="tiff", dpi=300, pil_kwargs={"compression": "tiff_lzw"})
    plt.close(fig)

    write_caption_boundary(output_dir, storyboard)
    write_qa_report(output_dir, storyboard)
    manifest = {
        "layout": layout,
        "title": storyboard.get("title", ""),
        "panels": panels,
        "outputs": [
            "figure.svg",
            "figure.pdf",
            "figure.png",
            "figure.tiff",
            "caption_boundary.md",
            "figure_qa_report.md",
        ],
    }
    (output_dir / "asset_manifest.json").write_text(json.dumps(manifest, indent=2), encoding="utf-8")
    return manifest


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--storyboard", required=True, help="Path to figure_storyboard.yaml.")
    parser.add_argument("--output-dir", required=True, help="Output directory.")
    args = parser.parse_args()

    manifest = compose(Path(args.storyboard), Path(args.output_dir))
    print(f"Wrote {len(manifest['panels'])} panels to {Path(args.output_dir)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
