"""Hierarchical mechanism schematic for a multi-step WER-EA flow.

Reads data/synthetic.csv (step, label, parent) and renders a tree-style
schematic with arrows.
"""
from __future__ import annotations

import csv
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.patches as mpatches
import matplotlib.pyplot as plt

PALETTE_FILL = "#3775BA"
PALETTE_TEXT = "white"

plt.rcParams.update({
    "font.family": "sans-serif",
    "font.sans-serif": ["Arial", "DejaVu Sans", "Liberation Sans"],
    "font.size": 12,
    "svg.fonttype": "none",
})


def _read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as f:
        return list(csv.DictReader(f))


def main() -> None:
    here = Path(__file__).resolve().parent
    rows = _read_csv(here / "data" / "synthetic.csv")
    fig, ax = plt.subplots(figsize=(11, 4.5))
    n = len(rows)
    for i, row in enumerate(rows):
        x = 0.10 + (0.80 / max(n - 1, 1)) * i
        rect = mpatches.FancyBboxPatch(
            (x - 0.07, 0.40), 0.14, 0.20,
            boxstyle="round,pad=0.01", facecolor=PALETTE_FILL,
            edgecolor="black", linewidth=1.4,
        )
        ax.add_patch(rect)
        ax.text(x, 0.50, row["label"], ha="center", va="center",
                fontsize=10, color=PALETTE_TEXT, fontweight="bold")
    for i in range(n - 1):
        x1 = 0.10 + (0.80 / max(n - 1, 1)) * i + 0.07
        x2 = 0.10 + (0.80 / max(n - 1, 1)) * (i + 1) - 0.07
        ax.annotate("", xy=(x2, 0.50), xytext=(x1, 0.50),
                    arrowprops=dict(arrowstyle="->", lw=1.8, color="#4D4D4D"))
    ax.set_xlim(0, 1)
    ax.set_ylim(0.2, 0.8)
    ax.axis("off")
    fig.tight_layout()
    out = here / "figures"
    out.mkdir(exist_ok=True)
    fig.savefig(out / "hierarchical_mechanism_schematic.png", dpi=300)
    fig.savefig(out / "hierarchical_mechanism_schematic.svg")
    plt.close(fig)
    print(f"Wrote {out / 'hierarchical_mechanism_schematic.png'}")


if __name__ == "__main__":
    main()
