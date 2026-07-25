"""Multiscale graphical abstract for a hierarchical materials design.

Reads data/synthetic.csv and renders a 4-level architecture diagram.
"""
from __future__ import annotations

import csv
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

PALETTE = ["#3775BA", "#7AA6D4", "#E07C3E", "#2E9E44"]

plt.rcParams.update({
    "font.family": "sans-serif",
    "font.sans-serif": ["Arial", "DejaVu Sans", "Liberation Sans"],
    "font.size": 14,
    "svg.fonttype": "none",
})


def _read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as f:
        return list(csv.DictReader(f))


def main() -> None:
    here = Path(__file__).resolve().parent
    rows = _read_csv(here / "data" / "synthetic.csv")
    fig, ax = plt.subplots(figsize=(10, 4.5))
    for i, row in enumerate(rows):
        circ = plt.Circle((0.10 + i * 0.27, 0.5), 0.08, color=PALETTE[i % len(PALETTE)])
        ax.add_patch(circ)
        ax.text(0.10 + i * 0.27, 0.5, row["label"], ha="center", va="center",
                fontsize=10, color="white", fontweight="bold")
        ax.text(0.10 + i * 0.27, 0.30, row["size_label"], ha="center", fontsize=10)
    ax.set_xlim(0, 1)
    ax.set_ylim(0.15, 0.85)
    ax.axis("off")
    fig.tight_layout()
    out = here / "figures"
    out.mkdir(exist_ok=True)
    fig.savefig(out / "multiscale_graphical_abstract.png", dpi=300)
    fig.savefig(out / "multiscale_graphical_abstract.svg")
    plt.close(fig)
    print(f"Wrote {out / 'multiscale_graphical_abstract.png'}")


if __name__ == "__main__":
    main()
