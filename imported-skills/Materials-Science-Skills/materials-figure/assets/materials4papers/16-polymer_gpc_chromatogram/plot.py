"""Polymer GPC chromatogram for molecular weight distribution.

Reads data/synthetic.csv (elution_mL, intensity) and plots the RI trace.
"""
from __future__ import annotations

import csv
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

PRIMARY = "#3775BA"
ACCENT = "#E07C3E"

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
    x = [float(r["elution_mL"]) for r in rows]
    y = [float(r["intensity"]) for r in rows]
    fig, ax = plt.subplots(figsize=(7, 4.2))
    ax.plot(x, y, color=PRIMARY, lw=2.0)
    ax.fill_between(x, 0, y, color=PRIMARY, alpha=0.25)
    peak_x = x[y.index(max(y))]
    ax.axvline(peak_x, color=ACCENT, ls="--", lw=1)
    ax.text(peak_x, max(y) * 0.95, f" peak = {peak_x:.1f} mL",
            color=ACCENT, fontsize=10, ha="left", va="top")
    ax.set_xlabel("Elution volume (mL)")
    ax.set_ylabel("Intensity (a.u.)")
    fig.tight_layout()
    out = here / "figures"
    out.mkdir(exist_ok=True)
    fig.savefig(out / "polymer_gpc_chromatogram.png", dpi=300)
    fig.savefig(out / "polymer_gpc_chromatogram.svg")
    plt.close(fig)
    print(f"Wrote {out / 'polymer_gpc_chromatogram.png'}")


if __name__ == "__main__":
    main()
