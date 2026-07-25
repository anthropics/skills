"""Asphalt fracture CT slice reconstruction (crack area and count vs depth).

Reads data/synthetic.csv (slice_z_um, crack_area_um2, crack_count) and
plots the crack profile through a 3D specimen.
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
    z = [float(r["slice_z_um"]) for r in rows]
    a = [float(r["crack_area_um2"]) for r in rows]
    n = [float(r["crack_count"]) for r in rows]
    fig, ax1 = plt.subplots(figsize=(7, 4.2))
    bars = ax1.bar(z, a, width=80, color=PRIMARY, edgecolor="black", linewidth=0.8, label="area")
    ax1.set_xlabel("Slice z (\u00b5m)")
    ax1.set_ylabel("Crack area (\u00b5m\u00b2)", color=PRIMARY)
    ax1.tick_params(axis="y", labelcolor=PRIMARY)
    ax2 = ax1.twinx()
    ax2.plot(z, n, "D-", color=ACCENT, lw=1.8, ms=7, label="count")
    ax2.set_ylabel("Crack count", color=ACCENT)
    ax2.tick_params(axis="y", labelcolor=ACCENT)
    fig.tight_layout()
    out = here / "figures"
    out.mkdir(exist_ok=True)
    fig.savefig(out / "asphalt_fracture_ct_reconstruction.png", dpi=300)
    fig.savefig(out / "asphalt_fracture_ct_reconstruction.svg")
    plt.close(fig)
    print(f"Wrote {out / 'asphalt_fracture_ct_reconstruction.png'}")


if __name__ == "__main__":
    main()
