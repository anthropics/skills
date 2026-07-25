"""Nano GISAXS 2D pattern for nanoparticle assembly.

Reads data/synthetic.csv (qy_inv_nm, qz_inv_nm, intensity) and renders a
2D scatter of intensity in the qy-qz plane.
"""
from __future__ import annotations

import csv
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

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
    qy = [float(r["qy_inv_nm"]) for r in rows]
    qz = [float(r["qz_inv_nm"]) for r in rows]
    inten = [float(r["intensity"]) for r in rows]
    fig, ax = plt.subplots(figsize=(6.5, 5))
    sc = ax.scatter(qy, qz, c=inten, cmap="viridis", s=320, edgecolors="black", lw=0.6)
    fig.colorbar(sc, ax=ax, label="Intensity (a.u.)")
    ax.set_xlabel("q\u1d67 (nm\u207b\u00b9)")
    ax.set_ylabel("q_z (nm\u207b\u00b9)")
    ax.set_aspect("equal")
    fig.tight_layout()
    out = here / "figures"
    out.mkdir(exist_ok=True)
    fig.savefig(out / "nano_gisaxs_2d.png", dpi=300)
    fig.savefig(out / "nano_gisaxs_2d.svg")
    plt.close(fig)
    print(f"Wrote {out / 'nano_gisaxs_2d.png'}")


if __name__ == "__main__":
    main()
