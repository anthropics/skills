"""Ceramic Nyquist plot for electrochemical impedance spectroscopy.

Reads data/synthetic.csv (freq_Hz, Z_real_ohm, Z_imag_ohm) and renders
the classic Nyquist diagram.
"""
from __future__ import annotations

import csv
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

PRIMARY = "#3775BA"

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
    zr = [float(r["Z_real_ohm"]) for r in rows]
    zi = [float(r["Z_imag_ohm"]) for r in rows]
    fig, ax = plt.subplots(figsize=(6.5, 5.5))
    ax.plot(zr, [-v for v in zi], "o-", color=PRIMARY, lw=1.8, ms=6)
    ax.set_xlabel("Z' (\u03a9)")
    ax.set_ylabel("-Z'' (\u03a9)")
    ax.set_aspect("equal")
    ax.axhline(0, color="black", lw=0.6, ls="--", alpha=0.5)
    fig.tight_layout()
    out = here / "figures"
    out.mkdir(exist_ok=True)
    fig.savefig(out / "ceramic_nyquist_plot.png", dpi=300)
    fig.savefig(out / "ceramic_nyquist_plot.svg")
    plt.close(fig)
    print(f"Wrote {out / 'ceramic_nyquist_plot.png'}")


if __name__ == "__main__":
    main()
