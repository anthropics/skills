"""Multifield temperature vs strain for polymer thermal expansion.

Reads data/synthetic.csv (temperature_c, strain_pct, time_min) and plots
strain versus temperature (color-coded by time).
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
    t = [float(r["temperature_c"]) for r in rows]
    eps = [float(r["strain_pct"]) for r in rows]
    tm = [float(r["time_min"]) for r in rows]
    fig, ax1 = plt.subplots(figsize=(7, 4.2))
    ax1.plot(t, eps, "o-", color=PRIMARY, lw=2, ms=7, label="strain")
    ax1.set_xlabel("Temperature (\u00b0C)")
    ax1.set_ylabel("Strain (%)", color=PRIMARY)
    ax1.tick_params(axis="y", labelcolor=PRIMARY)
    ax2 = ax1.twinx()
    ax2.plot(t, tm, "s--", color=ACCENT, lw=1.5, ms=6, label="time")
    ax2.set_ylabel("Time (min)", color=ACCENT)
    ax2.tick_params(axis="y", labelcolor=ACCENT)
    fig.tight_layout()
    out = here / "figures"
    out.mkdir(exist_ok=True)
    fig.savefig(out / "multifield_temperature_strain.png", dpi=300)
    fig.savefig(out / "multifield_temperature_strain.svg")
    plt.close(fig)
    print(f"Wrote {out / 'multifield_temperature_strain.png'}")


if __name__ == "__main__":
    main()
