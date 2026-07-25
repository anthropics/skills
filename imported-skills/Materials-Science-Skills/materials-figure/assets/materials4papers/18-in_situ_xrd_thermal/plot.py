"""In-situ XRD during thermal annealing for anatase->rutile transition.

Reads data/synthetic.csv (temperature_c, two_theta, phase, intensity) and
plots phase-resolved XRD patterns at the recorded temperatures.
"""
from __future__ import annotations

import csv
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

COLOR_ANATASE = "#3775BA"
COLOR_RUTILE = "#E07C3E"

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
    temps = sorted({int(r["temperature_c"]) for r in rows})
    fig, ax = plt.subplots(figsize=(8, 4.5))
    for i, t in enumerate(temps):
        offset = (len(temps) - 1 - i) * 200
        xs_a, ys_a, xs_r, ys_r = [], [], [], []
        for r in rows:
            if int(r["temperature_c"]) != t:
                continue
            if r["phase"] == "anatase":
                xs_a.append(float(r["two_theta"]))
                ys_a.append(float(r["intensity"]) + offset)
            else:
                xs_r.append(float(r["two_theta"]))
                ys_r.append(float(r["intensity"]) + offset)
        ax.plot(xs_a, ys_a, "o", color=COLOR_ANATASE, ms=5, label="anatase" if i == 0 else None)
        ax.plot(xs_r, ys_r, "s", color=COLOR_RUTILE, ms=5, label="rutile" if i == 0 else None)
        ax.text(82, offset + 50, f"{t} \u00b0C", fontsize=9, color="black", va="center")
    ax.set_xlabel("2\u03b8 (\u00b0)")
    ax.set_ylabel("Intensity (a.u., offset)")
    ax.legend(loc="upper right", frameon=False)
    fig.tight_layout()
    out = here / "figures"
    out.mkdir(exist_ok=True)
    fig.savefig(out / "in_situ_xrd_thermal.png", dpi=300)
    fig.savefig(out / "in_situ_xrd_thermal.svg")
    plt.close(fig)
    print(f"Wrote {out / 'in_situ_xrd_thermal.png'}")


if __name__ == "__main__":
    main()
