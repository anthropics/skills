#!/usr/bin/env python3
"""XRD phase identification: Al2O3 + t-ZrO2 + m-ZrO2."""
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import csv
from pathlib import Path

HERE = Path(__file__).resolve().parent
rows = list(csv.DictReader(open(HERE / "source_data.csv")))
tth = [float(r["two_theta"]) for r in rows]

fig, ax = plt.subplots(figsize=(6, 3.5))
ax.plot(tth, [float(r["alumina_intensity"]) for r in rows], label="Al₂O₃", lw=1)
ax.plot(tth, [float(r["zirconia_t_intensity"]) for r in rows], label="t-ZrO₂", lw=1)
ax.plot(tth, [float(r["zirconia_m_intensity"]) for r in rows], "--", label="m-ZrO₂", lw=1, alpha=0.7)
ax.set(xlabel="2θ (°)", ylabel="Intensity (a.u.)")
ax.legend(fontsize=8)
ax.set_title("XRD Pattern: Al₂O₃-ZrO₂ Composite", fontsize=10)

# Annotate key peaks
for pos, lbl in [(30.2, "t-ZrO₂ (101)"), (35.2, "Al₂O₃ (104)"), (43.4, "Al₂O₃ (113)"), (50.2, "t-ZrO₂ (200)"), (60.2, "t-ZrO₂ (211)")]:
    ax.annotate(lbl, (pos, ax.get_ylim()[1] * 0.85), fontsize=6, rotation=45, ha="center")

fig.tight_layout()
fig.savefig(HERE / "figure.png", dpi=300)
print("Figure saved")
