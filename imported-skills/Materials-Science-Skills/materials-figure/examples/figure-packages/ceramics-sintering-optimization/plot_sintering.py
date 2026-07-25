#!/usr/bin/env python3
"""Sintering optimization: density and grain size vs temperature."""
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import csv
from pathlib import Path

HERE = Path(__file__).resolve().parent
rows = list(csv.DictReader(open(HERE / "source_data.csv")))
T = [int(r["temperature"]) for r in rows]

fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(8, 3.5))

ax1.plot(T, [float(r["Al2O3_density"]) for r in rows], "o-", label="Al₂O₃")
ax1.plot(T, [float(r["Al2O3_SiC_density"]) for r in rows], "s--", label="Al₂O₃-5SiC")
ax1.set(xlabel="Sintering Temperature (°C)", ylabel="Relative Density (g/cm³)")
ax1.legend()

ax2.plot(T, [float(r["Al2O3_grain_size"]) for r in rows], "o-", label="Al₂O₃")
ax2.plot(T, [float(r["Al2O3_SiC_grain_size"]) for r in rows], "s--", label="Al₂O₃-5SiC")
ax2.set(xlabel="Sintering Temperature (°C)", ylabel="Grain Size (µm)")
ax2.legend()

fig.tight_layout()
fig.savefig(HERE / "figure.png", dpi=300)
print("Figure saved")
