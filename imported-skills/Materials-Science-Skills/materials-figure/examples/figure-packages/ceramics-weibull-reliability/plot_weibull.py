#!/usr/bin/env python3
"""Weibull reliability: 3Y-TZP vs 3Y-TZP + 0.5wt% Al2O3 strength distribution."""

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
import csv
from pathlib import Path

HERE = Path(__file__).resolve().parent
rows = list(csv.DictReader(open(HERE / "source_data.csv")))
s_3y = sorted(float(r["strength_3Y"]) for r in rows)
s_3y_al = sorted(float(r["strength_3Y_Al2O3"]) for r in rows)

def weibull_plot(strengths, label, color):
    s = np.array(strengths)
    n = len(s)
    F = (np.arange(1, n + 1) - 0.3) / (n + 0.4)
    ln_s = np.log(s)
    ln_ln = np.log(-np.log(1 - F))
    m = np.polyfit(ln_s, ln_ln, 1)[0]
    ax.plot(ln_s, ln_ln, "o-", color=color, linewidth=1.5, markersize=6,
            label=f"{label} (m={m:.1f})")

fig, ax = plt.subplots(figsize=(6, 4.5))
weibull_plot(s_3y, "3Y-TZP", "#4B6F8A")
weibull_plot(s_3y_al, "3Y-TZP + 0.5wt% Al₂O₃", "#C47B45")

ax.set_xlabel("ln(fracture strength) (MPa)")
ax.set_ylabel("ln(ln(1/(1-P_f)))")
ax.set_title("Weibull Plot: 3Y-TZP vs Al₂O₃-Doped", fontsize=11)
ax.legend(fontsize=9)
ax.spines["top"].set_visible(False)
ax.spines["right"].set_visible(False)
fig.tight_layout()
fig.savefig(HERE / "figure.png", dpi=300)
print("Figure saved")
