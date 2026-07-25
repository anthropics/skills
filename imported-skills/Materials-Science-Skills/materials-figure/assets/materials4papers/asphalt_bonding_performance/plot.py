"""
Asphalt bonding performance comparison for different modifiers.
Construction and Building Materials (CBM) style -- grouped bar chart with
dual Y-axis showing bond strength and retention rate.

Synthetic data: WER (waste engine oil residue), SBS, and EVA modifiers
under dry, wet, and aged conditions.
"""

import os
import csv
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from pathlib import Path

# ============================================================
# Publication rcParams
# ============================================================
matplotlib.rcParams.update({
    "font.family": "Arial",
    "font.size": 9,
    "axes.linewidth": 0.8,
    "xtick.major.width": 0.6,
    "ytick.major.width": 0.6,
    "xtick.minor.width": 0.4,
    "ytick.minor.width": 0.4,
    "xtick.major.size": 3,
    "ytick.major.size": 3,
    "xtick.direction": "in",
    "ytick.direction": "in",
    "axes.labelsize": 10,
    "axes.titlesize": 10,
    "legend.fontsize": 8,
    "figure.dpi": 300,
    "savefig.dpi": 300,
    "savefig.bbox": "tight",
    "pdf.fonttype": 42,
    "svg.fonttype": "none",
})

OUT_DIR = Path(__file__).resolve().parent
DATA_DIR = OUT_DIR / "data"
FIG_DIR = OUT_DIR / "figures"
DATA_DIR.mkdir(exist_ok=True)
FIG_DIR.mkdir(exist_ok=True)

# ============================================================
# Experimental data (synthetic but realistic)
# ============================================================
# Bond strength [MPa] and retention rate [%] for three modifiers
# Conditions: dry, wet (water immersion), aged (RTFOT + UV)

MODIFIERS = ["WER", "SBS", "EVA"]
CONDITIONS = ["Dry", "Wet", "Aged"]

# Bond strength data: shape (3 modifiers, 3 conditions)
BOND_STRENGTH = np.array([
    [0.82, 0.65, 0.58],  # WER
    [0.95, 0.78, 0.71],  # SBS
    [0.76, 0.61, 0.54],  # EVA
])

BOND_STD = np.array([
    [0.06, 0.08, 0.07],  # WER
    [0.07, 0.06, 0.05],  # SBS
    [0.05, 0.07, 0.06],  # EVA
])

# Retention rate [%] relative to dry condition
RETENTION_RATE = np.array([
    [100.0, 79.3, 70.7],  # WER
    [100.0, 82.1, 74.7],  # SBS
    [100.0, 80.3, 71.1],  # EVA
])

RETENTION_STD = np.array([
    [0.0, 4.2, 3.8],  # WER
    [0.0, 3.5, 2.9],  # SBS
    [0.0, 3.9, 3.4],  # EVA
])


def main():
    print("Generating asphalt bonding performance figure ...")

    n_modifiers = len(MODIFIERS)
    n_conditions = len(CONDITIONS)

    # Bar positions
    x = np.arange(n_conditions)
    width = 0.25

    fig, ax1 = plt.subplots(figsize=(6.0, 4.2))

    # Colors for each modifier
    colors = {"WER": "#FF7043", "SBS": "#42A5F5", "EVA": "#66BB6A"}

    # Plot bond strength on primary Y-axis
    for i, mod in enumerate(MODIFIERS):
        offset = (i - 1) * width
        bars = ax1.bar(
            x + offset, BOND_STRENGTH[i], width,
            yerr=BOND_STD[i],
            color=colors[mod], edgecolor="black", linewidth=0.6,
            capsize=3, error_kw={"elinewidth": 0.8, "ecolor": "black", "capthick": 0.8},
            label=f"{mod} (strength)", zorder=2,
        )

    ax1.set_xlabel("Test condition")
    ax1.set_ylabel("Bond strength  [MPa]", color="black")
    ax1.set_xticks(x)
    ax1.set_xticklabels(CONDITIONS)
    ax1.set_ylim(0, 1.2)
    ax1.tick_params(axis="y", labelcolor="black")
    ax1.grid(axis="y", linestyle="--", alpha=0.3, lw=0.5)
    ax1.set_axisbelow(True)

    # Create secondary Y-axis for retention rate
    ax2 = ax1.twinx()

    # Plot retention rate as line with markers
    for i, mod in enumerate(MODIFIERS):
        ax2.plot(
            x, RETENTION_RATE[i], "o-", color=colors[mod],
            markersize=6, linewidth=1.5, markeredgecolor="black",
            markeredgewidth=0.8, label=f"{mod} (retention)", zorder=3,
        )
        # Add error bars for retention
        ax2.errorbar(
            x, RETENTION_RATE[i], yerr=RETENTION_STD[i],
            fmt="none", ecolor=colors[mod], elinewidth=1.0,
            capsize=3, capthick=1.0, alpha=0.5,
        )

    ax2.set_ylabel("Retention rate  [%]", color="black")
    ax2.set_ylim(60, 110)
    ax2.tick_params(axis="y", labelcolor="black")

    # Combine legends
    lines1, labels1 = ax1.get_legend_handles_labels()
    lines2, labels2 = ax2.get_legend_handles_labels()
    ax1.legend(lines1 + lines2, labels1 + labels2,
               loc="lower left", frameon=True, framealpha=0.9, edgecolor="#CCCCCC")

    ax1.set_title("Asphalt bonding performance under different conditions",
                  fontweight="bold")

    fig.tight_layout()
    out = FIG_DIR / "bonding_performance.png"
    fig.savefig(out)
    plt.close(fig)
    print(f"Saved: {out}")

    # ---- save CSV data ----
    csv_path = DATA_DIR / "bonding_performance.csv"
    with open(csv_path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow([
            "modifier", "condition",
            "bond_strength_MPa", "bond_strength_std_MPa",
            "retention_rate_pct", "retention_rate_std_pct",
        ])
        for i, mod in enumerate(MODIFIERS):
            for j, cond in enumerate(CONDITIONS):
                w.writerow([
                    mod, cond,
                    f"{BOND_STRENGTH[i, j]:.3f}", f"{BOND_STD[i, j]:.3f}",
                    f"{RETENTION_RATE[i, j]:.1f}", f"{RETENTION_STD[i, j]:.1f}",
                ])
    print(f"Saved: {csv_path}")


if __name__ == "__main__":
    main()
