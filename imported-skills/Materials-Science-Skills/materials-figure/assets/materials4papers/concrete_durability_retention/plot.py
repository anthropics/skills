"""
Concrete durability retention comparison between control and modified groups.
Construction and Building Materials (CBM) style -- grouped bar chart with
error bars and significance annotations (*, **, ***).

Synthetic data: freeze-thaw, carbonation, and chloride ingress resistance
for plain concrete (control) vs nano-modified concrete.
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
# Durability retention (%) after accelerated testing
# Three durability indices: freeze-thaw (F-T), carbonation (Carb), chloride (Cl)
# Each measured with n=6 specimens, reported as mean +/- std

GROUPS = ["Freeze-thaw", "Carbonation", "Chloride ingress"]

# Control group: plain concrete C40
CONTROL_MEAN = np.array([72.3, 61.8, 58.4])
CONTROL_STD  = np.array([4.1, 5.6, 3.9])

# Modified group: nano-silica + fly ash composite
MODIFIED_MEAN = np.array([89.6, 82.4, 79.1])
MODIFIED_STD  = np.array([3.2, 4.3, 3.5])

# p-values from independent t-test (two-tailed)
P_VALUES = np.array([0.0008, 0.0021, 0.0065])


def significance_label(p):
    """Return significance annotation string."""
    if p < 0.001:
        return "***"
    elif p < 0.01:
        return "**"
    elif p < 0.05:
        return "*"
    return "n.s."


def main():
    print("Generating concrete durability retention figure ...")

    n_groups = len(GROUPS)
    x = np.arange(n_groups)
    width = 0.32

    fig, ax = plt.subplots(figsize=(5.0, 3.8))

    # Control bars
    bars_ctrl = ax.bar(
        x - width / 2, CONTROL_MEAN, width,
        yerr=CONTROL_STD,
        color="#B0BEC5", edgecolor="#455A64", linewidth=0.8,
        capsize=4, error_kw={"elinewidth": 1.0, "ecolor": "#455A64", "capthick": 1.0},
        label="Control (plain concrete)", zorder=2,
    )

    # Modified bars
    bars_mod = ax.bar(
        x + width / 2, MODIFIED_MEAN, width,
        yerr=MODIFIED_STD,
        color="#42A5F5", edgecolor="#1565C0", linewidth=0.8,
        capsize=4, error_kw={"elinewidth": 1.0, "ecolor": "#1565C0", "capthick": 1.0},
        label="Modified (nano-silica + FA)", zorder=2,
    )

    # Significance brackets and annotations
    bracket_y_top = max(CONTROL_MEAN.max(), MODIFIED_MEAN.max()) + 10
    for i in range(n_groups):
        label = significance_label(P_VALUES[i])
        # Draw bracket
        x_left = x[i] - width / 2
        x_right = x[i] + width / 2
        ax.plot([x_left, x_left, x_right, x_right],
                [bracket_y_top, bracket_y_top + 2, bracket_y_top + 2, bracket_y_top],
                color="black", lw=0.8)
        ax.text(x[i], bracket_y_top + 3, label,
                ha="center", va="bottom", fontsize=10, fontweight="bold")

    ax.set_ylabel("Durability retention  [%]")
    ax.set_xticks(x)
    ax.set_xticklabels(GROUPS)
    ax.set_ylim(0, 110)
    ax.set_title("Durability retention after accelerated tests", fontweight="bold")
    ax.legend(loc="lower left", frameon=True, framealpha=0.9, edgecolor="#CCCCCC")
    ax.grid(axis="y", linestyle="--", alpha=0.3, lw=0.5)
    ax.set_axisbelow(True)

    # Add individual data points as jittered dots
    rng = np.random.RandomState(42)
    for i in range(n_groups):
        # Control jitter
        ctrl_pts = np.clip(
            CONTROL_MEAN[i] + rng.normal(0, CONTROL_STD[i], 6), 0, 100
        )
        jitter_ctrl = x[i] - width / 2 + rng.uniform(-0.06, 0.06, 6)
        ax.scatter(jitter_ctrl, ctrl_pts, color="#455A64", s=12, zorder=3,
                   alpha=0.6, edgecolors="none")

        # Modified jitter
        mod_pts = np.clip(
            MODIFIED_MEAN[i] + rng.normal(0, MODIFIED_STD[i], 6), 0, 100
        )
        jitter_mod = x[i] + width / 2 + rng.uniform(-0.06, 0.06, 6)
        ax.scatter(jitter_mod, mod_pts, color="#1565C0", s=12, zorder=3,
                   alpha=0.6, edgecolors="none")

    fig.tight_layout()
    out = FIG_DIR / "durability_retention.png"
    fig.savefig(out)
    plt.close(fig)
    print(f"Saved: {out}")

    # ---- save CSV data ----
    csv_path = DATA_DIR / "durability_retention.csv"
    with open(csv_path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow([
            "test_type",
            "control_mean_pct", "control_std_pct",
            "modified_mean_pct", "modified_std_pct",
            "p_value", "significance",
        ])
        for i in range(n_groups):
            w.writerow([
                GROUPS[i],
                f"{CONTROL_MEAN[i]:.1f}", f"{CONTROL_STD[i]:.1f}",
                f"{MODIFIED_MEAN[i]:.1f}", f"{MODIFIED_STD[i]:.1f}",
                f"{P_VALUES[i]:.4f}", significance_label(P_VALUES[i]),
            ])
    print(f"Saved: {csv_path}")


if __name__ == "__main__":
    main()
