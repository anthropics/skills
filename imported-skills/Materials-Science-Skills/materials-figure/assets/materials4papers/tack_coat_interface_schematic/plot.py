"""
Tack coat interface schematic diagram for pavement structure.
Construction and Building Materials (CBM) style -- engineering cross-section
schematic showing tack coat layer location, test points, and interface
transition zone.

No data file needed (pure schematic diagram).
"""

import os
import csv
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.patches import FancyArrowPatch, FancyBboxPatch
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


def draw_hatch_pattern(ax, x_start, x_end, y_bottom, y_top, color, label):
    """Draw a filled layer with optional hatching."""
    rect = mpatches.Rectangle(
        (x_start, y_bottom), x_end - x_start, y_top - y_bottom,
        facecolor=color, edgecolor="black", linewidth=0.8, zorder=1,
    )
    ax.add_patch(rect)
    return rect


def main():
    print("Generating tack coat interface schematic ...")

    fig, ax = plt.subplots(figsize=(7.0, 5.5))

    # Pavement cross-section coordinates
    x_left = 1.0
    x_right = 13.0
    x_mid = (x_left + x_right) / 2

    # Layer boundaries (y values, bottom to top)
    y_subgrade_top = 0.8
    y_base_bottom = y_subgrade_top
    y_base_top = 2.2
    y_lower_ac_bottom = y_base_top
    y_lower_ac_top = 3.4
    y_tack_bottom = y_lower_ac_top
    y_tack_top = y_tack_bottom + 0.12  # thin tack coat layer
    y_upper_ac_bottom = y_tack_top
    y_upper_ac_top = 5.0

    # ===== Draw pavement layers =====

    # Subgrade (hatched)
    draw_hatch_pattern(ax, x_left, x_right, 0, y_subgrade_top,
                        "#D7CCC8", "Subgrade")
    # Add hatch overlay for subgrade
    rect_hatch = mpatches.Rectangle(
        (x_left, 0), x_right - x_left, y_subgrade_top,
        hatch="///", facecolor="none", edgecolor="#8D6E63",
        linewidth=0.5, zorder=2,
    )
    ax.add_patch(rect_hatch)

    # Base course
    draw_hatch_pattern(ax, x_left, x_right, y_base_bottom, y_base_top,
                        "#BCAAA4", "Base course")
    rect_hatch2 = mpatches.Rectangle(
        (x_left, y_base_bottom), x_right - x_left, y_base_top - y_base_bottom,
        hatch="...", facecolor="none", edgecolor="#795548",
        linewidth=0.5, zorder=2,
    )
    ax.add_patch(rect_hatch2)

    # Lower asphalt concrete (AC)
    draw_hatch_pattern(ax, x_left, x_right, y_lower_ac_bottom, y_lower_ac_top,
                        "#616161", "Lower AC (coarse)")

    # Tack coat layer (emphasized)
    rect_tack = mpatches.Rectangle(
        (x_left, y_tack_bottom), x_right - x_left, y_tack_top - y_tack_bottom,
        facecolor="#FFC107", edgecolor="#E65100", linewidth=1.2,
        linestyle="-", zorder=4,
    )
    ax.add_patch(rect_tack)

    # Upper asphalt concrete (AC)
    draw_hatch_pattern(ax, x_left, x_right, y_upper_ac_bottom, y_upper_ac_top,
                        "#424242", "Upper AC (fine)")

    # ===== Interface transition zone (highlighted) =====
    # Show the transition zone around tack coat
    zone_margin = 0.3
    rect_zone = mpatches.Rectangle(
        (x_left - 0.15, y_tack_bottom - zone_margin),
        x_right - x_left + 0.3,
        y_tack_top - y_tack_bottom + 2 * zone_margin,
        facecolor="none", edgecolor="#E65100", linewidth=1.5,
        linestyle="--", zorder=5,
    )
    ax.add_patch(rect_zone)

    # ===== Annotations: layer labels on the right =====
    label_x = x_right + 0.5
    ax.annotate("Upper AC layer\n(surface course)",
                xy=(x_right, (y_upper_ac_bottom + y_upper_ac_top) / 2),
                xytext=(label_x + 0.5, (y_upper_ac_bottom + y_upper_ac_top) / 2),
                fontsize=8, va="center",
                arrowprops=dict(arrowstyle="->", color="black", lw=0.8))

    ax.annotate("Tack coat\n(emulsion residue)",
                xy=(x_right, (y_tack_bottom + y_tack_top) / 2),
                xytext=(label_x + 0.5, y_tack_top + 0.6),
                fontsize=8, va="center", color="#E65100", fontweight="bold",
                arrowprops=dict(arrowstyle="->", color="#E65100", lw=1.0))

    ax.annotate("Lower AC layer\n(binder course)",
                xy=(x_right, (y_lower_ac_bottom + y_lower_ac_top) / 2),
                xytext=(label_x + 0.5, (y_lower_ac_bottom + y_lower_ac_top) / 2),
                fontsize=8, va="center",
                arrowprops=dict(arrowstyle="->", color="black", lw=0.8))

    ax.annotate("Base course",
                xy=(x_right, (y_base_bottom + y_base_top) / 2),
                xytext=(label_x + 0.5, (y_base_bottom + y_base_top) / 2),
                fontsize=8, va="center",
                arrowprops=dict(arrowstyle="->", color="black", lw=0.8))

    ax.annotate("Subgrade",
                xy=(x_right, y_subgrade_top / 2),
                xytext=(label_x + 0.5, y_subgrade_top / 2),
                fontsize=8, va="center",
                arrowprops=dict(arrowstyle="->", color="black", lw=0.8))

    # ===== Interface transition zone annotation =====
    ax.annotate("Interface transition\nzone (bonded region)",
                xy=(x_right + 0.05, y_tack_top + 0.05),
                xytext=(x_left - 0.8, y_tack_top + 0.9),
                fontsize=7, va="center", color="#E65100",
                arrowprops=dict(arrowstyle="->", color="#E65100", lw=0.8,
                                connectionstyle="arc3,rad=-0.3"))

    # ===== Test points on tack coat interface =====
    test_x_positions = [3.0, 5.5, 8.0, 10.5]
    for i, tx in enumerate(test_x_positions):
        # Test point marker (diamond)
        ax.plot(tx, y_tack_top, marker="D", markersize=7,
                color="#D32F2F", markeredgecolor="black", markeredgewidth=0.6,
                zorder=6)
        # Label
        ax.text(tx, y_tack_top - 0.25, f"P{i+1}", fontsize=7,
                ha="center", va="top", fontweight="bold", color="#D32F2F")

    # Test points legend
    ax.annotate("Bond strength\ntest points",
                xy=(test_x_positions[2], y_tack_top),
                xytext=(test_x_positions[2], y_upper_ac_top + 0.5),
                fontsize=7, ha="center", va="bottom", color="#D32F2F",
                arrowprops=dict(arrowstyle="->", color="#D32F2F", lw=0.8))

    # ===== Dimension lines on the left =====
    dim_x = x_left - 0.4
    # Upper AC thickness
    ax.annotate("", xy=(dim_x, y_upper_ac_bottom),
                xytext=(dim_x, y_upper_ac_top),
                arrowprops=dict(arrowstyle="<->", color="black", lw=0.8))
    ax.text(dim_x - 0.15, (y_upper_ac_bottom + y_upper_ac_top) / 2,
            "40\u201350 mm", fontsize=6, ha="right", va="center", rotation=90)

    # Tack coat application rate
    ax.annotate("", xy=(dim_x, y_tack_bottom),
                xytext=(dim_x, y_tack_top),
                arrowprops=dict(arrowstyle="<->", color="#E65100", lw=1.0))
    ax.text(dim_x - 0.15, (y_tack_bottom + y_tack_top) / 2,
            "0.2\u20130.6 L/m\u00b2", fontsize=6, ha="right", va="center",
            rotation=90, color="#E65100")

    # Lower AC thickness
    ax.annotate("", xy=(dim_x, y_lower_ac_bottom),
                xytext=(dim_x, y_lower_ac_top),
                arrowprops=dict(arrowstyle="<->", color="black", lw=0.8))
    ax.text(dim_x - 0.15, (y_lower_ac_bottom + y_lower_ac_top) / 2,
            "60\u201380 mm", fontsize=6, ha="right", va="center", rotation=90)

    # ===== Aggregate particles in AC layers (schematic) =====
    rng = np.random.RandomState(123)

    # Upper AC: fine aggregate (small circles)
    for _ in range(35):
        ax.plot(rng.uniform(x_left + 0.2, x_right - 0.2),
                rng.uniform(y_upper_ac_bottom + 0.1, y_upper_ac_top - 0.1),
                "o", color="#9E9E9E", markersize=rng.uniform(2, 4),
                alpha=0.5, zorder=3)

    # Lower AC: coarse aggregate (larger circles)
    for _ in range(25):
        ax.plot(rng.uniform(x_left + 0.2, x_right - 0.2),
                rng.uniform(y_lower_ac_bottom + 0.1, y_lower_ac_top - 0.1),
                "o", color="#BDBDBD", markersize=rng.uniform(4, 7),
                alpha=0.4, zorder=3, markeredgecolor="#757575",
                markeredgewidth=0.3)

    # Tack coat droplets (small yellow dots along interface)
    for _ in range(50):
        ax.plot(rng.uniform(x_left + 0.1, x_right - 0.1),
                rng.uniform(y_tack_bottom + 0.01, y_tack_top - 0.01),
                ".", color="#FF8F00", markersize=2, alpha=0.7, zorder=5)

    # ===== Axes setup =====
    ax.set_xlim(-0.5, 17.5)
    ax.set_ylim(-0.3, 6.5)
    ax.set_aspect("equal")
    ax.set_title("Tack coat interface in flexible pavement structure",
                 fontweight="bold", fontsize=11, pad=12)
    ax.set_xlabel("Cross-section width  [mm, not to scale]")
    ax.set_ylabel("Pavement depth  [mm, not to scale]")
    ax.set_xticks([])
    ax.set_yticks([])

    # ===== Legend =====
    legend_elements = [
        mpatches.Patch(facecolor="#424242", edgecolor="black", label="Upper AC (SMA-13)"),
        mpatches.Patch(facecolor="#FFC107", edgecolor="#E65100", label="Tack coat (CRS-2P)"),
        mpatches.Patch(facecolor="#616161", edgecolor="black", label="Lower AC (AC-20)"),
        mpatches.Patch(facecolor="#BCAAA4", edgecolor="black", hatch="...",
                       label="Base course (granular)"),
        mpatches.Patch(facecolor="#D7CCC8", edgecolor="black", hatch="///",
                       label="Subgrade (compacted soil)"),
        plt.Line2D([0], [0], marker="D", color="w", markerfacecolor="#D32F2F",
                   markeredgecolor="black", markersize=7, label="Test point (pull-off)"),
        mpatches.Patch(facecolor="none", edgecolor="#E65100", linestyle="--",
                       linewidth=1.5, label="Interface transition zone"),
    ]
    ax.legend(handles=legend_elements, loc="upper right",
              frameon=True, framealpha=0.95, edgecolor="#999999",
              fontsize=7, ncol=1)

    fig.tight_layout()
    out = FIG_DIR / "tack_coat_interface.png"
    fig.savefig(out)
    plt.close(fig)
    print(f"Saved: {out}")

    # ---- save schematic metadata as CSV ----
    csv_path = DATA_DIR / "schematic_layers.csv"
    with open(csv_path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["layer", "material", "thickness_mm", "color_hex"])
        w.writerow(["Surface course", "Upper AC (SMA-13)", "40-50", "#424242"])
        w.writerow(["Tack coat", "CRS-2P emulsion", "0.2-0.6 L/m2", "#FFC107"])
        w.writerow(["Binder course", "Lower AC (AC-20)", "60-80", "#616161"])
        w.writerow(["Base course", "Granular base", "150-200", "#BCAAA4"])
        w.writerow(["Subgrade", "Compacted soil", "Variable", "#D7CCC8"])
    print(f"Saved: {csv_path}")


if __name__ == "__main__":
    main()
