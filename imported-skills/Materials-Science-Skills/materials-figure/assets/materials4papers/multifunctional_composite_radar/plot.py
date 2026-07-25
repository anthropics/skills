#!/usr/bin/env python3
"""Multifunctional composite radar chart (Advanced Functional Materials style)."""

import os
from pathlib import Path
import numpy as np
from matplotlib import pyplot as plt
import csv


def plot_radar_chart(fig_name: str):
    """Plot radar chart comparing multifunctional composite properties."""
    HERE = Path(__file__).resolve().parent

    # Load data
    data_path = HERE / "data" / "composite_properties.csv"
    rows = list(csv.DictReader(open(data_path)))

    # Extract properties
    materials = [r["material"] for r in rows]
    properties = [
        "mechanical_strength",
        "thermal_conductivity",
        "electrical_conductivity",
        "emi_shielding",
        "flame_retardancy",
    ]

    # Build data matrix
    data = []
    for row in rows:
        values = [float(row[prop]) for prop in properties]
        data.append(values)
    data = np.array(data)

    # Number of variables
    num_vars = len(properties)

    # Compute angle for each axis
    angles = np.linspace(0, 2 * np.pi, num_vars, endpoint=False).tolist()
    angles += angles[:1]  # Close the polygon

    # Create figure
    fig, ax = plt.subplots(figsize=(8, 8), subplot_kw=dict(polar=True))

    # Color palette
    colors = ['#E91E63', '#2196F3', '#4CAF50', '#FF9800', '#9C27B0', '#795548']

    # Plot each material
    for i, (material, values) in enumerate(zip(materials, data)):
        values_closed = np.append(values, values[0])
        if material == "Target":
            # Plot target as dashed line
            ax.plot(angles, values_closed, 'k--', linewidth=2.0, label=material,
                    alpha=0.6)
        else:
            # Plot filled polygon for samples
            ax.plot(angles, values_closed, color=colors[i], linewidth=2.0,
                    label=material, marker='o', markersize=6)
            ax.fill(angles, values_closed, color=colors[i], alpha=0.15)

    # Set axis labels
    property_labels = [
        'Mechanical\nStrength',
        'Thermal\nConductivity',
        'Electrical\nConductivity',
        'EMI\nShielding',
        'Flame\nRetardancy',
    ]
    ax.set_xticks(angles[:-1])
    ax.set_xticklabels(property_labels, fontsize=11, fontweight='bold')

    # Set y-axis limits and ticks
    ax.set_ylim(0, 1.0)
    ax.set_yticks([0.2, 0.4, 0.6, 0.8, 1.0])
    ax.set_yticklabels(['0.2', '0.4', '0.6', '0.8', '1.0'], fontsize=9, color='gray')
    ax.set_rlabel_position(30)

    # Add grid lines
    ax.grid(True, linestyle='--', alpha=0.5, linewidth=0.8)

    # Add legend
    ax.legend(loc='upper right', bbox_to_anchor=(1.3, 1.1), fontsize=10,
              frameon=True, edgecolor='black', fancybox=False)

    # Add title
    ax.set_title('Multifunctional Composite Performance', fontsize=14,
                 fontweight='bold', pad=20)

    # Add normalized annotation
    annotation_text = 'Normalized to\nTarget Performance'
    ax.text(0.5, -0.15, annotation_text, transform=ax.transAxes, fontsize=10,
            ha='center', va='top', style='italic', color='gray')

    plt.tight_layout()
    os.makedirs(os.path.dirname(fig_name), exist_ok=True)
    fig.savefig(fig_name, dpi=300, bbox_inches="tight")
    plt.close(fig)


if __name__ == "__main__":
    # Set Advanced Functional Materials style rcParams
    plt.rcParams["svg.fonttype"] = "none"
    plt.rcParams["pdf.fonttype"] = 42
    plt.rcParams["font.family"] = "sans-serif"
    plt.rcParams["font.size"] = 11
    plt.rcParams["axes.linewidth"] = 1.5
    plt.rcParams["axes.labelsize"] = 12
    plt.rcParams["axes.titlesize"] = 14
    plt.rcParams["axes.titleweight"] = "bold"
    plt.rcParams["legend.fontsize"] = 10
    plt.rcParams["legend.frameon"] = True
    plt.rcParams["legend.edgecolor"] = "black"
    plt.rcParams["xtick.labelsize"] = 11
    plt.rcParams["ytick.labelsize"] = 9

    plot_radar_chart("./figures/radar_chart.png")
    print("Figure saved: figures/radar_chart.png")
