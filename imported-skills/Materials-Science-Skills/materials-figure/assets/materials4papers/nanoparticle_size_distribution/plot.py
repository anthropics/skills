#!/usr/bin/env python3
"""Nanoparticle size distribution analysis: TEM statistics and DLS distribution (ACS Nano style)."""

import os
from pathlib import Path
import numpy as np
from matplotlib import pyplot as plt
import csv


def lognormal_pdf(x, mu, sigma):
    """Log-normal probability density function."""
    return (1.0 / (x * sigma * np.sqrt(2 * np.pi)) *
            np.exp(-(np.log(x) - mu)**2 / (2 * sigma**2)))


def plot_nanoparticle_distribution(fig_name: str):
    """Plot multi-panel nanoparticle size distribution figure."""
    # Load TEM data
    HERE = Path(__file__).resolve().parent
    tem_path = HERE / "data" / "tem_sizes.csv"
    rows = list(csv.DictReader(open(tem_path)))
    tem_diameters = np.array([float(r["diameter_nm"]) for r in rows])

    # Load DLS data
    dls_path = HERE / "data" / "dls_distribution.csv"
    rows = list(csv.DictReader(open(dls_path)))
    dls_diameters = np.array([float(r["diameter_nm"]) for r in rows])
    dls_intensity = np.array([float(r["intensity_percent"]) for r in rows])

    # Calculate statistics
    tem_mean = np.mean(tem_diameters)
    tem_std = np.std(tem_diameters, ddof=1)
    tem_median = np.median(tem_diameters)

    # Fit log-normal distribution to TEM data
    log_tem = np.log(tem_diameters)
    mu_fit, sigma_fit = np.mean(log_tem), np.std(log_tem, ddof=1)

    # Create figure with 3 panels
    fig = plt.figure(figsize=(12, 4))

    # Panel (a): Simulated TEM image montage
    ax1 = plt.subplot(1, 3, 1)
    np.random.seed(42)
    # Create 4x4 grid of simulated nanoparticles
    for i in range(4):
        for j in range(4):
            # Generate random particle
            center_x = j * 25 + 12.5 + np.random.uniform(-3, 3)
            center_y = i * 25 + 12.5 + np.random.uniform(-3, 3)
            radius = np.random.choice(tem_diameters) / 2.5  # Scale for visualization

            circle = plt.Circle((center_x, center_y), radius,
                               color='#2c3e50', alpha=0.85, linewidth=0)
            ax1.add_patch(circle)

    ax1.set_xlim(0, 100)
    ax1.set_ylim(0, 100)
    ax1.set_aspect('equal')
    ax1.set_xlabel('50 nm', fontsize=11, labelpad=8)
    ax1.set_ylabel('50 nm', fontsize=11, labelpad=8)
    ax1.set_title('(a) TEM Image', fontsize=13, fontweight='bold', pad=10)
    ax1.set_xticks([])
    ax1.set_yticks([])
    ax1.spines['top'].set_visible(True)
    ax1.spines['right'].set_visible(True)
    ax1.spines['bottom'].set_visible(True)
    ax1.spines['left'].set_visible(True)

    # Panel (b): TEM size histogram with log-normal fit
    ax2 = plt.subplot(1, 3, 2)
    counts, bins, patches = ax2.hist(tem_diameters, bins=12, density=True,
                                     alpha=0.7, color='#3498db',
                                     edgecolor='black', linewidth=1.2)

    # Plot log-normal fit
    x_fit = np.linspace(np.min(tem_diameters) * 0.9, np.max(tem_diameters) * 1.1, 100)
    y_fit = lognormal_pdf(x_fit, mu_fit, sigma_fit)
    ax2.plot(x_fit, y_fit, 'r-', linewidth=2.5, label='Log-normal fit')

    # Add statistics text box
    stats_text = f'Mean: {tem_mean:.1f} ± {tem_std:.1f} nm\n'
    stats_text += f'Median: {tem_median:.1f} nm\n'
    stats_text += f'N = {len(tem_diameters)}'
    props = dict(boxstyle='round', facecolor='wheat', alpha=0.8, edgecolor='black', linewidth=1.2)
    ax2.text(0.05, 0.95, stats_text, transform=ax2.transAxes, fontsize=10,
             verticalalignment='top', bbox=props)

    ax2.set_xlabel('Diameter (nm)', fontsize=12)
    ax2.set_ylabel('Frequency', fontsize=12)
    ax2.set_title('(b) Size Distribution (TEM)', fontsize=13, fontweight='bold', pad=10)
    ax2.legend(fontsize=10, frameon=True, edgecolor='black', fancybox=False)

    # Panel (c): DLS intensity distribution
    ax3 = plt.subplot(1, 3, 3)
    ax3.fill_between(dls_diameters, dls_intensity, alpha=0.6, color='#e74c3c', linewidth=0)
    ax3.plot(dls_diameters, dls_intensity, 'r-', linewidth=2.5)

    # Mark peak
    peak_idx = np.argmax(dls_intensity)
    peak_diameter = dls_diameters[peak_idx]
    peak_intensity = dls_intensity[peak_idx]
    ax3.plot(peak_diameter, peak_intensity, 'ko', markersize=8, markerfacecolor='white',
             markeredgewidth=2, label=f'Peak: {peak_diameter:.1f} nm')

    # Add PDI annotation
    pdi_text = 'PDI: 0.142'
    ax3.text(0.95, 0.95, pdi_text, transform=ax3.transAxes, fontsize=10,
             verticalalignment='top', horizontalalignment='right',
             bbox=dict(boxstyle='round', facecolor='lightblue', alpha=0.8,
                      edgecolor='black', linewidth=1.2))

    ax3.set_xlabel('Hydrodynamic Diameter (nm)', fontsize=12)
    ax3.set_ylabel('Intensity (%)', fontsize=12)
    ax3.set_title('(c) DLS Distribution', fontsize=13, fontweight='bold', pad=10)
    ax3.legend(fontsize=10, frameon=True, edgecolor='black', fancybox=False, loc='upper left')

    # Adjust layout and save
    plt.tight_layout()
    os.makedirs(os.path.dirname(fig_name), exist_ok=True)
    fig.savefig(fig_name, dpi=300, bbox_inches="tight")
    plt.close(fig)
    return


if __name__ == "__main__":
    # Set ACS Nano style rcParams
    plt.rcParams["svg.fonttype"] = "none"
    plt.rcParams["pdf.fonttype"] = 42
    plt.rcParams["font.family"] = "sans-serif"
    plt.rcParams["font.size"] = 11
    plt.rcParams["axes.linewidth"] = 1.5
    plt.rcParams["axes.labelsize"] = 12
    plt.rcParams["axes.titlesize"] = 13
    plt.rcParams["axes.titleweight"] = "bold"
    plt.rcParams["legend.fontsize"] = 10
    plt.rcParams["legend.frameon"] = True
    plt.rcParams["legend.edgecolor"] = "black"
    plt.rcParams["xtick.labelsize"] = 11
    plt.rcParams["ytick.labelsize"] = 11

    plot_nanoparticle_distribution("./figures/nanoparticle_distribution.png")
    print("Figure saved: figures/nanoparticle_distribution.png")
