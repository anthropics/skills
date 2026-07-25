#!/usr/bin/env python3
"""2D material Raman mapping for graphene characterization (Advanced Materials style)."""

import os
from pathlib import Path
import numpy as np
from matplotlib import pyplot as plt
from matplotlib.colors import Normalize
from matplotlib.patches import Rectangle
import csv


def plot_raman_mapping(fig_name: str):
    """Plot multi-panel Raman mapping figure for graphene."""
    HERE = Path(__file__).resolve().parent

    # Load Raman spectra data
    spectra_path = HERE / "data" / "raman_spectra.csv"
    rows = list(csv.DictReader(open(spectra_path)))
    shift = np.array([float(r["raman_shift_cm"]) for r in rows])
    i_mono = np.array([float(r["intensity_monolayer"]) for r in rows])
    i_bi = np.array([float(r["intensity_bilayer"]) for r in rows])
    i_tri = np.array([float(r["intensity_trilayer"]) for r in rows])

    # Load mapping data
    mapping_path = HERE / "data" / "raman_mapping.csv"
    rows = list(csv.DictReader(open(mapping_path)))
    x_pos = np.array([float(r["x_um"]) for r in rows])
    y_pos = np.array([float(r["y_um"]) for r in rows])
    i2d_ig = np.array([float(r["two_d_over_g"]) for r in rows])
    id_ig = np.array([float(r["d_over_g"]) for r in rows])
    layers = np.array([int(r["layer_count"]) for r in rows])

    # Create figure: 2x2 layout
    fig = plt.figure(figsize=(10, 8))

    # Panel (a): Raman spectra comparison
    ax1 = plt.subplot(2, 2, 1)
    ax1.plot(shift, i_mono, color='#2196F3', linewidth=2.0, label='Monolayer')
    ax1.plot(shift, i_bi, color='#FF9800', linewidth=2.0, label='Bilayer')
    ax1.plot(shift, i_tri, color='#4CAF50', linewidth=2.0, label='Trilayer')

    # Annotate D, G, 2D peaks
    peak_annotations = [
        (1362, 'D', 0.85),
        (1591, 'G', 0.85),
        (2702, '2D', 0.85),
    ]
    y_max = max(np.max(i_mono), np.max(i_bi), np.max(i_tri))
    for pos, label, frac in peak_annotations:
        idx = np.argmin(np.abs(shift - pos))
        peak_val = max(i_mono[idx], i_bi[idx], i_tri[idx])
        ax1.annotate(label, xy=(pos, peak_val), xytext=(pos, y_max * 1.05),
                     fontsize=12, fontweight='bold', ha='center', va='bottom',
                     arrowprops=dict(arrowstyle='->', color='gray', lw=1.2))

    ax1.set_xlabel('Raman Shift (cm\u207b\u00b9)', fontsize=12)
    ax1.set_ylabel('Intensity (a.u.)', fontsize=12)
    ax1.set_title('(a) Raman Spectra', fontsize=13, fontweight='bold', pad=10)
    ax1.legend(fontsize=10, frameon=True, edgecolor='black', fancybox=False,
               loc='upper left')
    ax1.set_xlim(1280, 2820)

    # Panel (b): 2D/G intensity ratio mapping
    ax2 = plt.subplot(2, 2, 2)
    # Reshape data for pcolormesh
    x_unique = np.unique(x_pos)
    y_unique = np.unique(y_pos)
    nx = len(x_unique)
    ny = len(y_unique)

    # Build 2D arrays for each region
    mask_1L = layers == 1
    mask_2L = layers == 2
    mask_3L = layers == 3

    grid_2dg = np.full((ny, nx), np.nan)
    grid_dg = np.full((ny, nx), np.nan)
    grid_layer = np.full((ny, nx), np.nan)

    for i in range(len(x_pos)):
        xi = np.searchsorted(x_unique, x_pos[i])
        yi = np.searchsorted(y_unique, y_pos[i])
        if xi < nx and yi < ny:
            grid_2dg[yi, xi] = i2d_ig[i]
            grid_dg[yi, xi] = id_ig[i]
            grid_layer[yi, xi] = layers[i]

    # 2D/G ratio map
    X, Y = np.meshgrid(x_unique, y_unique)
    cmap_2dg = plt.cm.YlGnBu
    im1 = ax2.pcolormesh(X, Y, grid_2dg, cmap=cmap_2dg, shading='auto',
                         vmin=0.5, vmax=1.5)
    cb1 = plt.colorbar(im1, ax=ax2, pad=0.02)
    cb1.set_label('I(2D)/I(G)', fontsize=11)

    # Draw boundary lines between regions
    ax2.axvline(x=9.5, color='white', linewidth=1.5, linestyle='--')
    ax2.axvline(x=12.5, color='white', linewidth=1.5, linestyle='--')

    # Add region labels
    ax2.text(4.5, -1.2, '1L', fontsize=11, fontweight='bold', ha='center',
             color='#2196F3')
    ax2.text(10.5, -1.2, '2L', fontsize=11, fontweight='bold', ha='center',
             color='#FF9800')
    ax2.text(13.5, -1.2, '3L', fontsize=11, fontweight='bold', ha='center',
             color='#4CAF50')

    ax2.set_xlabel('x (\u03bcm)', fontsize=12)
    ax2.set_ylabel('y (\u03bcm)', fontsize=12)
    ax2.set_title('(b) 2D/G Ratio Map', fontsize=13, fontweight='bold', pad=10)
    ax2.set_aspect('equal')

    # Panel (c): D/G intensity ratio mapping
    ax3 = plt.subplot(2, 2, 3)
    cmap_dg = plt.cm.YlOrRd
    im2 = ax3.pcolormesh(X, Y, grid_dg, cmap=cmap_dg, shading='auto',
                         vmin=0.05, vmax=0.35)
    cb2 = plt.colorbar(im2, ax=ax3, pad=0.02)
    cb2.set_label('I(D)/I(G)', fontsize=11)

    ax3.axvline(x=9.5, color='white', linewidth=1.5, linestyle='--')
    ax3.axvline(x=12.5, color='white', linewidth=1.5, linestyle='--')

    ax3.text(4.5, -1.2, '1L', fontsize=11, fontweight='bold', ha='center',
             color='#2196F3')
    ax3.text(10.5, -1.2, '2L', fontsize=11, fontweight='bold', ha='center',
             color='#FF9800')
    ax3.text(13.5, -1.2, '3L', fontsize=11, fontweight='bold', ha='center',
             color='#4CAF50')

    ax3.set_xlabel('x (\u03bcm)', fontsize=12)
    ax3.set_ylabel('y (\u03bcm)', fontsize=12)
    ax3.set_title('(c) D/G Ratio Map', fontsize=13, fontweight='bold', pad=10)
    ax3.set_aspect('equal')

    # Panel (d): Layer count map
    ax4 = plt.subplot(2, 2, 4)
    cmap_layer = plt.cm.Set2
    im3 = ax4.pcolormesh(X, Y, grid_layer, cmap=cmap_layer, shading='auto',
                         vmin=0.5, vmax=3.5)
    cb3 = plt.colorbar(im3, ax=ax4, pad=0.02, ticks=[1, 2, 3])
    cb3.set_label('Layer Count', fontsize=11)
    cb3.ax.set_yticklabels(['1L', '2L', '3L'])

    ax4.axvline(x=9.5, color='white', linewidth=1.5, linestyle='--')
    ax4.axvline(x=12.5, color='white', linewidth=1.5, linestyle='--')

    ax4.set_xlabel('x (\u03bcm)', fontsize=12)
    ax4.set_ylabel('y (\u03bcm)', fontsize=12)
    ax4.set_title('(d) Layer Identification', fontsize=13, fontweight='bold', pad=10)
    ax4.set_aspect('equal')

    plt.tight_layout()
    os.makedirs(os.path.dirname(fig_name), exist_ok=True)
    fig.savefig(fig_name, dpi=300, bbox_inches="tight")
    plt.close(fig)


if __name__ == "__main__":
    # Set Advanced Materials style rcParams
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

    plot_raman_mapping("./figures/raman_mapping.png")
    print("Figure saved: figures/raman_mapping.png")
