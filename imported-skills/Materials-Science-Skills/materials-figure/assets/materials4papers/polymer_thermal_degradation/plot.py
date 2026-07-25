"""
Thermal degradation analysis of polymers using TGA/DTG.
Polymer journal style — dual-panel figure with TGA curves and DTG curves.

Synthetic data: PE, PP, PS, PMMA degradation at 10°C/min in N2.
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
FIG_DIR.mkdir(exist_ok=True)

# ============================================================
# TGA/DTG model
# ============================================================

def generate_tga_curve(T_onset, T_peak, T_end, residue_pct, heating_rate=10, seed=None):
    """Generate synthetic TGA/DTG data.
    
    T_onset: onset degradation temperature [deg C]
    T_peak: peak degradation temperature [deg C]
    T_end: end degradation temperature [deg C]
    residue_pct: final residue percentage [%]
    heating_rate: heating rate [deg C/min]
    """
    rng = np.random.RandomState(seed)
    
    # Temperature range
    T = np.linspace(50, 600, 500)
    
    # Sigmoidal degradation (Boltzmann function)
    mass_loss = 100 - residue_pct
    T_mid = (T_onset + T_end) / 2
    sigma = (T_end - T_onset) / 4
    
    mass_pct = 100 - mass_loss * (1 / (1 + np.exp(-(T - T_mid) / sigma)))
    
    # Add noise
    noise = rng.normal(0, 0.3, len(T))
    mass_pct += noise
    
    # DTG (derivative)
    DTG = -np.gradient(mass_pct, T) * heating_rate  # %/min
    
    return T, mass_pct, DTG


def find_degradation_temperatures(T, mass_pct):
    """Find T_onset (5% mass loss) and T_max (peak DTG)."""
    T_onset = np.interp(95, mass_pct[::-1], T[::-1])
    T_50 = np.interp(50, mass_pct[::-1], T[::-1])
    return T_onset, T_50


# ============================================================
# Main figure assembly
# ============================================================

def main():
    print("Generating synthetic TGA/DTG data ...")
    
    # Polymer degradation parameters
    polymers = {
        "PE": {"T_onset": 420, "T_peak": 460, "T_end": 500, "residue_pct": 1.5, "seed": 101},
        "PP": {"T_onset": 380, "T_peak": 420, "T_end": 470, "residue_pct": 2.0, "seed": 202},
        "PS": {"T_onset": 340, "T_peak": 380, "T_end": 430, "residue_pct": 5.0, "seed": 303},
        "PMMA": {"T_onset": 300, "T_peak": 350, "T_end": 400, "residue_pct": 3.0, "seed": 404},
    }
    
    colors = {"PE": "#d62728", "PP": "#ff7f0e", "PS": "#2ca02c", "PMMA": "#1f77b4"}
    data_all = {}
    
    for polymer, params in polymers.items():
        T, mass_pct, DTG = generate_tga_curve(**params)
        T_onset, T_50 = find_degradation_temperatures(T, mass_pct)
        data_all[polymer] = {
            "T": T, "mass_pct": mass_pct, "DTG": DTG,
            "T_onset": T_onset, "T_50": T_50,
            "residue": params["residue_pct"]
        }
    
    # --- figure ---
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.5, 3.2),
                                    gridspec_kw={"width_ratios": [1, 1]})
    
    # (a) TGA curves
    for polymer, data in data_all.items():
        T = data["T"]
        mass_pct = data["mass_pct"]
        T_onset = data["T_onset"]
        residue = data["residue"]
        
        ax1.plot(T, mass_pct, "-", color=colors[polymer], lw=1.5, label=polymer)
        
        # T_onset annotation
        ax1.axvline(T_onset, color=colors[polymer], linestyle="--", lw=0.6, alpha=0.5)
        ax1.text(T_onset, 97, f"{T_onset:.0f}", color=colors[polymer],
                 fontsize=6, ha="center", va="bottom", rotation=90)
        
        # Residue annotation
        ax1.text(580, residue + 2, f"{residue:.1f}%", color=colors[polymer],
                 fontsize=7, ha="right")
    
    ax1.set_xlabel("Temperature  T  [°C]")
    ax1.set_ylabel("Mass  [%]")
    ax1.set_title("(a) TGA curves", fontweight="bold")
    ax1.legend(loc="upper right", frameon=False)
    ax1.grid(True, linestyle="--", alpha=0.3, lw=0.5)
    ax1.set_xlim(50, 600)
    ax1.set_ylim(0, 105)
    
    # (b) DTG curves
    for polymer, data in data_all.items():
        T = data["T"]
        DTG = data["DTG"]
        T_50 = data["T_50"]
        
        ax2.plot(T, DTG, "-", color=colors[polymer], lw=1.5, label=polymer)
        
        # Peak annotation
        idx_peak = np.argmax(DTG)
        ax2.plot(T[idx_peak], DTG[idx_peak], "o", color=colors[polymer],
                 markersize=4, markerfacecolor="white", markeredgewidth=1.2,
                 markeredgecolor=colors[polymer])
        ax2.text(T[idx_peak] + 5, DTG[idx_peak], f"{T[idx_peak]:.0f}",
                 color=colors[polymer], fontsize=6, va="center")
    
    ax2.set_xlabel("Temperature  T  [°C]")
    ax2.set_ylabel("DTG  [%/min]")
    ax2.set_title("(b) DTG curves", fontweight="bold")
    ax2.legend(loc="upper right", frameon=False)
    ax2.grid(True, linestyle="--", alpha=0.3, lw=0.5)
    ax2.set_xlim(50, 600)
    ax2.set_ylim(0, max([np.max(data["DTG"]) for data in data_all.values()]) * 1.1)
    
    fig.tight_layout()
    
    out = FIG_DIR / "tga_dtg_thermal.png"
    fig.savefig(out)
    plt.close(fig)
    print(f"Saved: {out}")
    
    # ---- save CSV data ----
    for polymer, data in data_all.items():
        csv_path = DATA_DIR / f"tga_{polymer.lower()}.csv"
        with open(csv_path, "w", newline="") as f:
            w = csv.writer(f)
            w.writerow(["temperature_C", "mass_pct", "DTG_pct_per_min"])
            for T, mass, dtg in zip(data["T"], data["mass_pct"], data["DTG"]):
                w.writerow([f"{T:.1f}", f"{mass:.3f}", f"{dtg:.3f}"])
        print(f"Saved: {csv_path}")
    
    # Save summary
    summary_path = DATA_DIR / "thermal_properties.csv"
    with open(summary_path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["polymer", "T_onset_C", "T_50_C", "residue_pct"])
        for polymer, data in data_all.items():
            w.writerow([polymer, f"{data['T_onset']:.1f}", f"{data['T_50']:.1f}",
                        f"{data['residue']:.1f}"])
    print(f"Saved: {summary_path}")


if __name__ == "__main__":
    main()
