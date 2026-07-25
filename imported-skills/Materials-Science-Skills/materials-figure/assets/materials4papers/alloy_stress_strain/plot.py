"""
Tensile stress-strain curves for Ti-6Al-4V alloy under different heat treatment conditions.
MSE A (Materials Science and Engineering A) style — multi-panel figure with
stress-strain curves, work hardening rate, and mechanical property annotations.

Synthetic data: As-received, annealed, and solution-treated + aged conditions.
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
# Constitutive model for Ti-6Al-4V
# ============================================================

def generate_stress_strain(E, sigma_y, sigma_uts, eps_f, n, seed=None):
    """Generate engineering stress-strain curve with elastic-plastic transition.
    
    E: Young's modulus [GPa]
    sigma_y: yield strength [MPa]
    sigma_uts: ultimate tensile strength [MPa]
    eps_f: fracture strain
    n: strain hardening exponent
    """
    rng = np.random.RandomState(seed)
    
    # Elastic region
    eps_y = sigma_y / (E * 1000)  # convert E to MPa
    eps_elastic = np.linspace(0, eps_y, 50)
    sigma_elastic = E * 1000 * eps_elastic
    
    # Plastic region (Ludwik hardening)
    eps_plastic = np.linspace(eps_y, eps_f, 200)
    sigma_plastic = sigma_y + (sigma_uts - sigma_y) * \
                    ((eps_plastic - eps_y) / (eps_f - eps_y)) ** n
    
    # Add noise
    noise_elastic = rng.normal(0, 2, len(eps_elastic))
    noise_plastic = rng.normal(0, 3, len(eps_plastic))
    
    sigma_elastic += noise_elastic
    sigma_plastic += noise_plastic
    
    eps = np.concatenate([eps_elastic, eps_plastic])
    sigma = np.concatenate([sigma_elastic, sigma_plastic])
    
    return eps, sigma


def compute_work_hardening(eps, sigma):
    """Compute work hardening rate theta = d(sigma)/d(eps)."""
    theta = np.gradient(sigma, eps)
    return theta


# ============================================================
# Main figure assembly
# ============================================================

def main():
    print("Generating synthetic Ti-6Al-4V tensile data ...")
    
    # Material conditions
    conditions = {
        "As-received": {"E": 114, "sigma_y": 880, "sigma_uts": 950, "eps_f": 0.15, "n": 0.12, "seed": 101},
        "Annealed": {"E": 114, "sigma_y": 830, "sigma_uts": 900, "eps_f": 0.18, "n": 0.15, "seed": 202},
        "STA": {"E": 114, "sigma_y": 950, "sigma_uts": 1020, "eps_f": 0.12, "n": 0.10, "seed": 303},
    }
    
    colors = {"As-received": "#d62728", "Annealed": "#2ca02c", "STA": "#1f77b4"}
    data_all = {}
    
    for cond, params in conditions.items():
        eps, sigma = generate_stress_strain(**params)
        theta = compute_work_hardening(eps, sigma)
        data_all[cond] = {"eps": eps, "sigma": sigma, "theta": theta, "params": params}
    
    # --- figure ---
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.5, 3.2),
                                    gridspec_kw={"width_ratios": [1.2, 1]})
    
    # (a) Stress-strain curves
    for cond, data in data_all.items():
        eps = data["eps"]
        sigma = data["sigma"]
        params = data["params"]
        
        ax1.plot(eps * 100, sigma, "-", color=colors[cond], lw=1.5, label=cond)
        
        # Yield point annotation
        eps_y = params["sigma_y"] / (params["E"] * 1000)
        ax1.plot(eps_y * 100, params["sigma_y"], "o", color=colors[cond],
                 markersize=5, markerfacecolor="white", markeredgewidth=1.5,
                 markeredgecolor=colors[cond])
        ax1.annotate(f"\u03c3_y={params['sigma_y']}",
                     xy=(eps_y * 100, params["sigma_y"]),
                     xytext=(eps_y * 100 + 1.5, params["sigma_y"] - 30),
                     fontsize=7, color=colors[cond],
                     arrowprops=dict(arrowstyle="->", color=colors[cond], lw=0.8))
        
        # UTS annotation
        idx_uts = np.argmax(sigma)
        ax1.plot(eps[idx_uts] * 100, sigma[idx_uts], "s", color=colors[cond],
                 markersize=5, markerfacecolor="white", markeredgewidth=1.5,
                 markeredgecolor=colors[cond])
        ax1.annotate(f"UTS={sigma[idx_uts]:.0f}",
                     xy=(eps[idx_uts] * 100, sigma[idx_uts]),
                     xytext=(eps[idx_uts] * 100 + 1, sigma[idx_uts] + 20),
                     fontsize=7, color=colors[cond],
                     arrowprops=dict(arrowstyle="->", color=colors[cond], lw=0.8))
    
    ax1.set_xlabel("Engineering strain  \u03b5  [%]")
    ax1.set_ylabel("Engineering stress  \u03c3  [MPa]")
    ax1.set_title("(a) Tensile curves", fontweight="bold")
    ax1.legend(loc="lower right", frameon=False)
    ax1.grid(True, linestyle="--", alpha=0.3, lw=0.5)
    ax1.set_xlim(0, 20)
    ax1.set_ylim(0, 1100)
    
    # (b) Work hardening rate
    for cond, data in data_all.items():
        eps = data["eps"]
        theta = data["theta"]
        ax2.plot(eps * 100, theta, "-", color=colors[cond], lw=1.5, label=cond)
    
    ax2.set_xlabel("Engineering strain  \u03b5  [%]")
    ax2.set_ylabel("Work hardening rate  \u03b8  [MPa]")
    ax2.set_title("(b) Work hardening rate", fontweight="bold")
    ax2.legend(loc="upper right", frameon=False)
    ax2.grid(True, linestyle="--", alpha=0.3, lw=0.5)
    ax2.set_xlim(0, 20)
    ax2.set_ylim(0, 15000)
    
    fig.tight_layout()
    
    out = FIG_DIR / "stress_strain_tensile.png"
    fig.savefig(out)
    plt.close(fig)
    print(f"Saved: {out}")
    
    # ---- save CSV data ----
    for cond, data in data_all.items():
        csv_path = DATA_DIR / f"tensile_{cond.lower().replace(' ', '_').replace('+', '')}.csv"
        with open(csv_path, "w", newline="") as f:
            w = csv.writer(f)
            w.writerow(["strain", "stress_MPa", "work_hardening_MPa"])
            for eps, sigma, theta in zip(data["eps"], data["sigma"], data["theta"]):
                w.writerow([f"{eps:.5f}", f"{sigma:.2f}", f"{theta:.2f}"])
        print(f"Saved: {csv_path}")
    
    # Save summary
    summary_path = DATA_DIR / "mechanical_properties.csv"
    with open(summary_path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["condition", "E_GPa", "sigma_y_MPa", "UTS_MPa", "fracture_strain"])
        for cond, data in data_all.items():
            params = data["params"]
            eps = data["eps"]
            sigma = data["sigma"]
            w.writerow([cond, params["E"], params["sigma_y"],
                        f"{np.max(sigma):.1f}", f"{eps[-1]:.3f}"])
    print(f"Saved: {summary_path}")


if __name__ == "__main__":
    main()
