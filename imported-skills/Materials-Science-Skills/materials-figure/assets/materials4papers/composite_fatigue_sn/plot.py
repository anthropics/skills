"""
Fatigue S-N curves for fiber-reinforced composites.
Composites Science and Technology style — log-log S-N plot with fatigue limit annotations.

Synthetic data: CFRP and GFRP fatigue life at different stress levels.
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
# Basquin equation for fatigue
# ============================================================

def basquin_curve(sigma_f_prime, b, Nf_range=(1e3, 1e7)):
    """Generate S-N curve from Basquin equation: sigma = sigma_f' * (2*Nf)^b.
    
    sigma_f_prime: fatigue strength coefficient [MPa]
    b: Basquin exponent (negative)
    Nf_range: cycle range
    """
    Nf = np.logspace(np.log10(Nf_range[0]), np.log10(Nf_range[1]), 100)
    sigma = sigma_f_prime * (2 * Nf) ** b
    return Nf, sigma


def generate_fatigue_data(sigma_f_prime, b, n_points=15, scatter=0.15, seed=None):
    """Generate synthetic fatigue data with scatter around Basquin curve."""
    rng = np.random.RandomState(seed)
    
    Nf = np.logspace(3, 7, n_points)
    sigma_nominal = sigma_f_prime * (2 * Nf) ** b
    
    # Add log-normal scatter
    sigma = sigma_nominal * np.exp(rng.normal(0, scatter, n_points))
    
    return Nf, sigma


def fit_basquin(Nf, sigma):
    """Fit Basquin parameters from fatigue data."""
    log_Nf = np.log10(Nf)
    log_sigma = np.log10(sigma)
    
    # Linear fit: log(sigma) = log(sigma_f') + b*log(2*Nf)
    log_2Nf = np.log10(2 * Nf)
    coeffs = np.polyfit(log_2Nf, log_sigma, 1)
    b = coeffs[0]
    sigma_f_prime = 10 ** coeffs[1]
    
    return sigma_f_prime, b


def estimate_fatigue_limit(sigma_f_prime, b, Nf_limit=1e7):
    """Estimate fatigue limit at Nf_limit cycles."""
    sigma_limit = sigma_f_prime * (2 * Nf_limit) ** b
    return sigma_limit


# ============================================================
# Main figure assembly
# ============================================================

def main():
    print("Generating synthetic fatigue S-N data ...")
    
    # CFRP: higher strength, steeper slope
    Nf_cfrp, sigma_cfrp = generate_fatigue_data(
        sigma_f_prime=1200, b=-0.08, n_points=20, scatter=0.12, seed=101
    )
    sigma_f_prime_cfrp, b_cfrp = fit_basquin(Nf_cfrp, sigma_cfrp)
    sigma_limit_cfrp = estimate_fatigue_limit(sigma_f_prime_cfrp, b_cfrp)
    
    # GFRP: lower strength, shallower slope
    Nf_gfrp, sigma_gfrp = generate_fatigue_data(
        sigma_f_prime=800, b=-0.10, n_points=20, scatter=0.18, seed=202
    )
    sigma_f_prime_gfrp, b_gfrp = fit_basquin(Nf_gfrp, sigma_gfrp)
    sigma_limit_gfrp = estimate_fatigue_limit(sigma_f_prime_gfrp, b_gfrp)
    
    print(f"CFRP:  sigma_f' = {sigma_f_prime_cfrp:.1f} MPa, b = {b_cfrp:.4f}")
    print(f"       Fatigue limit (10^7 cycles) = {sigma_limit_cfrp:.1f} MPa")
    print(f"GFRP:  sigma_f' = {sigma_f_prime_gfrp:.1f} MPa, b = {b_gfrp:.4f}")
    print(f"       Fatigue limit (10^7 cycles) = {sigma_limit_gfrp:.1f} MPa")
    
    # --- figure ---
    fig, ax = plt.subplots(figsize=(4.5, 3.5))
    
    # Data points
    ax.loglog(Nf_cfrp, sigma_cfrp, "o", color="#1f77b4", markersize=6,
              markerfacecolor="white", markeredgewidth=1.5, markeredgecolor="#1f77b4",
              label="CFRP data", zorder=3)
    ax.loglog(Nf_gfrp, sigma_gfrp, "s", color="#d62728", markersize=6,
              markerfacecolor="white", markeredgewidth=1.5, markeredgecolor="#d62728",
              label="GFRP data", zorder=3)
    
    # Fit curves
    Nf_fit = np.logspace(3, 7, 100)
    sigma_cfrp_fit = sigma_f_prime_cfrp * (2 * Nf_fit) ** b_cfrp
    sigma_gfrp_fit = sigma_f_prime_gfrp * (2 * Nf_fit) ** b_gfrp
    
    ax.loglog(Nf_fit, sigma_cfrp_fit, "-", color="#1f77b4", lw=1.5,
              label=f"CFRP fit (b={b_cfrp:.3f})")
    ax.loglog(Nf_fit, sigma_gfrp_fit, "-", color="#d62728", lw=1.5,
              label=f"GFRP fit (b={b_gfrp:.3f})")
    
    # Fatigue limit annotations
    ax.axvline(1e7, color="gray", linestyle="--", lw=0.8, alpha=0.5)
    ax.text(1.1e7, sigma_limit_cfrp, f"CFRP: {sigma_limit_cfrp:.0f} MPa",
            color="#1f77b4", fontsize=7, va="center")
    ax.text(1.1e7, sigma_limit_gfrp, f"GFRP: {sigma_limit_gfrp:.0f} MPa",
            color="#d62728", fontsize=7, va="center")
    
    # Horizontal lines at fatigue limit
    ax.plot([1e7, 2e7], [sigma_limit_cfrp, sigma_limit_cfrp], "--",
            color="#1f77b4", lw=0.8, alpha=0.6)
    ax.plot([1e7, 2e7], [sigma_limit_gfrp, sigma_limit_gfrp], "--",
            color="#d62728", lw=0.8, alpha=0.6)
    
    ax.set_xlabel("Cycles to failure  N_f")
    ax.set_ylabel("Stress amplitude  \u03c3_a  [MPa]")
    ax.set_title("Fatigue S-N curves", fontweight="bold")
    ax.legend(loc="upper right", frameon=False)
    ax.grid(True, which="both", linestyle="--", alpha=0.3, lw=0.5)
    ax.set_xlim(1e3, 2e7)
    ax.set_ylim(100, 1500)
    
    fig.tight_layout()
    
    out = FIG_DIR / "fatigue_sn_curves.png"
    fig.savefig(out)
    plt.close(fig)
    print(f"Saved: {out}")
    
    # ---- save CSV data ----
    csv_path = DATA_DIR / "fatigue_cfrp.csv"
    with open(csv_path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["cycles_Nf", "stress_amplitude_MPa"])
        for Nf, sigma in zip(Nf_cfrp, sigma_cfrp):
            w.writerow([f"{Nf:.2e}", f"{sigma:.1f}"])
    print(f"Saved: {csv_path}")
    
    csv_path = DATA_DIR / "fatigue_gfrp.csv"
    with open(csv_path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["cycles_Nf", "stress_amplitude_MPa"])
        for Nf, sigma in zip(Nf_gfrp, sigma_gfrp):
            w.writerow([f"{Nf:.2e}", f"{sigma:.1f}"])
    print(f"Saved: {csv_path}")
    
    # Save fit parameters
    param_path = DATA_DIR / "fatigue_parameters.csv"
    with open(param_path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["material", "sigma_f_prime_MPa", "Basquin_exponent_b",
                    "fatigue_limit_10e7_MPa"])
        w.writerow(["CFRP", f"{sigma_f_prime_cfrp:.2f}", f"{b_cfrp:.4f}",
                    f"{sigma_limit_cfrp:.1f}"])
        w.writerow(["GFRP", f"{sigma_f_prime_gfrp:.2f}", f"{b_gfrp:.4f}",
                    f"{sigma_limit_gfrp:.1f}"])
    print(f"Saved: {param_path}")


if __name__ == "__main__":
    main()
