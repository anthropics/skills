"""
Weibull reliability analysis for structural ceramics.
JACS (Journal of the American Ceramic Society) style — dual-panel figure with
Weibull probability plot and strength distribution histograms.

Synthetic data: 3Y-TZP and Al2O3 fracture strength (n=30 each).
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
# Weibull statistics helpers
# ============================================================

def weibull_cdf(strength, sigma0, m):
    """Weibull cumulative distribution function P(sigma)."""
    return 1 - np.exp(-((strength / sigma0) ** m))


def weibull_pdf(strength, sigma0, m):
    """Weibull probability density function."""
    return (m / sigma0) * ((strength / sigma0) ** (m - 1)) * \
           np.exp(-((strength / sigma0) ** m))


def fit_weibull(strength_data):
    """Fit Weibull parameters (sigma0, m) using linear regression on
    ln(ln(1/(1-P))) vs ln(sigma)."""
    n = len(strength_data)
    sorted_s = np.sort(strength_data)
    # Median rank approximation
    P = (np.arange(1, n + 1) - 0.5) / n
    # Linearize: ln(ln(1/(1-P))) = m*ln(sigma) - m*ln(sigma0)
    Y = np.log(np.log(1 / (1 - P)))
    X = np.log(sorted_s)
    # Linear fit
    coeffs = np.polyfit(X, Y, 1)
    m = coeffs[0]
    sigma0 = np.exp(-coeffs[1] / m)
    return sigma0, m


def generate_weibull_data(sigma0, m, n=30, seed=None):
    """Generate synthetic Weibull-distributed strength data."""
    rng = np.random.RandomState(seed)
    u = rng.rand(n)
    strength = sigma0 * (-np.log(1 - u)) ** (1 / m)
    return strength


# ============================================================
# Main figure assembly
# ============================================================

def main():
    print("Generating synthetic Weibull strength data ...")
    # 3Y-TZP: high strength, moderate Weibull modulus
    s_tzp = generate_weibull_data(sigma0=950, m=12, n=30, seed=101)
    # Al2O3: lower strength, higher Weibull modulus (more reliable)
    s_al2o3 = generate_weibull_data(sigma0=420, m=18, n=30, seed=202)

    # Fit parameters
    sig0_tzp, m_tzp = fit_weibull(s_tzp)
    sig0_al2o3, m_al2o3 = fit_weibull(s_al2o3)

    print(f"3Y-TZP:  sigma0 = {sig0_tzp:.1f} MPa, m = {m_tzp:.2f}")
    print(f"Al2O3:   sigma0 = {sig0_al2o3:.1f} MPa, m = {m_al2o3:.2f}")

    # --- figure ---
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.5, 3.2),
                                    gridspec_kw={"width_ratios": [1.1, 1]})

    # (a) Weibull probability plot
    for s_data, sig0, m, label, color, marker in [
        (s_tzp, sig0_tzp, m_tzp, "3Y-TZP", "#d62728", "o"),
        (s_al2o3, sig0_al2o3, m_al2o3, "$\\mathrm{Al_2O_3}$", "#1f77b4", "s"),
    ]:
        n = len(s_data)
        sorted_s = np.sort(s_data)
        P = (np.arange(1, n + 1) - 0.5) / n
        Y = np.log(np.log(1 / (1 - P)))
        X = np.log(sorted_s)
        ax1.plot(X, Y, marker, color=color, label=f"{label} (m={m:.1f})",
                 markersize=5, markerfacecolor="white", markeredgewidth=1.2,
                 markeredgecolor=color)
        # Fit line
        s_fit = np.linspace(sorted_s.min() * 0.9, sorted_s.max() * 1.1, 100)
        P_fit = weibull_cdf(s_fit, sig0, m)
        Y_fit = np.log(np.log(1 / (1 - P_fit)))
        ax1.plot(np.log(s_fit), Y_fit, "-", color=color, lw=1.2, alpha=0.7)

    ax1.set_xlabel("ln(\u03c3)  [MPa]")
    ax1.set_ylabel("ln[ln(1/(1\u2212P))]")
    ax1.set_title("(a) Weibull probability plot", fontweight="bold")
    ax1.legend(loc="lower right", frameon=False)
    ax1.grid(True, linestyle="--", alpha=0.3, lw=0.5)

    # (b) Strength distribution histogram + PDF
    bins = np.linspace(300, 1100, 15)
    ax2.hist(s_tzp, bins=bins, density=True, alpha=0.35, color="#d62728",
             edgecolor="#d62728", label="3Y-TZP data")
    ax2.hist(s_al2o3, bins=bins, density=True, alpha=0.35, color="#1f77b4",
             edgecolor="#1f77b4", label="$\\mathrm{Al_2O_3}$ data")

    # PDF curves
    s_pdf = np.linspace(300, 1100, 200)
    pdf_tzp = weibull_pdf(s_pdf, sig0_tzp, m_tzp)
    pdf_al2o3 = weibull_pdf(s_pdf, sig0_al2o3, m_al2o3)
    ax2.plot(s_pdf, pdf_tzp, "-", color="#d62728", lw=1.5,
             label=f"3Y-TZP fit ($\\sigma_0$={sig0_tzp:.0f})")
    ax2.plot(s_pdf, pdf_al2o3, "-", color="#1f77b4", lw=1.5,
             label=f"$\\mathrm{{Al_2O_3}}$ fit ($\\sigma_0$={sig0_al2o3:.0f})")

    # Annotations for characteristic strength
    ax2.axvline(sig0_tzp, color="#d62728", linestyle="--", lw=0.8, alpha=0.6)
    ax2.text(sig0_tzp, ax2.get_ylim()[1] * 0.92, f"$\\sigma_0$={sig0_tzp:.0f}",
             color="#d62728", fontsize=7, ha="left", va="top")
    ax2.axvline(sig0_al2o3, color="#1f77b4", linestyle="--", lw=0.8, alpha=0.6)
    ax2.text(sig0_al2o3, ax2.get_ylim()[1] * 0.85, f"$\\sigma_0$={sig0_al2o3:.0f}",
             color="#1f77b4", fontsize=7, ha="left", va="top")

    ax2.set_xlabel("Fracture strength  \u03c3  [MPa]")
    ax2.set_ylabel("Probability density")
    ax2.set_title("(b) Strength distribution", fontweight="bold")
    ax2.legend(loc="upper right", frameon=False, fontsize=7)

    fig.tight_layout()

    out = FIG_DIR / "weibull_reliability.png"
    fig.savefig(out)
    plt.close(fig)
    print(f"Saved: {out}")

    # ---- save CSV data ----
    csv_path = DATA_DIR / "weibull_strength.csv"
    with open(csv_path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["material", "strength_MPa"])
        for s in s_tzp:
            w.writerow(["3Y-TZP", f"{s:.1f}"])
        for s in s_al2o3:
            w.writerow(["Al2O3", f"{s:.1f}"])
    print(f"Saved: {csv_path}")

    # Save fit parameters
    param_path = DATA_DIR / "weibull_parameters.csv"
    with open(param_path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["material", "sigma0_MPa", "Weibull_modulus_m"])
        w.writerow(["3Y-TZP", f"{sig0_tzp:.2f}", f"{m_tzp:.2f}"])
        w.writerow(["Al2O3", f"{sig0_al2o3:.2f}", f"{m_al2o3:.2f}"])
    print(f"Saved: {param_path}")


if __name__ == "__main__":
    main()
