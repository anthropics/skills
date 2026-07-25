"""
EBSD Inverse Pole Figure mapping for polycrystalline steel.
Acta Materialia style — multi-panel figure with IPF-ND map, IPF-RD map,
grain boundary overlay, {100}/{110}/{111} pole figures, and inverse pole figure key.

Synthetic data: Voronoi tessellation with random Bunge Euler angles.
"""

import os
import csv
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon
from pathlib import Path

# ============================================================
# Publication rcParams
# ============================================================
matplotlib.rcParams.update({
    "font.family": "Arial",
    "font.size": 8,
    "axes.linewidth": 0.8,
    "xtick.major.width": 0.6,
    "ytick.major.width": 0.6,
    "xtick.minor.width": 0.4,
    "ytick.minor.width": 0.4,
    "xtick.major.size": 3,
    "ytick.major.size": 3,
    "xtick.direction": "in",
    "ytick.direction": "in",
    "axes.labelsize": 9,
    "axes.titlesize": 9,
    "legend.fontsize": 7,
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
# 24 cubic symmetry operators (rotation matrices)
# ============================================================
CU = []
for s1 in [1, -1]:
    for s2 in [1, -1]:
        for s3 in [1, -1]:
            CU.append(np.diag([s1, s2, s3]))
            CU.append(np.diag([s1, s2, s3]) @ np.array([[0,0,1],[1,0,0],[0,1,0]]))
            CU.append(np.diag([s1, s2, s3]) @ np.array([[0,1,0],[0,0,1],[1,0,0]]))
            CU.append(np.diag([s1, s2, s3]) @ np.array([[0,0,-1],[1,0,0],[0,-1,0]]))
CU = CU[:24]

# ============================================================
# IPF coloring helpers
# ============================================================

def to_std_triangle(d):
    """Map direction *d* into the cubic fundamental zone (x >= y >= z >= 0)."""
    best = None
    for R in CU:
        de = R @ d
        de = np.abs(de)
        a, b, c = sorted(de, reverse=True)
        if best is None or a > best[0] or (a == best[0] and b > best[1]):
            best = (a, b, c)
    n = np.sqrt(best[0]**2 + best[1]**2 + best[2]**2)
    return np.array([best[0], best[1], best[2]]) / n if n > 0 else np.zeros(3)


def ipf_rgb(d):
    """RGB colour for a crystal direction in the standard triangle."""
    t = to_std_triangle(d)
    n = np.linalg.norm(t)
    if n < 1e-12:
        return np.array([1., 1., 1.])
    x, y, z = t / n
    r = 1 - x
    g = 1 - y
    b = 1 - z
    c = np.sqrt(x*x + y*y + z*z)
    return np.clip([r/c, g/c, b/c], 0, 1)


def euler_to_R(phi1, Phi, phi2):
    """Bunge Euler angles (radians) -> rotation matrix."""
    c1, s1 = np.cos(phi1), np.sin(phi1)
    cn, sn = np.cos(Phi),  np.sin(Phi)
    c2, s2 = np.cos(phi2), np.sin(phi2)
    return np.array([
        [c1*c2 - s1*s2*cn,  -c1*s2 - s1*c2*cn,  s1*sn],
        [s1*c2 + c1*s2*cn,  -s1*s2 + c1*c2*cn, -c1*sn],
        [s2*sn,              s2*cn,               cn   ],
    ])


def ipf_color_euler(phi1, Phi, phi2, ref):
    """IPF colour for an orientation given a reference sample direction."""
    R = euler_to_R(phi1, Phi, phi2)
    d_crystal = R.T @ ref
    return ipf_rgb(d_crystal)


# ============================================================
# Synthetic EBSD data generation
# ============================================================

def generate_ebsd(nx=120, ny=120, n_grains=250, seed=42):
    """Return pixel arrays of IPF-ND colour, IPF-RD colour, grain_id,
    and a list of (phi1, Phi, phi2) per grain.
    Uses a simple nearest-centre Voronoi tessellation (no scipy)."""
    rng = np.random.RandomState(seed)

    # Voronoi tessellation via nearest-centre assignment
    pts = rng.rand(n_grains, 2) * [nx, ny]

    yy, xx = np.mgrid[0:ny, 0:nx]
    flat = np.column_stack([xx.ravel(), yy.ravel()])
    # Assign each pixel to nearest seed
    grain_id = np.zeros(ny * nx, dtype=int)
    chunk = 5000
    for start in range(0, len(flat), chunk):
        end = min(start + chunk, len(flat))
        dists = np.sum((flat[start:end, None, :] - pts[None, :, :]) ** 2, axis=2)
        grain_id[start:end] = np.argmin(dists, axis=1)
    grain_id = grain_id.reshape(ny, nx)

    # Random orientations per grain
    eulers = np.column_stack([
        rng.rand(n_grains) * 2 * np.pi,
        np.arccos(1 - 2 * rng.rand(n_grains)),
        rng.rand(n_grains) * 2 * np.pi,
    ])

    nd = np.array([0., 0., 1.])
    rd = np.array([1., 0., 0.])
    img_nd = np.zeros((ny, nx, 3))
    img_rd = np.zeros((ny, nx, 3))
    for gid in range(n_grains):
        mask = grain_id == gid
        img_nd[mask] = ipf_color_euler(*eulers[gid], nd)
        img_rd[mask] = ipf_color_euler(*eulers[gid], rd)

    return img_nd, img_rd, grain_id, eulers


def grain_boundary_map(grain_id, lw=0.7):
    """Binary image of grain boundaries (True = boundary pixel)."""
    ny, nx = grain_id.shape
    bnd = np.zeros((ny, nx), dtype=bool)
    bnd[:, :-1] |= grain_id[:, :-1] != grain_id[:, 1:]
    bnd[:-1, :] |= grain_id[:-1, :] != grain_id[1:, :]
    # dilate
    dil = bnd.copy()
    for _ in range(int(lw)):
        tmp = dil.copy()
        dil[1:, :] |= tmp[:-1, :]
        dil[:-1, :] |= tmp[1:, :]
        dil[:, 1:] |= tmp[:, :-1]
        dil[:, :-1] |= tmp[:, 1:]
    return dil


# ============================================================
# Pole figure helpers
# ============================================================

def stereo(d):
    """Stereo projection of unit direction -> (X, Y), only upper hemisphere."""
    d = d / (np.linalg.norm(d) + 1e-30)
    if d[2] < 0:
        d = -d
    if d[2] >= 1.0:
        return 0.0, 0.0
    f = np.sqrt(2 / (1 + d[2]))
    return d[0] * f, d[1] * f


PF_FAMILIES = {
    "{100}": [[1,0,0], [0,1,0], [0,0,1]],
    "{110}": [[1,1,0], [1,0,1], [0,1,1], [1,-1,0], [1,0,-1], [0,1,-1]],
    "{111}": [[1,1,1], [1,1,-1], [1,-1,1], [-1,1,1]],
}


def plot_pole_figures(ax, eulers, family, symbol=".", color="k", ms=1.2, alpha=0.25):
    ax.set_aspect("equal")
    th = np.linspace(0, 2 * np.pi, 200)
    ax.plot(np.cos(th), np.sin(th), "k-", lw=0.6)
    # standard triangle outline (approximate)
    verts_st = [(0, 0)]
    for t in np.linspace(0, 1, 40):
        d = np.array([1, t, 0], dtype=float)
        d /= np.linalg.norm(d)
        verts_st.append(stereo(d))
    for t in np.linspace(0, 1, 40):
        d = np.array([1, 1, t], dtype=float)
        d /= np.linalg.norm(d)
        verts_st.append(stereo(d))
    for t in np.linspace(1, 0, 40):
        d = np.array([t, t, t], dtype=float)
        d /= np.linalg.norm(d)
        verts_st.append(stereo(d))
    vs = np.array(verts_st)
    ax.plot(vs[:, 0], vs[:, 1], "k-", lw=0.4, alpha=0.4)

    dirs = PF_FAMILIES[family]
    for eu in eulers:
        R = euler_to_R(*eu)
        for h in dirs:
            h = np.array(h, dtype=float)
            h /= np.linalg.norm(h)
            for R_op in CU[:24]:
                d_c = R.T @ (R_op @ h)
                if d_c[2] < 0:
                    d_c = -d_c
                if d_c[2] > -0.01:
                    sx, sy = stereo(d_c)
                    if sx**2 + sy**2 <= 1.02:
                        ax.plot(sx, sy, symbol, color=color, ms=ms, alpha=alpha,
                                markeredgecolor="none")
    ax.set_xlim(-1.1, 1.1)
    ax.set_ylim(-1.1, 1.1)
    ax.axis("off")
    ax.set_title(family, fontsize=9, pad=2)


# ============================================================
# Main figure assembly
# ============================================================

def main():
    print("Generating synthetic EBSD data (250 grains, 120x120 px) ...")
    img_nd, img_rd, grain_id, eulers = generate_ebsd()

    # Grain boundary overlay
    bnd = grain_boundary_map(grain_id)
    img_nd_gb = img_nd.copy()
    img_nd_gb[bnd] = 0

    # --- figure ---
    fig = plt.figure(figsize=(7.4, 5.0))
    gs = fig.add_gridspec(3, 4, width_ratios=[1, 1, 0.85, 0.85],
                          height_ratios=[1, 1, 0.12], hspace=0.22, wspace=0.25)

    # (a) IPF-ND
    ax1 = fig.add_subplot(gs[0, 0])
    ax1.imshow(img_nd, origin="upper")
    ax1.set_title("(a) IPF // ND", fontweight="bold")
    ax1.set_xticks([]); ax1.set_yticks([])
    for sp in ax1.spines.values():
        sp.set_visible(True); sp.set_linewidth(0.8)

    # (b) IPF-RD
    ax2 = fig.add_subplot(gs[0, 1])
    ax2.imshow(img_rd, origin="upper")
    ax2.set_title("(b) IPF // RD", fontweight="bold")
    ax2.set_xticks([]); ax2.set_yticks([])
    for sp in ax2.spines.values():
        sp.set_visible(True); sp.set_linewidth(0.8)

    # (c) IPF-ND + grain boundaries
    ax3 = fig.add_subplot(gs[1, 0])
    ax3.imshow(img_nd_gb, origin="upper")
    ax3.set_title("(c) IPF-ND + GBs", fontweight="bold")
    ax3.set_xticks([]); ax3.set_yticks([])
    for sp in ax3.spines.values():
        sp.set_visible(True); sp.set_linewidth(0.8)

    # (d) Grain boundary network
    ax4 = fig.add_subplot(gs[1, 1])
    ax4.imshow(~bnd, cmap="gray", origin="upper", vmin=0, vmax=1)
    ax4.set_title("(d) Grain boundaries", fontweight="bold")
    ax4.set_xticks([]); ax4.set_yticks([])
    for sp in ax4.spines.values():
        sp.set_visible(True); sp.set_linewidth(0.8)

    # (e-g) Pole figures
    ax_pf1 = fig.add_subplot(gs[0, 2])
    plot_pole_figures(ax_pf1, eulers, "{100}", color="#d62728", ms=0.9)
    ax_pf2 = fig.add_subplot(gs[0, 3])
    plot_pole_figures(ax_pf2, eulers, "{110}", color="#2ca02c", ms=0.9)
    ax_pf3 = fig.add_subplot(gs[1, 2])
    plot_pole_figures(ax_pf3, eulers, "{111}", color="#1f77b4", ms=0.9)

    # (h) IPF colour key (standard triangle)
    ax_ipf = fig.add_subplot(gs[1, 3])
    N = 200
    xg = np.linspace(0, 1, N)
    yg = np.linspace(0, 1, N)
    X, Y = np.meshgrid(xg, yg)
    Z = 1 - X - Y
    valid = Z >= 0
    img_tri = np.ones((N, N, 3))
    for i in range(N):
        for j in range(N):
            if Z[i, j] >= 0:
                d = np.array([X[i, j], Y[i, j], Z[i, j]])
                n = np.linalg.norm(d)
                if n > 0:
                    d /= n
                img_tri[i, j] = ipf_rgb(d)
            else:
                img_tri[i, j] = [1, 1, 1]
    ax_ipf.imshow(img_tri, origin="lower", extent=[0, 1, 0, 1], aspect="equal")
    tri = Polygon([[0, 0], [1, 0], [0, 1]], closed=True,
                  fill=False, edgecolor="k", lw=0.8)
    ax_ipf.add_patch(tri)
    ax_ipf.plot([0, 1], [0, 0], "k-", lw=0.8)
    ax_ipf.plot([0, 0], [0, 1], "k-", lw=0.8)
    ax_ipf.plot([1, 0], [0, 1], "k-", lw=0.8)
    ax_ipf.text(0.02, -0.07, "<100>", fontsize=7, ha="center", va="top")
    ax_ipf.text(1.02, -0.07, "<110>", fontsize=7, ha="center", va="top")
    ax_ipf.text(-0.05, 1.02, "<111>", fontsize=7, ha="center", va="bottom")
    ax_ipf.set_xlim(-0.15, 1.15)
    ax_ipf.set_ylim(-0.15, 1.15)
    ax_ipf.set_aspect("equal")
    ax_ipf.axis("off")
    ax_ipf.set_title("(h) IPF key", fontsize=9, fontweight="bold", pad=2)

    # Scale bars
    px_per_um = 120 / 60  # 120 px = 60 um
    bar_px = int(10 * px_per_um)
    for ax in [ax1, ax2, ax3, ax4]:
        ax.plot([8, 8 + bar_px], [114, 114], "w-", lw=2)
        ax.plot([8, 8 + bar_px], [114, 114], "k-", lw=1)
        ax.text(8 + bar_px / 2, 110, "10 \u03bcm", ha="center", va="top",
                fontsize=6, color="white",
                bbox=dict(boxstyle="round,pad=0.15", fc="black", alpha=0.55, ec="none"))

    fig.text(0.5, 0.01,
             "EBSD characterization of polycrystalline steel  "
             "(synthetic data, 250 grains)",
             ha="center", fontsize=7, style="italic", color="#555")

    out = FIG_DIR / "ebsd_ipf_maps.png"
    fig.savefig(out)
    plt.close(fig)
    print(f"Saved: {out}")

    # ---- save CSV data ----
    csv_path = DATA_DIR / "ebsd_orientations.csv"
    with open(csv_path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["grain_id", "phi1_deg", "Phi_deg", "phi2_deg"])
        for gid, eu in enumerate(eulers):
            w.writerow([gid,
                        f"{np.degrees(eu[0]):.2f}",
                        f"{np.degrees(eu[1]):.2f}",
                        f"{np.degrees(eu[2]):.2f}"])
    print(f"Saved: {csv_path}")


if __name__ == "__main__":
    main()
