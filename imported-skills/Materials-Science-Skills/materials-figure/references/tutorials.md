# Materials Figure Tutorials

End-to-end walkthroughs for the most common materials-science figure types.
Each tutorial starts from raw data and produce a publication-ready SVG + PNG.

**Note**: In LLM-as-artist mode, the LLM writes plotting code directly using matplotlib.
The tutorials below are kept as reference examples. The `materials_plot_lib` helper library
was removed; the LLM implements equivalent functionality directly in `plot.py`.

---

## Prerequisites

Every script in this file begins with the same mandatory setup:

```python
import matplotlib
matplotlib.use('Agg')                    # headless / server rendering
import matplotlib.pyplot as plt
import matplotlib.gridspec as gridspec
import numpy as np
from pathlib import Path

# ── MANDATORY rcParams ────────────────────────────────────────────────────────
plt.rcParams['font.family'] = 'sans-serif'
plt.rcParams['font.sans-serif'] = ['Arial', 'DejaVu Sans', 'Liberation Sans']
plt.rcParams['svg.fonttype'] = 'none'

# ── Style defaults ────────────────────────────────────────────────────────────
plt.rcParams.update({
    'font.size': 12,
    'axes.spines.right': False,
    'axes.spines.top': False,
    'axes.linewidth': 2.0,
    'legend.frameon': False,
    'xtick.major.width': 1.5,
    'ytick.major.width': 1.5,
    'savefig.dpi': 300,
    'savefig.bbox': 'tight',
})
```

Import helpers from `materials_plot_lib`:

```python
from materials_plot_lib import (
    apply_pub_style, make_grouped_bar, make_line_trend, make_ftir_overlay,
    make_xrd_pattern, make_radar, make_heatmap, make_stacked_bar,
    make_boxplot, make_tga_dtg_overlay, add_panel_label, annotate_bars,
    tighten_ylimits, finalize_figure, PALETTE_CBM, PALETTE_CCC,
    PALETTE_SEMANTIC, PALETTE_SINGLE_HUE, PALETTE_NMI_PASTEL,
)
```

---

## Tutorial 1: Bonding Strength Grouped Bar

**Scenario**: Pull-off bond strength of waterborne epoxy modified emulsified
asphalt at 4 dosage levels, tested under dry and moisture-conditioned states.

### Step 1: Prepare data

```python
labels = ["Dry", "Moisture-conditioned"]
groups = ["Control", "10% WER", "15% WER", "20% WER"]

# Mean bond strength (MPa)
values = [
    [0.45, 0.32],   # Control
    [0.62, 0.51],   # 10% WER
    [0.78, 0.68],   # 15% WER
    [0.71, 0.55],   # 20% WER
]

# Standard deviation (n = 3)
errors = [
    [0.04, 0.03],
    [0.05, 0.04],
    [0.06, 0.05],
    [0.05, 0.04],
]
```

### Step 2: Create figure

```python
apply_pub_style()
fig, ax = plt.subplots(figsize=(6, 4))
bars = make_grouped_bar(ax, labels, groups, values, PALETTE_CBM,
                        error_bars=errors, ylabel="Bond strength (MPa)")

# Tighten y-limits
all_vals = [v for row in values for v in row]
all_errs = [e for row in errors for e in row]
tighten_ylimits(ax, [v + e for v, e in zip(all_vals, all_errs)], ymin=0)

# Add panel label
add_panel_label(ax, "(a)", loc="top-left")

# Tight layout and export
fig.tight_layout(pad=2)
finalize_figure(fig, "bonding_strength_grouped_bar", output_dir="./figures/")
```

### Step 3: Caption

```
Figure X. Pull-off bond strength of waterborne epoxy modified emulsified
asphalt at different WER contents under dry and moisture-conditioned states.
Error bars represent SD (n = 3). The 15% WER group showed the highest mean
strength under both conditions; field performance requires additional moisture
and traffic exposure validation.
```

---

## Tutorial 2: Dosage-Performance Curve with Optimum Region

**Scenario**: Bond strength measured at 6 epoxy dosages; need to mark the
optimum range.

### Step 1: Prepare data

```python
dosage = [0, 5, 10, 15, 20, 25]
strength_mean = [0.45, 0.58, 0.72, 0.78, 0.71, 0.63]
strength_sd = [0.04, 0.05, 0.05, 0.06, 0.05, 0.04]
```

### Step 2: Create figure

```python
apply_pub_style()
fig, ax = plt.subplots(figsize=(6, 4))

# Trend line with uncertainty band
make_line_trend(ax, dosage, [strength_mean], ["Bond strength"],
                PALETTE_CBM, xlabel="WER content (%)",
                ylabel="Bond strength (MPa)", fill_between=[strength_sd])

# Mark optimum region
ax.axvspan(12, 18, alpha=0.12, color=PALETTE_CBM["optimal"])
ax.annotate("Optimum range", xy=(15, 0.78), xytext=(18, 0.82),
            arrowprops=dict(arrowstyle="->", color="#4F7C6A", lw=1.5),
            fontsize=9, color="#4F7C6A", fontweight="bold")

# Mark peak
ax.plot(15, 0.78, marker='*', markersize=15, color=PALETTE_CBM["optimal"],
        zorder=5)

tighten_ylimits(ax, [s + e for s, e in zip(strength_mean, strength_sd)],
                ymin=0)
add_panel_label(ax, "(a)")
fig.tight_layout(pad=2)
finalize_figure(fig, "dosage_performance_curve")
```

### Step 3: Caption

```
Figure X. Bond strength of waterborne epoxy modified emulsified asphalt as a
function of WER content. Error bands represent SD (n = 3). The shaded region
(12–18%) indicates the optimum dosage range based on mechanical performance;
durability validation at the optimum dosage is reported in Figure Y.
```

---

## Tutorial 3: FTIR Curing Evidence

**Scenario**: FTIR spectra of neat epoxy resin and cured WER-asphalt, showing
epoxide peak disappearance.

### Step 1: Prepare data

```python
# Simulated FTIR data (replace with real spectra)
wavenumber = np.linspace(4000, 400, 1000)

def gaussian_peak(x, center, width, height=1.0):
    return height * np.exp(-0.5 * ((x - center) / width) ** 2)

neat = (gaussian_peak(wavenumber, 3400, 80, 0.6) +
        gaussian_peak(wavenumber, 1730, 25, 0.4) +
        gaussian_peak(wavenumber, 1510, 20, 0.3) +
        gaussian_peak(wavenumber, 1240, 20, 0.25) +
        gaussian_peak(wavenumber, 915, 15, 0.35) +
        gaussian_peak(wavenumber, 830, 15, 0.2))

cured = (gaussian_peak(wavenumber, 3400, 70, 0.55) +
         gaussian_peak(wavenumber, 1730, 25, 0.5) +
         gaussian_peak(wavenumber, 1510, 20, 0.3) +
         gaussian_peak(wavenumber, 1240, 20, 0.3) +
         gaussian_peak(wavenumber, 1080, 30, 0.3) +
         gaussian_peak(wavenumber, 830, 15, 0.2))
# Note: 915 cm⁻¹ peak gone in cured sample
```

### Step 2: Create figure

```python
apply_pub_style()
fig, ax = plt.subplots(figsize=(7, 4))

make_ftir_overlay(ax, wavenumber, [neat, cured],
                  ["Neat WER resin", "Cured WER-asphalt (7 d)"],
                  PALETTE_CBM,
                  peak_annotations={
                      915: "Epoxide\n(disappeared)",
                      1240: "C–O–C",
                      1730: "C=O",
                      3400: "O–H"
                  })

# Mark the disappeared peak
ax.axvspan(900, 930, alpha=0.08, color=PALETTE_CBM["danger"])
ax.text(915, ax.get_ylim()[1] * 0.95, "Cured", fontsize=7,
        color=PALETTE_CBM["danger"], ha="center", va="top")

add_panel_label(ax, "(a)")
fig.tight_layout(pad=2)
finalize_figure(fig, "ftir_curing_evidence")
```

### Step 3: Caption

```
Figure X. FTIR spectra of neat WER resin and WER-asphalt after 7 d curing.
The disappearance of the 915 cm⁻¹ epoxide peak is consistent with ring-opening
crosslinking during curing. The increased C=O absorption at 1730 cm⁻¹ suggests
ester formation. FTIR alone cannot confirm the full curing mechanism; further
evidence from DSC (Figure Y) and XPS (Figure Z) is recommended.
```

---

## Tutorial 4: XRD Hydration Evidence

**Scenario**: XRD patterns of cement paste with and without fly ash replacement
at 28 d.

### Step 1: Prepare data

```python
two_theta = np.linspace(5, 70, 2000)

def xrd_pattern(two_theta, peaks):
    """Generate a simulated XRD pattern from peak positions and intensities."""
    pattern = np.zeros_like(two_theta)
    for pos, intensity, width in peaks:
        pattern += gaussian_peak(two_theta, pos, width, intensity)
    # Add amorphous hump
    pattern += 0.3 * gaussian_peak(two_theta, 30, 10, 0.5)
    return pattern / pattern.max()

opc_peaks = [
    (18.0, 0.4, 0.3),   # CH (portlandite)
    (29.4, 1.0, 0.4),   # C₃S
    (32.2, 0.7, 0.3),   # C₂S
    (34.1, 0.5, 0.3),   # C–S–H
    (41.2, 0.3, 0.3),   # C₃A
    (50.8, 0.4, 0.3),   # C₄AF
]
fa_peaks = [
    (18.0, 0.15, 0.3),  # CH reduced
    (29.4, 0.6, 0.4),   # C₃S reduced
    (32.2, 0.5, 0.3),   # C₂S
    (34.1, 0.7, 0.3),   # C–S–H enhanced
    (26.6, 0.4, 0.3),   # Quartz (from fly ash)
    (50.8, 0.25, 0.3),  # C₄AF
]

opc_pattern = xrd_pattern(two_theta, opc_peaks)
fa_pattern = xrd_pattern(two_theta, fa_peaks)
```

### Step 2: Create figure

```python
apply_pub_style()
fig, ax = plt.subplots(figsize=(7, 5))

make_xrd_pattern(ax, two_theta, [opc_pattern, fa_pattern],
                 ["OPC 28 d", "FA30 28 d"], PALETTE_CBM, offset=1.2,
                 peak_annotations={
                     18.0: "CH",
                     26.6: "Quartz",
                     29.4: "C₃S",
                     34.1: "C–S–H"
                 })

# Add annotation for CH reduction
ax.annotate("CH reduced\nwith FA replacement",
            xy=(18, opc_pattern[np.argmin(np.abs(two_theta - 18))] + 1.2),
            xytext=(22, 2.8),
            arrowprops=dict(arrowstyle="->", color="#4F7C6A"),
            fontsize=8, color="#4F7C6A")

add_panel_label(ax, "(a)")
fig.tight_layout(pad=2)
finalize_figure(fig, "xrd_hydration_evidence")
```

### Step 3: Caption

```
Figure X. XRD patterns of OPC paste and FA30 paste at 28 d curing. Portlandite
(CH) peak at 2θ = 18.0° is reduced in the FA30 sample, consistent with
pozzolanic reaction. Enhanced C–S–H peak at 34.1° suggests additional
C–S–H formation from the pozzolanic reaction. Quartz peak at 26.6° originates
from the fly ash mineralogy.
```

---

## Tutorial 5: Multi-Panel Evidence Board (2×2)

**Scenario**: A complete evidence board for a WER-asphalt manuscript —
bonding strength, FTIR, dosage curve, and durability retention.

### Step 1: Prepare all data

```python
# Panel a: Bonding strength
labels_a = ["Dry", "Moisture"]
groups_a = ["Control", "15% WER"]
values_a = [[0.45, 0.32], [0.78, 0.68]]
errors_a = [[0.04, 0.03], [0.06, 0.05]]

# Panel b: FTIR (reuse Tutorial 3 data)
# Panel c: Dosage curve (reuse Tutorial 2 data)
# Panel d: Durability retention
labels_d = ["Control", "10% WER", "15% WER", "20% WER"]
retention = [62, 84, 85, 78]
```

### Step 2: Create figure

```python
apply_pub_style()
fig = plt.figure(figsize=(12, 10))
gs = gridspec.GridSpec(2, 2, hspace=0.35, wspace=0.3)

# Panel a: Bonding strength
ax_a = fig.add_subplot(gs[0, 0])
make_grouped_bar(ax_a, labels_a, groups_a, values_a, PALETTE_CBM,
                 error_bars=errors_a, ylabel="Bond strength (MPa)")
add_panel_label(ax_a, "(a)")

# Panel b: FTIR
ax_b = fig.add_subplot(gs[0, 1])
make_ftir_overlay(ax_b, wavenumber, [neat, cured],
                  ["Neat WER", "Cured 7 d"], PALETTE_CBM,
                  peak_annotations={915: "Epoxide", 1730: "C=O"})
add_panel_label(ax_b, "(b)")

# Panel c: Dosage curve
ax_c = fig.add_subplot(gs[1, 0])
make_line_trend(ax_c, dosage, [strength_mean], ["Bond strength"],
                PALETTE_CBM, xlabel="WER (%)", ylabel="Strength (MPa)",
                fill_between=[strength_sd])
ax_c.axvspan(12, 18, alpha=0.12, color=PALETTE_CBM["optimal"])
add_panel_label(ax_c, "(c)")

# Panel d: Durability retention
ax_d = fig.add_subplot(gs[1, 1])
make_grouped_bar(ax_d, labels_d, ["Retention"],
                 [retention], PALETTE_CBM, ylabel="Retention (%)")
tighten_ylimits(ax_d, retention, ymin=0)
add_panel_label(ax_d, "(d)")

# Shared title
fig.suptitle("WER-Asphalt Evidence Board", fontsize=14, fontweight="bold", y=0.98)

finalize_figure(fig, "evidence_board_2x2")
```

### Step 3: Caption

```
Figure X. Evidence board for waterborne epoxy modified emulsified asphalt:
(a) pull-off bond strength under dry and moisture-conditioned states (SD, n = 3);
(b) FTIR spectra showing epoxide peak disappearance after curing;
(c) bond strength as a function of WER content with optimum range shaded;
(d) moisture-conditioned retention ratio across WER dosages.
```

---

## Tutorial 6: Radar Chart for Multi-Property Screening

**Scenario**: Comparing 3 material formulations across 6 performance indices.

### Step 1: Prepare data

```python
categories = [
    "Bond strength", "Tensile strength", "Flexural modulus",
    "Impact resistance", "Thermal stability", "Workability"
]

series = {
    "Control":     [0.45, 0.60, 0.55, 0.30, 0.70, 0.85],
    "10% WER":     [0.62, 0.72, 0.68, 0.45, 0.75, 0.78],
    "15% WER":     [0.78, 0.82, 0.75, 0.55, 0.80, 0.70],
}
```

### Step 2: Create figure

```python
apply_pub_style()
fig, ax = plt.subplots(figsize=(7, 7), subplot_kw=dict(projection="polar"))

make_radar(ax, categories, series, PALETTE_CBM, max_val=1.0, n_ticks=5)

# Add note about normalization
ax.text(0.5, -0.08, "Values normalized to 0–1 scale. Raw data in Table S1.",
        transform=ax.transAxes, fontsize=8, ha="center", style="italic",
        color="#666666")

fig.tight_layout(pad=2)
finalize_figure(fig, "radar_multi_property")
```

### Step 3: Caption

```
Figure X. Multi-property radar chart comparing control, 10% WER, and 15% WER
formulations across six performance indices. Values normalized to 0–1 scale;
raw data and statistical analysis in Table S1. The 15% WER group shows balanced
improvement across mechanical properties with a slight reduction in workability.
```

---

## Tutorial 7: Evidence Heatmap for Review Figures

**Scenario**: Literature evidence coverage matrix for a WER-EA mini-review.

### Step 1: Prepare data

```python
claims = [
    "Epoxy improves bond strength",
    "WER improves moisture resistance",
    "Curing mechanism is crosslinking",
    "Optimal dosage is 12–18%",
    "Field performance validated",
    "Storage stability acceptable",
    "Cost-effectiveness demonstrated",
]

evidence_layers = ["FTIR", "SEM", "XRD", "Mechanical", "Durability", "Field"]

# Evidence matrix: 1=direct, 0.5=indirect, 0=absent, -1=not searched
data = np.array([
    [1.0, 0.5, 0.0, 1.0, 0.5, 0.0],   # bond strength
    [0.5, 0.0, 0.0, 0.5, 1.0, 0.0],   # moisture resistance
    [1.0, 0.5, 0.5, 0.0, 0.0, 0.0],   # curing mechanism
    [0.0, 0.0, 0.0, 1.0, 0.5, 0.0],   # optimal dosage
    [0.0, 0.0, 0.0, 0.0, 0.0, 0.0],   # field performance
    [0.0, 0.0, 0.0, 0.5, 0.5, 0.0],   # storage stability
    [0.0, 0.0, 0.0, 0.0, 0.0, 0.0],   # cost-effectiveness
])
```

### Step 2: Create figure

```python
apply_pub_style()
fig, ax = plt.subplots(figsize=(8, 5))

im = ax.imshow(data, cmap="YlOrRd", aspect="auto", vmin=-1, vmax=1)

ax.set_xticks(range(len(evidence_layers)))
ax.set_xticklabels(evidence_layers, rotation=45, ha="right", fontsize=9)
ax.set_yticks(range(len(claims)))
ax.set_yticklabels(claims, fontsize=9)

# Add cell annotations
symbols = {1.0: "✓", 0.5: "~", 0.0: "✗", -1.0: "?"}
for i in range(data.shape[0]):
    for j in range(data.shape[1]):
        sym = symbols.get(data[i, j], "?")
        color = "white" if data[i, j] > 0.5 else "#333333"
        ax.text(j, i, sym, ha="center", va="center", fontsize=10,
                fontweight="bold", color=color)

cbar = fig.colorbar(im, ax=ax, shrink=0.8, ticks=[-1, 0, 0.5, 1])
cbar.set_ticklabels(["Not searched", "Absent", "Indirect", "Direct"])
cbar.ax.tick_params(labelsize=8)

add_panel_label(ax, "(a)")
fig.tight_layout(pad=2)
finalize_figure(fig, "evidence_heatmap_review")
```

### Step 3: Caption

```
Figure X. Literature evidence coverage matrix for waterborne epoxy modified
emulsified asphalt (WER-EA). ✓ = direct evidence, ~ = indirect or partial
evidence, ✗ = absent, ? = not searched in this review. Major gaps exist in
field validation, storage stability, and cost-effectiveness evidence.
```

---

## Tutorial 8: SEM Image Plate with Scale Bars

**Scenario**: SEM images comparing morphology of neat asphalt and WER-asphalt.

### Step 1: Load images

```python
from PIL import Image

# Load real SEM images (replace with actual paths)
images = [
    (Image.open("sem_control_500x.tiff"), "Control (500×)"),
    (Image.open("sem_10pct_500x.tiff"), "10% WER (500×)"),
    (Image.open("sem_15pct_500x.tiff"), "15% WER (500×)"),
    (Image.open("sem_20pct_500x.tiff"), "20% WER (500×)"),
    (Image.open("sem_15pct_2000x.tiff"), "15% WER (2000×)"),
    (Image.open("sem_15pct_5000x.tiff"), "15% WER (5000×)"),
]
```

### Step 2: Create figure

```python
apply_pub_style()
fig, axes = plt.subplots(2, 3, figsize=(12, 8))

for ax, (img, label) in zip(axes.flat, images):
    ax.imshow(img, cmap="gray")
    ax.set_title(label, fontsize=9, pad=4)
    ax.axis("off")

    # Add scale bar
    bar_length_px = 50  # adjust per image
    bar_x = img.width * 0.85
    bar_y = img.height * 0.92
    ax.plot([bar_x - bar_length_px, bar_x], [bar_y, bar_y],
            color="white", linewidth=2)
    ax.text(bar_x - bar_length_px / 2, bar_y - 15, "50 μm",
            ha="center", va="top", fontsize=7, color="white",
            fontweight="bold")

# Panel labels
for i, ax in enumerate(axes.flat):
    add_panel_label(ax, f"({chr(97 + i)})", loc="top-left",
                    fontsize=11)

fig.tight_layout(pad=1)
finalize_figure(fig, "sem_morphology_plate")
```

### Step 3: Caption

```
Figure X. SEM images of (a) neat asphalt, (b–d) WER-asphalt at 10%, 15%,
and 20% WER content (500×), (e–f) 15% WER at 2000× and 5000× showing
co-continuous morphology. Scale bars: 50 μm (a–d), 20 μm (e), 10 μm (f).
Images are representative of 5 fields per sample.
```

---

## Tutorial 9: TGA / DTG Thermal Analysis

**Scenario**: Comparing thermal stability of neat polymer and WER-modified
asphalt.

### Step 1: Prepare data

```python
temp = np.linspace(50, 800, 500)

def tga_curve(temp, onset, mid, residue):
    """Simulated TGA curve."""
    curve = np.ones_like(temp) * 100
    mask = temp > onset
    curve[mask] = 100 - (100 - residue) * (
        1 / (1 + np.exp(-0.05 * (temp[mask] - mid)))
    )
    return curve

tga_neat = tga_curve(temp, onset=300, mid=400, residue=15)
tga_wer = tga_curve(temp, onset=320, mid=420, residue=22)

dtg_neat = -np.gradient(tga_neat, temp)
dtg_wer = -np.gradient(tga_wer, temp)
```

### Step 2: Create figure

```python
apply_pub_style()
fig, ax1 = plt.subplots(figsize=(7, 4))

# TGA curves
colors = [PALETTE_CBM["control"], PALETTE_CBM["modified"]]
ax1.plot(temp, tga_neat, color=colors[0], linewidth=1.8, label="Neat TGA")
ax1.plot(temp, tga_wer, color=colors[1], linewidth=1.8, label="WER TGA")
ax1.set_xlabel("Temperature (°C)")
ax1.set_ylabel("Mass (%)", color="#333333")
ax1.tick_params(axis="y", labelcolor="#333333")

# DTG curves (secondary axis)
ax2 = ax1.twinx()
ax2.plot(temp, dtg_neat, color=colors[0], linewidth=1.2, linestyle="--",
         label="Neat DTG")
ax2.plot(temp, dtg_wer, color=colors[1], linewidth=1.2, linestyle="--",
         label="WER DTG")
ax2.set_ylabel("DTG (%/°C)", color="#333333")
ax2.tick_params(axis="y", labelcolor="#333333")

# Mark onset temperatures
for onset, label, color in [(300, "Neat onset", colors[0]),
                             (320, "WER onset", colors[1])]:
    ax1.axvline(onset, color=color, linestyle=":", linewidth=1, alpha=0.7)
    ax1.text(onset + 5, 95, label, fontsize=7, color=color, rotation=90,
             va="top")

# Combined legend
lines1, labels1 = ax1.get_legend_handles_labels()
lines2, labels2 = ax2.get_legend_handles_labels()
ax1.legend(lines1 + lines2, labels1 + labels2, fontsize=8, frameon=False,
           loc="lower left")

add_panel_label(ax1, "(a)")
fig.tight_layout(pad=2)
finalize_figure(fig, "tga_dtg_thermal")
```

### Step 3: Caption

```
Figure X. TGA and DTG curves of neat asphalt and WER-modified asphalt under
N₂ atmosphere (10°C/min). WER modification increases the onset decomposition
temperature from 300°C to 320°C and increases char residue from 15% to 22%,
consistent with improved thermal stability. DTG peak shift from 400°C to 420°C
suggests enhanced crosslinking density.
```

---

## Tutorial 10: Response Surface (DOE)

**Scenario**: Bond strength as a function of WER content and curing temperature
from a central composite design.

### Step 1: Prepare data

```python
from scipy.interpolate import griddata

# Experimental points (WER %, Temperature °C, Bond strength MPa)
experimental = np.array([
    [5, 25, 0.52], [10, 25, 0.65], [15, 25, 0.78], [20, 25, 0.70],
    [25, 25, 0.60], [5, 40, 0.55], [10, 40, 0.70], [15, 40, 0.82],
    [20, 40, 0.73], [25, 40, 0.63], [5, 55, 0.48], [10, 55, 0.60],
    [15, 55, 0.75], [20, 55, 0.68], [25, 55, 0.58],
])

wer = experimental[:, 0]
temp = experimental[:, 1]
strength = experimental[:, 2]

# Interpolate for smooth surface
wer_grid = np.linspace(5, 25, 50)
temp_grid = np.linspace(25, 55, 50)
W, T = np.meshgrid(wer_grid, temp_grid)
Z = griddata((wer, temp), strength, (W, T), method='cubic')
```

### Step 2: Create figure

```python
apply_pub_style()
fig, ax = plt.subplots(figsize=(7, 5))

# Contour surface
im = ax.contourf(W, T, Z, levels=20, cmap='YlOrRd')
ax.contour(W, T, Z, levels=5, colors='k', linewidths=0.5, alpha=0.5)

# Overlay experimental points
scatter = ax.scatter(wer, temp, c=strength, cmap='YlOrRd', edgecolors='k',
                     linewidths=1, s=80, zorder=5)
for i, (w, t, s) in enumerate(experimental):
    ax.annotate(f"{s:.2f}", (w, t), fontsize=6, ha="center", va="bottom",
                xytext=(0, 5), textcoords="offset points")

# Mark optimum
opt_idx = np.argmax(strength)
ax.plot(wer[opt_idx], temp[opt_idx], marker='*', markersize=18,
        color=PALETTE_CBM["optimal"], zorder=6, markeredgecolor='k',
        markeredgewidth=0.5)

ax.set_xlabel("WER content (%)")
ax.set_ylabel("Curing temperature (°C)")
cbar = fig.colorbar(im, ax=ax, shrink=0.85)
cbar.set_label("Bond strength (MPa)")

add_panel_label(ax, "(a)")
fig.tight_layout(pad=2)
finalize_figure(fig, "response_surface_doe")
```

### Step 3: Caption

```
Figure X. Response surface for bond strength as a function of WER content and
curing temperature. Experimental points (n = 3 per condition) are overlaid.
The star marks the experimental optimum (15% WER, 40°C). Model: quadratic RSM
(R² = 0.96, adjusted R² = 0.94). Optimization beyond the experimental range
requires additional data points.
```

---

## Quick Reference: Export Checklist

For each final figure:

- [ ] SVG exported with `bbox_inches='tight'` and `svg.fonttype='none'`.
- [ ] PNG exported at 300 dpi as raster preview.
- [ ] Source data saved as CSV.
- [ ] Plotting script saved.
- [ ] Caption drafted with: what is shown, material/system, condition,
      error bar definition, cautious interpretation, boundary statement.
- [ ] Check journal-specific requirements (see `figure-production-spec.md`).
- [ ] Open SVG in Illustrator/Inkscape to verify text is editable.
- [ ] Print grayscale version to verify all groups distinguishable.

---
