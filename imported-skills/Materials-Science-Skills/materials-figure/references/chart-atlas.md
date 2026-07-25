# Materials Science Chart Atlas

Use this atlas when choosing a production figure family before coding. Each
chart type links a **materials claim** to a **safe code pattern**, a **visual
reference**, and the **reviewer risk** most commonly flagged for that chart
type.

**Start with the claim, then choose the chart.** Do not start with the
prettiest chart and retrofit a claim.

Each entry below includes: chart family name, best use, code pattern (Python),
reviewer risk, and when NOT to use the chart.

---

## Chart Family Index

| # | Chart family | Best use | Code helper | Reviewer risk |
|---|---|---|---|---|
| 1 | Grouped bar | Control vs. modified under multiple conditions | `make_grouped_bar()` | Missing replicate count or test condition |
| 2 | Dosage-performance curve | Optimization trend across additive/modifier dosage | `make_line_trend()` | Calling one dosage "optimal" without durability |
| 3 | FTIR overlay | Curing or chemical-change evidence | `make_ftir_overlay()` | Claiming full mechanism from FTIR alone |
| 4 | XRD stacked pattern | Hydration or crystalline phase comparison | `make_xrd_pattern()` | Unassigned peaks or no baseline correction |
| 5 | Durability retention bar | Moisture, aging, freeze-thaw, UV screening | `make_grouped_bar()` | Retention without original absolute values |
| 6 | Mechanical radar | Multi-index comparison for screening | `make_radar()` | Hiding weak raw indicators behind normalization |
| 7 | SEM / fluorescence plate | Morphology and phase distribution | Manual panel assembly | Representative image without field count |
| 8 | TGA / DTG paired plot | Thermal stability and decomposition | `make_tga_dtg_overlay()` | Overinterpreting small peak shifts |
| 9 | Box / violin plot | Replicate-rich performance datasets | `make_boxplot()` | Using distribution plots for n < 5 |
| 10 | Heatmap (sequential) | Property correlation or composition matrix | `make_heatmap()` | False color boundaries from rainbow cmap |
| 11 | Heatmap (diverging / z-score) | Deviation from mean across conditions | `make_heatmap()` with `RdBu_r` | Confusing z-score with absolute value |
| 12 | Stacked bar | Composition or cumulative contribution | `make_stacked_bar()` | Stacking more than 5 categories |
| 13 | Mechanism schematic | Evidence-chain summary | Manual drawing | Drawing unsupported causal links |
| 14 | Evidence heatmap | Literature evidence coverage matrix | `make_heatmap()` | Treating empty cells as "no evidence" vs "not searched" |
| 15 | Research gap matrix | Gap identification for review papers | `make_heatmap()` | Confusing "few studies" with "no studies" |
| 16 | Graphical abstract | Visual summary for journal submission | Manual schematic | Overclaiming in the visual summary |
| 17 | Pavement layer diagram | Interface / tack coat positioning | Manual schematic | Missing test location specification |
| 18 | Scatter / bubble plot | Two-variable correlation with optional third | `ax.scatter()` | Extrapolating trend from clustered data |
| 19 | Forest / interval plot | Effect sizes with confidence intervals | `ax.errorbar()` horizontal | Heterogeneous confidence interval widths |
| 20 | Contour / response surface | DOE response optimization | `ax.contourf()` | Overinterpreting interpolation near edges |
| 21 | Scatter regression | Source-data association with linear fit | `make_scatter_regression()` | Treating association as mechanism |
| 22 | Boxplot with points | Small replicate groups with raw data visible | `make_boxplot_with_points()` | Hiding n or outlier rule |
| 23 | Violin distribution | Replicate-rich retention or strength distributions | `make_violin_plot()` | Using smooth density for low n |
| 24 | Contour response map | Two-factor response map with measured grid | `make_contour_map()` | Extrapolating beyond measured grid |
| 25 | 3D response surface | Two-factor optimization surface | `make_3d_surface()` | Over-selling visual curvature |
| 26 | Polar performance | Normalized multi-index profile | `make_polar_plot()` | Hiding raw values behind normalization |
| 27 | Errorbar trend | Time, aging, or dosage trend with SD/SE/CI | `make_errorbar_trend()` | Undefined error bars |
| 28 | Dual-axis trend | Paired responses with different units | `make_dual_axis_trend()` | Implying causal coupling from co-variation |
| 29 | Correlation heatmap | Property-property correlation matrix | `make_correlation_heatmap()` | Treating correlation as proof |
| 30 | Stacked composition | Formulation or phase fraction comparison | `make_stacked_composition_bar()` | Comparing totals that do not balance |

---

## 1. Grouped Bar Chart

**When to use**: Comparing 2–5 material variants across 2–4 test conditions.

**Common materials claims**:
- "Modified asphalt shows higher bond strength than control under both dry and
  moisture-conditioned states."
- "The 15% epoxy group outperforms all other dosages."

**Code pattern**:

```python
# Note: materials_plot_lib was removed in the transition to LLM-as-artist mode.
# The LLM now writes plotting code directly using matplotlib.
# This code pattern is kept as a reference example.

import matplotlib.pyplot as plt

fig, ax = plt.subplots(figsize=(6, 4))
labels = ["Dry", "Moisture", "Freeze-thaw"]
groups = ["Control", "10% WER", "15% WER", "20% WER"]
values = [
    [0.45, 0.32, 0.28],   # Control
    [0.62, 0.51, 0.44],   # 10% WER
    [0.78, 0.68, 0.59],   # 15% WER
    [0.71, 0.55, 0.47],   # 20% WER
]
errors = [
    [0.04, 0.03, 0.03],
    [0.05, 0.04, 0.04],
    [0.06, 0.05, 0.05],
    [0.05, 0.04, 0.04],
]
make_grouped_bar(ax, labels, groups, values, PALETTE_CBM, error_bars=errors,
                 ylabel="Bond strength (MPa)")
```

**When NOT to use**:
- More than 6 groups (use faceted bar or line instead).
- Continuous x-axis data (use line trend instead).
- Only one group (use simple bar with individual points).

**Reviewer checklist**:
- [ ] Replicate count (n) stated in caption.
- [ ] Error bar type defined (SD, SE, or CI).
- [ ] Test condition specified (temperature, curing time, standard).
- [ ] Statistical comparison (if claimed "significant").

---

## 2. Dosage-Performance Curve (dosage-performance)

**When to use**: Property measured across a continuous dosage range (e.g., 0%,
5%, 10%, 15%, 20% epoxy content).

**Common materials claims**:
- "Bond strength increases with epoxy content up to 15%, then decreases."
- "The optimal dosage window is 12–18% based on mechanical performance."

**Code pattern**:

```python
from materials_plot_lib import apply_pub_style, make_line_trend, PALETTE_CBM

apply_pub_style()
fig, ax = plt.subplots(figsize=(6, 4))
dosage = [0, 5, 10, 15, 20, 25]
strength = [0.45, 0.58, 0.72, 0.78, 0.71, 0.63]
sd = [0.04, 0.05, 0.05, 0.06, 0.05, 0.04]
make_line_trend(ax, dosage, [strength], ["Bond strength"], PALETTE_CBM,
                xlabel="WER content (%)", ylabel="Bond strength (MPa)",
                fill_between=[sd])
# Mark optimum region
ax.axvspan(12, 18, alpha=0.12, color=PALETTE_CBM["optimal"])
ax.annotate("Optimum range", xy=(15, 0.78), xytext=(18, 0.82),
            arrowprops=dict(arrowstyle="->", color="#4F7C6A"),
            fontsize=8, color="#4F7C6A")
```

**When NOT to use**:
- Only 2 data points (use simple comparison).
- Non-continuous x-axis (use grouped bar instead).
- Multiple independent variables (use heatmap or response surface).

**Reviewer checklist**:
- [ ] Optimum claim backed by statistical test (not just visual peak).
- [ ] If "optimum" is claimed, durability data at that dosage is also shown.
- [ ] Trend direction stated with evidence strength ("suggests" not "proves").
- [ ] Uncertainty bands present (fill_between or error bars).

---

## 3. FTIR Overlay

**When to use**: Showing chemical changes (curing, crosslinking, degradation)
across material variants or conditions.

**Common materials claims**:
- "The disappearance of the 915 cm⁻¹ epoxide peak confirms curing."
- "The shift in the O–H stretching region suggests hydrogen bonding."

**Code pattern**:

```python
from materials_plot_lib import apply_pub_style, make_ftir_overlay, PALETTE_CBM

apply_pub_style()
fig, ax = plt.subplots(figsize=(7, 4))
wn = np.linspace(4000, 400, 1000)
# Simulated spectra
neat = gaussian_peak(wn, 3400, 50) + gaussian_peak(wn, 1730, 30) + gaussian_peak(wn, 915, 20)
cured = gaussian_peak(wn, 3400, 45) + gaussian_peak(wn, 1730, 35)  # 915 peak gone
make_ftir_overlay(ax, wn, [neat, cured], ["Neat resin", "Cured (7 d)"],
                  PALETTE_CBM,
                  peak_annotations={915: "Epoxide", 1730: "C=O", 3400: "O–H"})
```

**When NOT to use**:
- Quantitative comparison (use bar chart of peak heights instead).
- More than 5 overlays (too crowded — use stacked offset).

**Reviewer checklist**:
- [ ] Key peaks annotated with wavenumber.
- [ ] X-axis inverted (wavenumber decreases left to right).
- [ ] Claims use "consistent with" not "confirms" (FTIR alone cannot confirm mechanism).
- [ ] Baseline correction stated if applied.
- [ ] If peak area is quantified, state integration range.

---

## 4. XRD Stacked Pattern

**When to use**: Comparing crystalline phase changes across hydration time,
sintering temperature, or composition.

**Common materials claims**:
- "Portlandite peaks decrease with increasing fly ash replacement."
- "New C–S–H peaks appear after 28 d curing."

**Code pattern**:

```python
from materials_plot_lib import apply_pub_style, make_xrd_pattern, PALETTE_CBM

apply_pub_style()
fig, ax = plt.subplots(figsize=(7, 4))
two_theta = np.linspace(5, 70, 1000)
# Simulated patterns
ref = cement_xrd_pattern(two_theta, "OPC_3d")
blend = cement_xrd_pattern(two_theta, "FA30_28d")
make_xrd_pattern(ax, two_theta, [ref, blend], ["OPC 3 d", "FA30 28 d"],
                 PALETTE_CBM, offset=1.0,
                 peak_annotations={18.0: "CH", 29.4: "C₃S", 34.1: "C–S–H"})
```

**When NOT to use**:
- Amorphous materials (use PDF/total scattering instead).
- Quantitative phase analysis (use Rietveld refinement bar chart).

**Reviewer checklist**:
- [ ] Peak assignments match ICDD/JCPDS cards.
- [ ] 2θ range and step size stated.
- [ ] Instrument conditions noted (Cu Kα, voltage, current).
- [ ] Baseline correction or background subtraction noted.
- [ ] No unassigned major peaks.

---

## 5. Durability Retention Bar

**When to use**: Showing property retention after durability exposure (moisture,
aging, freeze-thaw, UV, chemical).

**Common materials claims**:
- "The modified group retains 85% bond strength after 5 freeze-thaw cycles."
- "WER modification improves moisture resistance by 40%."

**Code pattern**:

```python
from materials_plot_lib import apply_pub_style, make_grouped_bar, PALETTE_CBM

apply_pub_style()
fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10, 4), width_ratios=[1, 1])

# Panel a: absolute values
labels = ["Control", "10% WER", "15% WER", "20% WER"]
make_grouped_bar(ax1, ["Before", "After"], labels,
                 [[0.45, 0.62, 0.78, 0.71], [0.28, 0.52, 0.66, 0.55]],
                 PALETTE_CBM, ylabel="Bond strength (MPa)")

# Panel b: retention ratio
retention = [r / b * 100 for r, b in zip([0.28, 0.52, 0.66, 0.55],
                                           [0.45, 0.62, 0.78, 0.71])]
make_grouped_bar(ax2, labels, ["Retention"], [retention],
                 PALETTE_CBM, ylabel="Retention (%)")
```

**When NOT to use**:
- Only one exposure condition (use simple before/after bar).
- Time-series degradation (use line trend).

**Reviewer checklist**:
- [ ] **Both** absolute values and retention ratio shown.
- [ ] Exposure conditions fully specified (cycles, temperature, duration, standard).
- [ ] Baseline (pre-exposure) value clearly labeled.
- [ ] Standard deviation or confidence interval present.
- [ ] Caption notes that retention alone does not prove field applicability.

---

## 6. Mechanical Radar Chart

**When to use**: Screening multiple performance indices for a material system
where no single metric dominates.

**Common materials claims**:
- "The 15% WER group shows balanced performance across all indices."
- "High dosage improves strength but sacrifices workability."

**Code pattern**:

```python
from materials_plot_lib import apply_pub_style, make_radar, PALETTE_CBM

apply_pub_style()
fig, ax = plt.subplots(figsize=(6, 6), subplot_kw=dict(projection="polar"))
categories = ["Bond strength", "Tensile", "Flexural", "Impact", "Hardness"]
series = {
    "Control": [0.45, 0.60, 0.55, 0.30, 0.70],
    "15% WER": [0.78, 0.82, 0.75, 0.55, 0.68],
}
make_radar(ax, categories, series, PALETTE_CBM, max_val=1.0)
```

**When NOT to use**:
- Only 2 indices (use grouped bar).
- Indices with very different scales (normalize first).
- Claiming "balanced" performance without showing raw values in supplement.

**Reviewer checklist**:
- [ ] Raw (unnormalized) values in supplement.
- [ ] Normalization method stated (0–1, % of control, z-score).
- [ ] Not hiding weak indicators behind normalization.
- [ ] At least 3 indices (otherwise use bar chart).

---

## 7. SEM / Fluorescence Image Plate

**When to use**: Showing morphology, microstructure, or phase distribution.

**Common materials claims**:
- "SEM shows a co-continuous morphology in the 15% WER blend."
- "Fluorescence microscopy confirms uniform WER dispersion."

**Assembly pattern**:

```python
fig, axes = plt.subplots(2, 3, figsize=(12, 8))
for ax, (img, label) in zip(axes.flat, images):
    ax.imshow(img, cmap="gray")
    ax.set_title(label, fontsize=9)
    add_scale_bar(ax, length=10, unit="μm", position="bottom-right")
    ax.axis("off")
```

**Reviewer checklist**:
- [ ] Scale bar present on **every** panel, with explicit length.
- [ ] Magnification stated in caption.
- [ ] Consistent brightness/contrast across panels.
- [ ] Number of fields imaged stated (not just "representative image").
- [ ] If phases are labeled, the identification technique is stated.
- [ ] No selective enhancement of one panel over another.

---

## 8. TGA / DTG Paired Plot

**When to use**: Comparing thermal stability and decomposition behavior.

**Common materials claims**:
- "WER modification increases the onset decomposition temperature by 15°C."
- "The DTG peak shifts from 380°C to 410°C, indicating improved thermal stability."

**Code pattern**:

```python
from materials_plot_lib import apply_pub_style, make_tga_dtg_overlay, PALETTE_CBM

apply_pub_style()
fig, ax = plt.subplots(figsize=(6, 4))
temp = np.linspace(50, 800, 500)
tga_neat = tga_curve(temp, onset=350)
tga_wer = tga_curve(temp, onset=365)
dtg_neat = np.gradient(tga_neat, temp)
dtg_wer = np.gradient(tga_wer, temp)
make_tga_dtg_overlay(ax, temp, tga_neat, dtg_neat, ("Neat TGA", "Neat DTG"))
```

**Reviewer checklist**:
- [ ] Onset temperature, T₅%, T₅₀%, and char residue reported.
- [ ] Heating rate and atmosphere stated (N₂, air, 10°C/min).
- [ ] Sample mass stated.
- [ ] Not overinterpreting small peak shifts (< 5°C) without replication.

---

## 9. Box / Violin Plot

**When to use**: Showing distribution of replicate-rich datasets (n ≥ 10).

**Common materials claims**:
- "The modified group shows higher median strength with lower variance."
- "Distribution plots reveal bimodal behavior in the control group."

**Code pattern**:

```python
from materials_plot_lib import apply_pub_style, make_boxplot, PALETTE_CBM

apply_pub_style()
fig, ax = plt.subplots(figsize=(6, 4))
data = {
    "Control": np.random.normal(0.45, 0.08, 20).tolist(),
    "10% WER": np.random.normal(0.62, 0.06, 20).tolist(),
    "15% WER": np.random.normal(0.78, 0.07, 20).tolist(),
}
make_boxplot(ax, list(data.keys()), data, PALETTE_CBM, ylabel="Bond strength (MPa)")
```

**When NOT to use**:
- n < 5 (show individual points instead).
- Comparing only 2 groups (use bar with individual points).

**Reviewer checklist**:
- [ ] n ≥ 10 for box/violin; otherwise show individual points.
- [ ] Individual data points overlaid if n < 30.
- [ ] Outlier definition stated (1.5× IQR or other rule).
- [ ] Median and IQR clearly visible.

---

## 10. Heatmap (Sequential)

**When to use**: Showing property matrix, correlation, or composition-property
relationships.

**Common materials claims**:
- "Correlation analysis shows strong positive correlation between WER content
  and bond strength (r = 0.89)."

**Code pattern**:

```python
from materials_plot_lib import apply_pub_style, make_heatmap

apply_pub_style()
fig, ax = plt.subplots(figsize=(6, 5))
data = np.random.rand(5, 5)
labels = ["WER content", "Curing time", "Temperature", "Bond strength", "Tensile"]
make_heatmap(ax, data, labels, labels, cmap="YlOrRd", annot=True, fmt=".2f")
```

**Reviewer checklist**:
- [ ] Colormap is sequential (not diverging) for magnitude data.
- [ ] No rainbow colormap (`jet`, `rainbow`).
- [ ] Cell annotations present for key values.
- [ ] Colorbar labeled with units.

---

## 11. Heatmap (Diverging / Z-Score)

**When to use**: Showing **deviation from mean** across conditions — each cell
shows how far that value is from the column mean in standard deviation units.

**Common materials claims**:
- "The 15% WER group shows above-average performance across all conditions
  except freeze-thaw."

**Code pattern**:

```python
z = (data - data.mean(axis=0)) / data.std(axis=0)
im = ax.imshow(z.values, cmap='RdBu_r', aspect='auto', vmin=-2.5, vmax=2.5)
cbar.set_label('Z-score vs column mean')
```

**Reviewer checklist**:
- [ ] Diverging colormap (`RdBu_r`, `coolwarm`), not sequential.
- [ ] Z-score range symmetric (e.g., -2.5 to +2.5).
- [ ] Caption explains what z-score means (deviation from column mean).
- [ ] Not confused with absolute values.

---

## 12. Stacked Bar Chart

**When to use**: Showing composition or cumulative contribution.

**Common materials claims**:
- "The composite is 60% matrix, 25% fiber, and 15% filler by volume."

**Code pattern**:

```python
from materials_plot_lib import apply_pub_style, make_stacked_bar, PALETTE_CBM

apply_pub_style()
fig, ax = plt.subplots(figsize=(6, 4))
series = {"Matrix": [60, 55, 50], "Fiber": [25, 30, 30], "Filler": [15, 15, 20]}
make_stacked_bar(ax, ["Mix A", "Mix B", "Mix C"], series, PALETTE_CBM,
                 ylabel="Volume fraction (%)")
```

**When NOT to use**:
- More than 5 categories (too many slices).
- Comparing across groups where total varies (use grouped bar instead).

**Reviewer checklist**:
- [ ] Categories ≤ 5.
- [ ] Totals are meaningful (all should sum to 100% or the same value).
- [ ] Legend order matches stack order.

---

## 13–20. Additional Chart Types

### 13. Mechanism Schematic

**Use for**: Evidence-chain summary, interface mechanism, reaction pathway.

**Rules**:
- Solid arrows = direct evidence. Dashed arrows = inferred steps.
- Color by evidence tier: green = measured, orange = inferred, grey = speculative.
- Label each step with the characterization technique that supports it.
- Do not draw causal loops without mechanistic evidence.

### 14. Evidence Heatmap (Review Figures)

**Use for**: Literature evidence coverage matrix.

**Layout**:
- Rows = claims or mechanisms.
- Columns = evidence layers (FTIR, SEM, XRD, mechanical, durability, field).
- Cell values: ✓ (direct), ~ (indirect), ✗ (absent), ? (not searched).

**Rule**: Empty ≠ absent. Distinguish "not searched" from "no evidence found."

### 15. Research Gap Matrix

**Use for**: Gap identification in review papers.

**Layout**:
- Rows = topics or sub-topics.
- Columns = study counts or evidence depth.
- Color = coverage level (red = few studies, green = many studies).

**Rule**: "Few studies" ≠ "no studies." State exact counts.

### 16. Graphical Abstract

**Use for**: Visual summary for journal submission.

**Rules**:
- Follow journal-specific size requirements.
- Show the workflow and key result, not every experiment.
- One clear take-away message.
- No overclaiming in the visual summary.

### 17. Pavement Layer Diagram

**Use for**: Interface / tack coat positioning, field test locations.

**Rules**:
- Cross-section schematic with labeled layers.
- Mark test locations with symbols.
- Include thickness and material specification.
- Note: this is a schematic, not a to-scale drawing.

### 18. Scatter / Bubble Plot

**Use for**: Two-variable correlation, optionally with a third variable as size.

**Code pattern**:

```python
ax.scatter(x, y, s=size_var * scale, c=colors, edgecolors='white',
           linewidth=0.8, alpha=0.9)
ax.axvline(np.median(x), lw=1.2, ls='--', color='#767676', alpha=0.6)
ax.axhline(np.median(y), lw=1.2, ls='--', color='#767676', alpha=0.6)
# Label quadrants
ax.text(0.95, 0.95, "High-High", transform=ax.transAxes,
        fontsize=7.5, color='#888888', style='italic', ha='right', va='top')
```

**Reviewer checklist**:
- [ ] Trend line or correlation coefficient if claiming correlation.
- [ ] Not extrapolating from clustered data.
- [ ] Outliers identified and discussed.

### 19. Forest / Interval Plot

**Use for**: Effect sizes with confidence intervals, meta-analysis style.

**Code pattern**:

```python
ax.errorbar(effect_sizes, y_pos, xerr=[ci_low, ci_high],
            fmt='o', capsize=4, color=colors)
ax.axvline(0, color='grey', linestyle='--', linewidth=0.8)
```

**Reviewer checklist**:
- [ ] Confidence interval level stated (95% CI).
- [ ] Effect size metric defined (mean difference, % change, Cohen's d).
- [ ] Sample size per group shown.

### 20. Contour / Response Surface

**Use for**: DOE response optimization (two factors, one response).

**Code pattern**:

```python
ax.contourf(X, Y, Z, levels=20, cmap='YlOrRd')
ax.contour(X, Y, Z, levels=5, colors='k', linewidths=0.5)
ax.set_xlabel('Factor A')
ax.set_ylabel('Factor B')
cbar = fig.colorbar(im, ax=ax)
cbar.set_label('Response')
```

**Reviewer checklist**:
- [ ] Experimental points overlaid on the surface.
- [ ] Model type stated (linear, quadratic, RSM).
- [ ] R² or adjusted R² reported.
- [ ] Not overinterpreting extrapolation beyond experimental range.

---

## Usage Rules

- Keep performance figures separate from mechanism figures unless both
  measurements exist.
- Do not use a mechanism schematic as proof of chemical reaction.
- Do not infer durability from short-term bonding strength.
- For waterborne epoxy modified emulsified asphalt, separate emulsion
  stability, epoxy curing, interface bonding, viscosity, storage stability,
  and moisture/aging evidence.
- Put control, dosage, temperature, curing condition, and test standard in the
  figure plan or caption when available.

## Public Preview Boundary

The installable skill bundle does not ship generated chart-atlas PNG boards.
Use the compact repository-level preview board at
`docs/gallery/gallery_chart_atlas.png` for visual orientation, and use the
rules in this reference plus the figure-package templates for actual delivery.
The full generated atlas is a maintainer-side asset pack.

## LLM-as-Artist Mode

The LLM writes plotting code directly using matplotlib, following the code
patterns and reviewer checklists above. Use the public preview board only as
visual orientation. For source-level examples, see the figure-package templates
and small runnable examples.
