# Common Patterns — Materials Science Figure Making

Reusable layout and encoding patterns used across publication-grade materials-science scripts. Each pattern addresses a specific visualization need common in materials research: characterization overlay, performance comparison, mechanism schematic, or multi-figure narrative.

---

## Pattern 1: XRD Pattern Overlay (Phase Comparison)

For comparing crystalline phases across multiple samples or conditions. Use when showing phase evolution, hydration products, or filler interactions.

```python
fig, ax = plt.subplots(figsize=(7.2, 4.5))
apply_publication_style(font_size=14)

# Load XRD data
samples = [
    {'two_theta': theta_raw, 'intensity': intensity_raw, 'label': 'Raw'},
    {'two_theta': theta_aged, 'intensity': intensity_aged, 'label': 'Aged'},
]

colors = [PALETTE_CHARACTERIZATION['xrd_primary'],
          PALETTE_CHARACTERIZATION['xrd_secondary']]

for i, sample in enumerate(samples):
    two_theta = np.array(sample['two_theta'])
    intensity = np.array(sample['intensity'])
    intensity_norm = intensity / intensity.max()
    
    ax.plot(two_theta, intensity_norm, color=colors[i], lw=1.5, label=sample['label'])

# Mark reference peaks
ref_peaks = [
    {'two_theta': 26.65, 'phase': 'Quartz', 'hkl': '011'},
    {'two_theta': 25.3, 'phase': 'Anatase', 'hkl': '101'},
]
for peak in ref_peaks:
    ax.axvline(peak['two_theta'], color='gray', linestyle='--', lw=0.8, alpha=0.6)
    ax.text(peak['two_theta'], 1.02, f"{peak['phase']}\n({peak['hkl']})",
            ha='center', va='bottom', fontsize=9, color='gray')

ax.set_xlabel('2θ (°)', fontsize=14)
ax.set_ylabel('Intensity (a.u.)', fontsize=14)
ax.set_xlim(15, 70)
ax.legend(loc='upper right', frameon=False)

finalize_figure(fig, 'figures/xrd_overlay.svg', formats=['svg', 'png'])
```

**Rules**:
- Normalize all patterns to max=1.0 for visual comparison.
- Use 2–3 colors max; reserve stronger color for the hero sample.
- Mark reference peaks with dashed vertical lines and labels.
- X-axis range typically 15–70° for civil materials; adjust for your system.

---

## Pattern 2: FTIR Spectrum Overlay (Functional Group Tracking)

For tracking functional group evolution during curing, aging, or reaction. Use when showing epoxy curing (oxirane ring disappearance), asphalt aging (C=O growth), or cement hydration (C-S-H formation).

```python
fig, ax = plt.subplots(figsize=(7.2, 4.5))
apply_publication_style(font_size=14)

# Load FTIR data
spectra = [
    {'wavenumber': wn_uncured, 'absorbance': abs_uncured, 'label': 'Uncured'},
    {'wavenumber': wn_cured, 'absorbance': abs_cured, 'label': 'Cured'},
]

colors = [PALETTE_CHARACTERIZATION['ftir_primary'],
          PALETTE_CHARACTERIZATION['ftir_secondary']]

for i, spectrum in enumerate(spectra):
    wavenumber = np.array(spectrum['wavenumber'])
    absorbance = np.array(spectrum['absorbance'])
    absorbance_norm = absorbance / absorbance.max()
    
    ax.plot(wavenumber, absorbance_norm, color=colors[i], lw=1.5, label=spectrum['label'])

# Annotate key peaks
annotations = [
    {'wavenumber': 915, 'label': 'Oxirane', 'va': 'top'},
    {'wavenumber': 1730, 'label': 'C=O', 'va': 'top'},
    {'wavenumber': 3400, 'label': 'O-H', 'va': 'top'},
]
for ann in annotations:
    ax.axvline(ann['wavenumber'], color='gray', linestyle=':', lw=0.8, alpha=0.5)
    ax.text(ann['wavenumber'], 0.95, ann['label'], ha='center', va=ann['va'],
            fontsize=9, color='gray')

ax.invert_xaxis()  # FTIR convention: high wavenumber on left
ax.set_xlabel('Wavenumber (cm⁻¹)', fontsize=14)
ax.set_ylabel('Absorbance (a.u.)', fontsize=14)
ax.set_xlim(4000, 400)
ax.legend(loc='upper right', frameon=False)

finalize_figure(fig, 'figures/ftir_overlay.svg', formats=['svg', 'png'])
```

**Rules**:
- Invert x-axis (high wavenumber on left) — this is FTIR convention.
- Normalize spectra for visual comparison.
- Annotate key functional groups with vertical markers.
- Use 2–3 colors; reserve stronger color for the hero condition.

---

## Pattern 3: Performance Comparison Bar Chart (Material System Benchmarking)

For comparing mechanical, thermal, or durability properties across material systems. Use when benchmarking a new material against references or showing optimization results.

```python
fig, ax = plt.subplots(figsize=(7.2, 5.0))
apply_publication_style(font_size=14)

materials = ['Reference', 'Optimized A', 'Optimized B']
properties = ['Flexural strength', 'Elastic modulus']
values = [
    np.array([5.2, 7.8, 8.5]),   # Flexural strength (MPa)
    np.array([28, 35, 38]),       # Elastic modulus (GPa)
]
errors = [
    np.array([0.3, 0.4, 0.5]),   # Flexural strength errors
    np.array([2, 3, 3]),          # Elastic modulus errors
]

colors = [PALETTE_MATERIALS['neutral_mid'],
          PALETTE_MATERIALS['ceramics_orange'],
          PALETTE_MATERIALS['metals_blue']]

n_properties = len(properties)
n_materials = len(materials)
w = 0.8 / n_properties
x = np.arange(n_materials)

for i, (prop_vals, prop_name, color) in enumerate(zip(values, properties, colors)):
    offset = (i - (n_properties - 1) / 2) * w
    bars = ax.bar(x + offset, prop_vals, width=w, label=prop_name,
                  color=color, edgecolor='black', linewidth=1.5,
                  yerr=errors[i], error_kw={'elinewidth': 2, 'capthick': 2, 'capsize': 6})

# Add target line
target = 8.0
ax.axhline(target, color=PALETTE_MATERIALS['gold'], linestyle='--', lw=1.5, label=f'Target: {target} MPa')

ax.set_xticks(x)
ax.set_xticklabels(materials)
ax.set_ylabel('Performance', fontsize=14)
ax.legend(loc='upper left', frameon=False)

# Annotate values
for i, prop_vals in enumerate(values):
    for j, val in enumerate(prop_vals):
        offset = (i - (n_properties - 1) / 2) * w
        ax.text(j + offset, val + errors[i][j] + 0.5, f'{val:.1f}',
                ha='center', va='bottom', fontsize=10)

finalize_figure(fig, 'figures/performance_comparison.svg', formats=['svg', 'png'])
```

**Rules**:
- Group bars by material; use color to distinguish properties.
- Include error bars (standard deviation or confidence interval).
- Add target/specification lines when relevant.
- Annotate values above bars for clarity.
- Reserve green/red for improvement/degradation markers, not primary series.

---

## Pattern 4: Mechanism Schematic + Evidence Panels (Schematic-Led Composite)

For figures where one mechanism story leads, with 2–4 smaller evidence plots below. Use when defending a process-structure-property relationship.

```python
fig = plt.figure(figsize=(7.2, 6.2))
gs = fig.add_gridspec(2, 4, height_ratios=[2.2, 1.0], hspace=0.18, wspace=0.28)

# Top panel: hero schematic
ax_schematic = fig.add_subplot(gs[0, :])
ax_schematic.set_facecolor('white')

# Draw mechanism components
components = [
    {'label': 'Material A', 'position': (0.1, 0.5), 'color': PALETTE_MATERIALS['ceramics_orange']},
    {'label': 'Interface', 'position': (0.5, 0.5), 'color': PALETTE_MATERIALS['polymers_green']},
    {'label': 'Material B', 'position': (0.9, 0.5), 'color': PALETTE_MATERIALS['metals_blue']},
]
connections = [
    {'from': 'Material A', 'to': 'Interface', 'label': 'Bonding'},
    {'from': 'Interface', 'to': 'Material B', 'label': 'Load transfer'},
]
make_mechanism_schematic(ax_schematic, components, connections)
add_panel_label(ax_schematic, 'a', x=-0.06, y=1.02)

# Bottom panels: evidence plots
ax_ftir = fig.add_subplot(gs[1, 0:2])
# Plot FTIR evidence
ax_ftir.plot(wavenumber, absorbance, color=PALETTE_CHARACTERIZATION['ftir_primary'], lw=1.5)
ax_ftir.set_xlabel('Wavenumber (cm⁻¹)', fontsize=10)
ax_ftir.set_ylabel('Absorbance', fontsize=10)
ax_ftir.invert_xaxis()
add_panel_label(ax_ftir, 'b', x=-0.06, y=1.02)

ax_performance = fig.add_subplot(gs[1, 2:4])
# Plot performance evidence
ax_performance.bar(materials, bond_strength, color=PALETTE_MATERIALS['ceramics_orange'])
ax_performance.set_xlabel('Material system', fontsize=10)
ax_performance.set_ylabel('Bond strength (MPa)', fontsize=10)
add_panel_label(ax_performance, 'c', x=-0.06, y=1.02)

finalize_figure(fig, 'figures/mechanism_composite.svg', formats=['svg', 'png'])
```

**Rules**:
- Allocate 45–60% of total height to the hero schematic.
- Reuse softened versions of the same colors in the lower plots.
- Keep support plots quieter than the hero panel.
- The schematic should tell the story; the evidence panels back it up.

---

## Pattern 5: SEM/TEM Image Plate + Quantification (Image Plate + Quant)

For microscopy figures that combine image plates with quantitative analysis (grain size, porosity, particle distribution). Use when morphology evidence supports a claim.

```python
fig = plt.figure(figsize=(7.2, 6.5))
gs = fig.add_gridspec(2, 3, hspace=0.08, wspace=0.04)

# Top row: SEM images
for i, (img, label) in enumerate(zip(sem_images, ['a', 'b', 'c'])):
    ax = fig.add_subplot(gs[0, i])
    ax.imshow(img, cmap='gray')
    ax.set_xticks([])
    ax.set_yticks([])
    for spine in ax.spines.values():
        spine.set_visible(False)
    
    # Add scale bar
    scale_bar_length = 10  # microns
    ax.plot([10, 10 + scale_bar_length * 10], [img.shape[0] - 20, img.shape[0] - 20],
            color='white', lw=2)
    ax.text(10 + scale_bar_length * 5, img.shape[0] - 30, f'{scale_bar_length} μm',
            ha='center', va='top', color='white', fontsize=9)
    
    add_panel_label(ax, label, x=0.01, y=0.98, color='white')

# Bottom row: quantification
ax_dist = fig.add_subplot(gs[1, 0:2])
ax_dist.hist(grain_sizes, bins=20, color=PALETTE_MATERIALS['ceramics_orange'],
             edgecolor='black', linewidth=1)
ax_dist.set_xlabel('Grain size (μm)', fontsize=12)
ax_dist.set_ylabel('Frequency', fontsize=12)
add_panel_label(ax_dist, 'd', x=-0.06, y=1.02)

ax_stats = fig.add_subplot(gs[1, 2])
ax_stats.axis('off')
stats_text = f"Mean: {np.mean(grain_sizes):.1f} μm\nStd: {np.std(grain_sizes):.1f} μm\nn = {len(grain_sizes)}"
ax_stats.text(0.1, 0.5, stats_text, fontsize=12, va='center',
              bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))

finalize_figure(fig, 'figures/sem_plate.svg', formats=['svg', 'png'])
```

**Rules**:
- Use black background only for the image plate cells.
- Include scale bars in all microscopy images.
- Put quantification panels below or beside the images.
- Keep crop geometry and scale-bar placement consistent across the grid.
- Preserve image provenance (do not over-process).

---

## Pattern 6: Durability Retention Curve (Time-Series Performance)

For showing performance retention under aging, freeze-thaw, moisture, or UV conditioning. Use when validating long-term durability.

```python
fig, ax = plt.subplots(figsize=(7.2, 4.5))
apply_publication_style(font_size=14)

# Time-series data
cycles = np.array([0, 50, 100, 150, 200, 250, 300])
retention_reference = np.array([100, 92, 85, 78, 72, 66, 60])
retention_optimized = np.array([100, 96, 93, 90, 88, 86, 85])

ax.plot(cycles, retention_reference, color=PALETTE_MATERIALS['neutral_mid'],
        lw=2.5, marker='o', markersize=8, label='Reference')
ax.plot(cycles, retention_optimized, color=PALETTE_MATERIALS['ceramics_orange'],
        lw=2.5, marker='s', markersize=8, label='Optimized')

# Fill between to show retention band
ax.fill_between(cycles, retention_optimized, alpha=0.2, color=PALETTE_MATERIALS['ceramics_orange'])

# Add target retention line
target_retention = 80
ax.axhline(target_retention, color=PALETTE_MATERIALS['gold'], linestyle='--',
           lw=1.5, label=f'Target: {target_retention}%')

# Annotate final retention
ax.annotate(f'{retention_reference[-1]}%', xy=(cycles[-1], retention_reference[-1]),
            xytext=(cycles[-1] + 10, retention_reference[-1] - 5),
            fontsize=10, color=PALETTE_MATERIALS['neutral_mid'],
            arrowprops=dict(arrowstyle='->', color=PALETTE_MATERIALS['neutral_mid']))
ax.annotate(f'{retention_optimized[-1]}%', xy=(cycles[-1], retention_optimized[-1]),
            xytext=(cycles[-1] + 10, retention_optimized[-1] + 5),
            fontsize=10, color=PALETTE_MATERIALS['ceramics_orange'],
            arrowprops=dict(arrowstyle='->', color=PALETTE_MATERIALS['ceramics_orange']))

ax.set_xlabel('Conditioning cycles', fontsize=14)
ax.set_ylabel('Property retention (%)', fontsize=14)
ax.set_ylim(50, 110)
ax.legend(loc='lower left', frameon=False)

finalize_figure(fig, 'figures/durability_retention.svg', formats=['svg', 'png'])
```

**Rules**:
- Show both reference and optimized materials for comparison.
- Use fill_between to highlight the retention band.
- Add target retention lines (e.g., 80% after 300 cycles).
- Annotate final retention values.
- Use consistent time units (cycles, days, years).

---

## Pattern 7: Review Evidence Heatmap (Technique × Mechanism Matrix)

For review articles that map evidence strength across techniques and mechanisms. Use when synthesizing literature or showing research gaps.

```python
fig, ax = plt.subplots(figsize=(7.2, 5.5))
apply_publication_style(font_size=12)

# Evidence matrix (techniques × mechanisms)
techniques = ['XRD', 'FTIR', 'SEM', 'TGA', 'Rheology', 'DSR']
mechanisms = ['Hydration', 'Oxidation', 'Cross-linking', 'Degradation']
evidence_matrix = np.array([
    [0.9, 0.3, 0.2, 0.4],  # XRD
    [0.4, 0.8, 0.9, 0.6],  # FTIR
    [0.5, 0.6, 0.7, 0.8],  # SEM
    [0.7, 0.5, 0.3, 0.9],  # TGA
    [0.2, 0.4, 0.8, 0.5],  # Rheology
    [0.3, 0.7, 0.6, 0.7],  # DSR
])

make_evidence_heatmap(ax, evidence_matrix, techniques, mechanisms,
                      cmap='YlOrRd', cbar_label='Evidence strength',
                      annotate=True, fmt='{:.1f}')

ax.set_title('Evidence strength by technique and mechanism', fontsize=14, pad=15)

finalize_figure(fig, 'figures/evidence_heatmap.svg', formats=['svg', 'png'])
```

**Rules**:
- Use a sequential colormap (YlOrRd, Viridis) for evidence strength.
- Annotate cells with numeric values for clarity.
- Order techniques and mechanisms logically (e.g., by frequency or importance).
- Use this pattern for review figures, not original research.

---

## Pattern 8: Multi-Figure Narrative Composition (Manuscript-Level)

For orchestrating multiple figures within a manuscript. Each figure has a role (establish_system, prove_mechanism, show_performance, validate_durability) and evidence dependencies. Use when building a cumulative argument across figures.

```python
# This is a workflow pattern, not a single plot.
# Define the narrative arc in figure_storyboard.yaml:

narrative_arc = [
    {
        'figure_id': 'fig1',
        'role': 'establish_system',
        'claim': 'The emulsion system achieves stable bonding.',
        'panels': ['a: SEM interface', 'b: Dosage window'],
        'evidence_depends_on': [],
    },
    {
        'figure_id': 'fig2',
        'role': 'prove_mechanism',
        'claim': 'FTIR oxirane disappearance confirms cross-linking.',
        'panels': ['a: FTIR spectra', 'b: Rheology crossover'],
        'evidence_depends_on': ['fig1'],
    },
    {
        'figure_id': 'fig3',
        'role': 'show_performance',
        'claim': 'Bond strength peaks at optimal dosage.',
        'panels': ['a: Bond strength bar', 'b: Viscosity curve'],
        'evidence_depends_on': ['fig2'],
    },
    {
        'figure_id': 'fig4',
        'role': 'validate_durability',
        'claim': 'Performance persists under moisture aging.',
        'panels': ['a: Retention curve', 'b: Aging SEM'],
        'evidence_depends_on': ['fig3'],
    },
]

# For each figure, create a figure_contract.md and plot script.
# Ensure cross-figure consistency:
# - Shared palette (from target_journal preset)
# - Shared fonts and rcParams
# - No redundant panels across figures
# - Evidence flow: later figures cite earlier claims
```

**Rules**:
- Write the storyboard before individual figure contracts.
- Each figure must have a clear role and claim.
- Evidence dependencies must form a DAG (no cycles).
- Check for redundancy: no two figures show the same data panel.
- Use `check_storyboard.py` to validate narrative structure.

---

## Pattern 9: Dosage-Viscosity-Bonding Window (Multi-Axis Optimization)

For showing the optimization window where multiple properties (dosage, viscosity, bond strength) are balanced. Use when defending a processing window or formulation range.

```python
fig, ax1 = plt.subplots(figsize=(7.2, 4.5))
apply_publication_style(font_size=14)

# Dual-axis plot
dosage = np.array([2, 4, 6, 8, 10, 12])
viscosity = np.array([50, 80, 120, 180, 260, 380])  # mPa·s
bond_strength = np.array([0.4, 0.8, 1.2, 1.1, 0.9, 0.7])  # MPa

# Left axis: viscosity
color_visc = PALETTE_MATERIALS['metals_blue']
ax1.set_xlabel('WER-EA dosage (wt%)', fontsize=14)
ax1.set_ylabel('Viscosity (mPa·s)', fontsize=14, color=color_visc)
ax1.plot(dosage, viscosity, color=color_visc, lw=2.5, marker='o', markersize=8, label='Viscosity')
ax1.tick_params(axis='y', labelcolor=color_visc)

# Right axis: bond strength
ax2 = ax1.twinx()
color_bond = PALETTE_MATERIALS['ceramics_orange']
ax2.set_ylabel('Bond strength (MPa)', fontsize=14, color=color_bond)
ax2.plot(dosage, bond_strength, color=color_bond, lw=2.5, marker='s', markersize=8, label='Bond strength')
ax2.tick_params(axis='y', labelcolor=color_bond)

# Highlight optimal window
optimal_window = [5, 8]
ax1.axvspan(optimal_window[0], optimal_window[1], alpha=0.2, color=PALETTE_MATERIALS['improvement'])
ax1.text(np.mean(optimal_window), 0.95 * max(viscosity), 'Optimal window',
         ha='center', va='top', fontsize=11, color=PALETTE_MATERIALS['improvement'],
         fontweight='bold')

# Combined legend
lines1, labels1 = ax1.get_legend_handles_labels()
lines2, labels2 = ax2.get_legend_handles_labels()
ax1.legend(lines1 + lines2, labels1 + labels2, loc='upper left', frameon=False)

finalize_figure(fig, 'figures/dosage_window.svg', formats=['svg', 'png'])
```

**Rules**:
- Use dual axes when two properties have different units.
- Color-code each axis to match its data series.
- Highlight the optimal window with a shaded region.
- Include a combined legend.
- Clearly label the trade-off (e.g., "viscosity increases but bond strength peaks").

---

## Pattern 10: Weibull Reliability Plot (Brittle Material Statistics)

For showing the statistical reliability of brittle materials (ceramics, concrete, glass). Use when defending Weibull modulus or characteristic strength.

```python
fig, ax = plt.subplots(figsize=(7.2, 5.0))
apply_publication_style(font_size=14)

# Weibull data
strength = np.array([280, 300, 310, 320, 330, 340, 350, 360, 370, 380])
n = len(strength)
failure_probability = np.arange(1, n + 1) / (n + 1)

# Weibull plot (log-log scale)
ln_sigma = np.log(strength)
ln_ln_1_over_1_minus_P = np.log(np.log(1 / (1 - failure_probability)))

ax.scatter(ln_sigma, ln_ln_1_over_1_minus_P, color=PALETTE_MATERIALS['ceramics_orange'],
           s=80, zorder=5, label='Data')

# Linear fit
slope, intercept = np.polyfit(ln_sigma, ln_ln_1_over_1_minus_P, 1)
sigma_0 = np.exp(-intercept / slope)
m = slope

ln_sigma_fit = np.linspace(ln_sigma.min(), ln_sigma.max(), 100)
ln_ln_fit = slope * ln_sigma_fit + intercept
ax.plot(ln_sigma_fit, ln_ln_fit, color=PALETTE_MATERIALS['neutral_dark'],
        lw=2, linestyle='--', label=f'Weibull fit: m={m:.1f}, σ₀={sigma_0:.0f} MPa')

ax.set_xlabel('ln(σ)', fontsize=14)
ax.set_ylabel('ln(ln(1/(1-P)))', fontsize=14)
ax.legend(loc='upper left', frameon=False)

# Annotate Weibull modulus
ax.text(0.95, 0.05, f'Weibull modulus m = {m:.1f}', transform=ax.transAxes,
        ha='right', va='bottom', fontsize=12, fontweight='bold',
        bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))

finalize_figure(fig, 'figures/weibull_plot.svg', formats=['svg', 'png'])
```

**Rules**:
- Use log-log scale for Weibull plot.
- Include linear fit with Weibull modulus and characteristic strength.
- Annotate the Weibull modulus prominently.
- Show individual data points.
- Typical Weibull modulus: Al2O3 ~8-12, 3Y-TZP ~10-15.

---

## Pattern 11: Thermal Properties Panel (Conductivity + Expansion)

For showing thermal conductivity and coefficient of thermal expansion (CTE) together. Use when defending thermal barrier or thermal shock resistance.

```python
fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10, 4.5))
apply_publication_style(font_size=14)

# Left: thermal conductivity vs temperature
materials = ['Al2O3', 'ZrO2', 'SiC']
temperatures = np.array([25, 200, 400, 600, 800, 1000])
k_Al2O3 = np.array([30, 25, 20, 16, 13, 11])
k_ZrO2 = np.array([2.5, 2.3, 2.1, 2.0, 1.9, 1.8])
k_SiC = np.array([120, 100, 80, 65, 55, 48])

colors = [PALETTE_MATERIALS['ceramics_orange'],
          PALETTE_MATERIALS['ceramics_red'],
          PALETTE_MATERIALS['metals_blue']]

for mat, k, color in zip(materials, [k_Al2O3, k_ZrO2, k_SiC], colors):
    ax1.plot(temperatures, k, color=color, lw=2.5, marker='o', markersize=8, label=mat)

ax1.set_xlabel('Temperature (°C)', fontsize=14)
ax1.set_ylabel('Thermal conductivity (W/mK)', fontsize=14)
ax1.legend(loc='upper right', frameon=False)
add_panel_label(ax1, 'a', x=-0.06, y=1.02)

# Right: CTE bar chart
materials_bar = ['Al2O3', 'ZrO2', 'SiC']
CTE = np.array([8e-6, 10e-6, 4.5e-6])

bars = ax2.bar(materials_bar, CTE * 1e6, color=colors, edgecolor='black', linewidth=1.5)
ax2.set_xlabel('Material', fontsize=14)
ax2.set_ylabel('CTE (×10⁻⁶ /K)', fontsize=14)

# Annotate values
for bar, val in zip(bars, CTE):
    ax2.text(bar.get_x() + bar.get_width() / 2, bar.get_height() + 0.2,
             f'{val*1e6:.1f}', ha='center', va='bottom', fontsize=11)

add_panel_label(ax2, 'b', x=-0.06, y=1.02)

fig.tight_layout(pad=2)
finalize_figure(fig, 'figures/thermal_properties.svg', formats=['svg', 'png'])
```

**Rules**:
- Show thermal conductivity as a function of temperature (line plot).
- Show CTE as a bar chart (single value or range).
- Use consistent colors for the same material across panels.
- Annotate values for clarity.
- Typical values: Al2O3 ~30 W/mK, ZrO2 ~2-3 W/mK (thermal barrier), SiC ~120 W/mK (high k).

---

## Related files

- [SKILL.md](../SKILL.md) — When to use this skill
- [api.md](api.md) — Helper function signatures and PALETTE
- [figure-design-theory.md](figure-design-theory.md) — Rationale behind every pattern above; **see §4.3 for legend conventions** (position, sort order, symbol rules, dual-axis, certainty-tier, direct labels, colorblind-safe design, QA checklist)
- [characterization-figures.md](characterization-figures.md) — Technique-specific templates
- [performance-figures.md](performance-figures.md) — Performance curve patterns
- [mechanism-figures.md](mechanism-figures.md) — Mechanism schematic patterns
- [tutorials.md](tutorials.md) — End-to-end walkthroughs
