# Figure Design Theory for Materials Science

This is the governing reference for all materials-science figure production.
Read this before writing any plotting code. Every rule below exists because a
reviewer, editor, or co-author has flagged the violation in a real submission.

---

## 1. Core Philosophy

Scientific figures are **evidence delivery vehicles**, not illustrations.
Every pixel must serve one of three purposes:

1. **Encode data** — show measurements, trends, or distributions.
2. **Encode uncertainty** — error bars, confidence bands, replicate counts.
3. **Guide interpretation** — axis labels, annotations, panel labels.

If a visual element does none of these, remove it.

### The three questions

Before drawing anything, answer:

1. What **claim** does this figure support?
2. What **evidence** (data, image, statistic) backs that claim?
3. What **boundary** limits the claim's applicability?

If you cannot answer all three, the figure is not ready to plot.

---

## 2. Color Theory and Semantic Mapping

### 2.1 Core principle

Color in scientific figures is not decoration — it is a **semantic encoding
channel**. Every color must carry meaning that is consistent across all panels
of a figure.

### 2.2 Semantic roles for materials science

| Role | Use case | Recommended hue | Hex |
|---|---|---|---|
| Control / baseline | Unmodified material, reference group | Neutral blue-grey | `#4B6F8A` |
| Modified / experimental | Formulation variant, treatment, additive | Warm orange-brown | `#C47B45` |
| Optimal / best performer | Selected composition, peak dosage, peak performance | Forest green | `#4F7C6A` |
| Mechanism evidence | FTIR, XRD, SEM, characterization | Earth brown | `#8B6F47` |
| Comparison / competitor | Literature data, commercial product, standard | Neutral grey | `#8C8C8C` |
| Danger / warning | Failed group, degradation, risk threshold | Muted red | `#B85450` |
| Accent | Annotation, highlight, callout, optimum marker | Gold / amber | `#D4A574` |
| Baseline (soft) | Background reference, shaded region | Light blue-grey | `#A8B8C8` |

### 2.3 Unified low-saturation palette (Nature Machine Intelligence style)

When comparing **related variants** of the same material system (e.g., 3 epoxy
dosages, 4 curing temperatures), use a **single hue family** with increasing
saturation/darkness. This communicates "these are siblings, not unrelated
categories."

```python
PALETTE_SINGLE_HUE = {
    "variant_1": "#B4C0E4",   # light
    "variant_2": "#7884B4",   # medium
    "variant_3": "#484878",   # dark
    "variant_4": "#2C2C58",   # darkest
}
```

### 2.4 Domain-specific palettes

Different material families have natural color associations. Use them to
create instant visual recognition:

#### Asphalt / pavement

```python
PALETTE_ASPHALT = {
    "control":      "#6B7B8D",   # raw asphalt grey
    "modified":     "#8B6914",   # golden amber (binder)
    "optimal":      "#4A7C59",   # green (best performance)
    "moisture":     "#5B8FA8",   # blue (moisture condition)
    "aging":        "#C47B45",   # warm orange (RTFO/PAV aging)
    "mechanism":    "#8B6F47",   # earth brown (FTIR/SEM)
    "danger":       "#B85450",   # red (failure, stripping)
    "neutral":      "#8C8C8C",   # grey
}
```

#### Cement / concrete

```python
PALETTE_CEMENT = {
    "control":      "#7A7A7A",   # raw cement grey
    "modified":     "#4B6F8A",   # blue (supplementary cementite material)
    "optimal":      "#4F7C6A",   # green (best mix)
    "hydration":    "#C47B45",   # warm (hydration products)
    "mechanism":    "#8B6F47",   # earth (XRD/SEM evidence)
    "durability":   "#5B8FA8",   # blue (durability test)
    "danger":       "#B85450",   # red (cracking, ASR)
    "neutral":      "#9E9E9E",   # light grey
}
```

#### Polymers / composites

```python
PALETTE_POLYMER = {
    "control":      "#4B6F8A",   # neat resin blue-grey
    "modified":     "#9A4D8E",   # purple (filler, fiber)
    "optimal":      "#4F7C6A",   # green (best formulation)
    "mechanism":    "#C47B45",   # warm (FTIR, DSC)
    "thermal":      "#B85450",   # red (TGA, thermal events)
    "mechanical":   "#5B8FA8",   # blue (tensile, flexural)
    "danger":       "#D4574E",   # bright red (failure mode)
    "neutral":      "#8C8C8C",   # grey
}
```

#### Ceramics / structural

```python
PALETTE_CERAMIC = {
    "control":      "#8C8C8C",   # reference grey
    "modified":     "#C47B45",   # warm (dopant, additive)
    "optimal":      "#4F7C6A",   # green (best sintering)
    "mechanism":    "#8B6F47",   # earth (XRD phases)
    "thermal":      "#B85450",   # red (sintering temperature)
    "mechanical":   "#4B6F8A",   # blue (hardness, toughness)
    "danger":       "#D4574E",   # red (fracture, failure)
    "neutral":      "#9E9E9E",   # grey
}
```

### 2.5 NMI pastel palette (editorial multi-panel figures)

For dense multi-panel result figures where multiple panels must feel visually
unified — especially when comparing model families (e.g., dosage series,
temperature series):

```python
PALETTE_NMI_PASTEL = {
    # Baseline / comparison family (cool blue-grey)
    "baseline_dark":  "#484878",
    "baseline_mid":   "#7884B4",
    "baseline_soft":  "#B4C0E4",

    # Hero / proposed family (lilac → rose)
    "ours_tiny":   "#E4E4F0",
    "ours_base":   "#E4CCD8",
    "ours_large":  "#F0C0CC",

    # Background blocks for overview / concept panels
    "bg_lilac":  "#E0E0F0",
    "bg_aqua":   "#E0F0F0",
    "bg_peach":  "#F0E0D0",

    # Neutral support
    "neutral_light":  "#D8D8D8",
    "neutral_mid":    "#A8A8A8",
    "neutral_dark":   "#606060",

    # Accent only for directional annotations
    "delta_up":    "#2E9E44",
    "delta_down":  "#E53935",
}

DEFAULT_COLORS_NMI_PASTEL = [
    PALETTE_NMI_PASTEL["baseline_dark"],
    PALETTE_NMI_PASTEL["baseline_mid"],
    PALETTE_NMI_PASTEL["baseline_soft"],
    PALETTE_NMI_PASTEL["ours_tiny"],
    PALETTE_NMI_PASTEL["ours_base"],
    PALETTE_NMI_PASTEL["ours_large"],
]
```

### 2.6 Journal-specific palettes

#### CBM (Construction and Building Materials)

```python
PALETTE_CBM = {
    "control":    "#4B6F8A",
    "modified":   "#C47B45",
    "optimal":    "#4F7C6A",
    "mechanism":  "#8B6F47",
    "accent":     "#D4A574",
    "danger":     "#B85450",
    "neutral":    "#8C8C8C",
}
```

#### CCC (Cement and Concrete Composites)

```python
PALETTE_CCC = {
    "control":    "#3A5A7C",
    "modified":   "#C17817",
    "optimal":    "#2D6A4F",
    "mechanism":  "#7A4F2E",
    "accent":     "#D4A574",
    "danger":     "#9B2335",
    "neutral":    "#6B6B6B",
}
```

### 2.7 Color rules

#### Consistency rule

The **same** material variant keeps the **same** color in **every** panel of a
figure. Do not recolor "15% epoxy" from orange in panel (a) to green in panel
(c) just because that panel needs more contrast.

#### Signed semantics

Reserve green and red for **directional meaning**:

- Green = improvement, pass, increase, positive
- Red = decline, fail, decrease, risk, warning

Do not use green for "sample 3" or red for "sample 5" — that implies judgment.

#### Colorblind accessibility

- **Never** rely on red-green contrast alone. At least 8% of male readers
  have red-green color deficiency.
- Use blue-orange instead of red-green for contrast.
- Add marker shapes (`o`, `s`, `^`, `D`, `v`) alongside color.
- Add hatching patterns (`//`, `\\`, `xx`, `++`) for bar charts.
- Test figures in grayscale: if information is lost, add pattern or shape cues.

#### Grayscale test

Print the figure in grayscale. If two groups become indistinguishable, add:
- Different marker shapes
- Different line styles (solid, dashed, dotted)
- Direct labels instead of legends
- Hatching patterns on bars

#### No rainbow

Do not use `jet`, `rainbow`, `hsv`, or other rainbow colormaps. They:
- Create false boundaries between continuous data
- Are not perceptually uniform
- Fail in grayscale
- Are hostile to colorblind readers

Use sequential (`YlOrRd`, `viridis`, `magma`) or diverging (`RdBu_r`,
`coolwarm`) colormaps instead.

---

## 3. Typography and Fonts

### 3.1 Mandatory font stack

Every materials figure script must begin with:

```python
plt.rcParams['font.family'] = 'sans-serif'
plt.rcParams['font.sans-serif'] = ['Arial', 'DejaVu Sans', 'Liberation Sans']
plt.rcParams['svg.fonttype'] = 'none'
```

**Why `svg.fonttype = 'none'`**: matplotlib's default (`'path'`) converts every
glyph to a bezier curve. The result is visually identical but every `<text>`
element becomes a `<path d="M...">` — unselectable, unsearchable, and impossible
to realign in Illustrator or Inkscape. With `'none'`, text stays as SVG `<text>`
nodes. Font substitution happens at render time.

**Why three fonts in the stack**: `Arial` is standard on macOS/Windows. `DejaVu
Sans` ships with matplotlib and is the Linux fallback. `Liberation Sans` is
metric-compatible with Arial on RHEL/Ubuntu. The cascade guarantees identical
letter-spacing on all platforms.

### 3.2 Font size hierarchy

| Context | Publication (single-column) | Presentation / poster |
|---|---|---|
| Axis labels | 8–10 pt | 14–18 pt |
| Tick labels | 7–9 pt | 12–14 pt |
| Panel labels (a, b, c) | 10–12 pt bold | 16–20 pt bold |
| Legend | 7–8 pt | 12–14 pt |
| In-bar / in-cell annotation | 6–7 pt | 10–12 pt |
| Caption (in figure) | 8–9 pt | 12–14 pt |
| Large bar panels (figsize > 28 in) | 24 pt | — |
| Axis labels (large panels) | 32–54 pt via per-label override | — |

### 3.3 Panel label placement

```python
ax.text(-0.08, 1.05, "a", transform=ax.transAxes,
        fontsize=12, fontweight="bold", va="top", ha="left")
```

- Use **bold lowercase** (a, b, c).
- Place at top-left via `transAxes`.
- Size: 20–22 pt for large multi-panel figures, 10–12 pt for compact layouts.
- Never use (A), (B), (C) or Fig. 1a — journals want lowercase without parentheses.

### 3.4 Unit formatting

Use standard SI notation with proper superscripts:

| Correct | Wrong |
|---|---|
| `cm⁻¹` | `cm-1` |
| `W/(m·K)` | `W/mK` |
| `MPa` | `Mpa` |
| `°C` | `C` or `oC` |
| `2θ (°)` | `2-theta` |
| `μm` | `um` |

Use matplotlib's mathtext for superscripts:

```python
ax.set_xlabel(r"Wavenumber (cm$^{-1}$)")
ax.set_ylabel(r"Thermal conductivity (W m$^{-1}$ K$^{-1}$)")
```

---

## 4. Layout Rules

### 4.1 Figure size recommendations

| Chart type | figsize (inches) | Aspect ratio | Notes |
|---|---|---|---|
| Single grouped bar (3–4 groups) | (4.5, 3.5) | 1.3:1 | Standard single-column |
| Multi-panel (2 panels) | (8, 4) | 2:1 | Side-by-side |
| Multi-panel (3–4 panels) | (10, 6) | 1.7:1 | 2×2 grid |
| Multi-panel (6+ panels) | (14, 10) | 1.4:1 | 2×3 or 3×2 |
| Large multi-metric bar | (28–45, 6–12) | 3–4:1 | Width ≈ 3–4× height |
| Grand multi-panel (GridSpec) | (22, 17) | 1.3:1 | Full-page figure |
| Line / trend | (5, 3) | 1.7:1 | Standard |
| Heatmap | (5, 4) | 1.25:1 | Square-ish |
| XRD pattern (stacked) | (6, 3) | 2:1 | Wide for 2θ axis |
| FTIR overlay | (6, 3.5) | 1.7:1 | Wide for wavenumber |
| TGA / DTG overlay | (5, 3.5) | 1.4:1 | Dual Y-axis |
| Radar / polar | (5, 5) | 1:1 | Must be square |
| SEM / fluorescence plate | (8, 6) | 1.3:1 | Depends on panel count |
| Mechanism schematic | (6, 4) | 1.5:1 | Schematic layout |
| Evidence heatmap | (8, 5) | 1.6:1 | Wide for claim columns |
| Graphical abstract | (8, 4) | 2:1 | Journal-specific |

### 4.2 Axes and spines

```python
plt.rcParams['axes.spines.right'] = False
plt.rcParams['axes.spines.top'] = False
plt.rcParams['axes.linewidth'] = 1.5
```

- Top and right spines: **always off**.
- Left and bottom spines: 1.5–2.0 pt linewidth.
- No gridlines by default. Use sparse `set_yticks` to guide the eye.
- Y-limits tightened to data range — never use 0–100 when all values sit in 80–95.

```python
def tighten_ylimits(ax, data, margin=0.1, ymin=None):
    """Tighten y-axis to data range instead of using a fixed 0-max."""
    arr = np.asarray(data, dtype=float)
    dmin, dmax = float(np.nanmin(arr)), float(np.nanmax(arr))
    span = dmax - dmin if dmax != dmin else abs(dmax) * 0.1 or 1.0
    pad = span * margin
    bottom = ymin if ymin is not None else dmin - pad
    ax.set_ylim(bottom, dmax + pad)
```

### 4.3 Legend conventions

Legends are the reader's first stop when decoding a figure. A poorly placed or
inconsistent legend forces the reader to mentally map colors back to series —
worse, a missing legend makes the figure unreadable. Follow these rules for
every figure.

#### 4.3.1 Global rules

| Rule | Value | Rationale |
|------|-------|-----------|
| Frame | `frameon=False` — always | Frames add visual noise; the legend should blend into the figure |
| Font size | 7–8 pt (publication), 12–14 pt (poster) | Match tick label size; never larger than axis labels |
| Marker in legend | Show the same marker as the plot (`marker='o'` → legend shows `o`) | Reader must match legend to data without guessing |
| Handle length | `handlelength=1.5` for lines, `handlelength=0` for markers-only | Shorter handles save horizontal space |
| Spacing | `handletextpad=0.4`, `labelspacing=0.3`, `borderpad=0` | Tight but not cramped |
| Edge color | No edge on legend handles unless bars have edgecolor | Consistent with plot style |

```python
# Standard legend call for most plots
ax.legend(loc='best', frameon=False, fontsize=8,
          handlelength=1.5, handletextpad=0.4, labelspacing=0.3)
```

#### 4.3.2 Position by chart type

Choose legend position based on where data is **not** — never default to
`loc='best'` for the final figure; pick an explicit corner.

| Chart type | Preferred position | Alternative | When to move outside |
|------------|-------------------|-------------|---------------------|
| Line / trend (data in lower-left) | `upper right` | `upper center` | >4 series |
| Line / trend (data in lower-right) | `upper left` | `upper center` | >4 series |
| Bar chart (vertical) | `upper left` or `upper right` | Below plot (outside) | >5 groups |
| Bar chart (horizontal) | `lower right` | Right of plot (outside) | >5 groups |
| Scatter / bubble | Corner opposite to data cluster | Outside plot | Dense data |
| Heatmap | Right of colorbar | Below plot | Categorical legend |
| Radar / polar | Below plot (outside) | `upper right` in data space | >6 axes |
| XRD / FTIR overlay | `upper right` | `upper left` | >3 patterns |
| Stacked area | `upper right` | Below plot | >5 layers |
| Weibull / log-log | `upper left` | `lower right` | — |
| Dosage window (dual-axis) | `upper left` | Combined legend below | — |
| Mechanism schematic | No legend (use direct labels) | — | — |

#### 4.3.3 Outside-plot legend

When the legend is too large for the plot area, place it outside:

```python
# Below the plot (horizontal layout)
ax.legend(loc='upper center', bbox_to_anchor=(0.5, -0.15),
          ncol=3, frameon=False, fontsize=8, columnspacing=1.0)

# Right of the plot (vertical layout)
ax.legend(loc='center left', bbox_to_anchor=(1.02, 0.5),
          frameon=False, fontsize=8)

# Dedicated legend axis (for multi-panel figures)
ax_legend = fig.add_subplot(gs[legend_slot])
ax_legend.set_axis_off()
ax_legend.legend(handles, labels, loc='center', frameon=False, fontsize=8)
```

**Rules for outside legends**:
- Horizontal (`ncol>1`) when placing below — saves vertical space.
- Always use `bbox_to_anchor` with explicit coordinates.
- Add `bbox_extra_artists` to `savefig` to prevent clipping:
  ```python
  leg = ax.get_legend()
  fig.savefig('figure.svg', bbox_inches='tight',
              bbox_extra_artists=[leg] if leg else [])
  ```

#### 4.3.4 Sort order

Legend entries must follow a logical order, not the order `plot()` was called.

| Context | Sort rule | Example |
|---------|-----------|---------|
| Dosage series | Ascending by value | 5%, 10%, 15%, 20% |
| Temperature series | Ascending | 25°C, 100°C, 200°C, 400°C |
| Time series | Chronological | Day 0, Day 7, Day 28, Day 90 |
| Control vs modified | Control first | Reference, Modified A, Modified B |
| Performance ranking | Descending by key metric | Best, Second, Third |
| Phase comparison | By 2θ position (XRD) or wavenumber (FTIR) | Low-angle peaks first |
| Mechanism steps | Causal order | Step 1 → Step 2 → Step 3 |

```python
# Explicit order — do not rely on plot() call order
handles, labels = ax.get_legend_handles_labels()
order = [2, 0, 1]  # reorder: third series first, then first, then second
ax.legend([handles[i] for i in order], [labels[i] for i in order],
          frameon=False, fontsize=8)
```

#### 4.3.5 Symbol conventions

The legend handle must match the plot element exactly:

| Plot element | Legend handle | Code |
|-------------|---------------|------|
| Line + marker | Line with marker | `ax.plot(..., marker='o', label='Sample')` |
| Marker only (scatter) | Marker only | `ax.scatter(..., label='Sample')` |
| Bar | Filled rectangle | `ax.bar(..., label='Group')` |
| Filled area | Filled polygon | `ax.fill_between(..., label='Band')` |
| Dashed line | Dashed line | `ax.plot(..., linestyle='--', label='Fit')` |
| Error bar | Line + cap | Use `Plot2D` errorbar legend handler |
| Stacked bar | Filled rectangle (single color) | `ax.bar(..., label='Component')` |

**Stacked bar legend rule**: Legend order must match stack order (bottom to top).
Use `reversed()` if matplotlib auto-reverses:
```python
handles, labels = ax.get_legend_handles_labels()
ax.legend(reversed(handles), reversed(labels), loc='upper right', frameon=False)
```

#### 4.3.6 Dual-axis combined legend

When a figure has two y-axes, merge both axes' handles into one legend:

```python
lines1, labels1 = ax1.get_legend_handles_labels()
lines2, labels2 = ax2.get_legend_handles_labels()
ax1.legend(lines1 + lines2, labels1 + labels2,
           loc='upper left', frameon=False, fontsize=8)
```

**Color-code axis labels** to match their data series — this reduces dependence
on the legend:
```python
ax1.set_ylabel('Viscosity (mPa·s)', color=color_visc)
ax2.set_ylabel('Bond strength (MPa)', color=color_bond)
ax1.tick_params(axis='y', labelcolor=color_visc)
ax2.tick_params(axis='y', labelcolor=color_bond)
```

#### 4.3.7 Certainty-tier legend

For evidence heatmaps and mechanism maps, use a certainty legend to distinguish
evidence quality:

| Symbol | Meaning | Color | When |
|--------|---------|-------|------|
| ✓ or ● | Direct evidence | Forest green `#4F7C6A` | Measured by characterization |
| ~ or ◐ | Indirect / consistent with | Amber `#D4A574` | Inferred from related data |
| ✗ or ○ | Not observed / absent | Grey `#8C8C8C` | Searched but not found |
| ? or ⊘ | Not searched | Light grey `#C0C0C0` | Outside scope of this study |

```python
certainty_handles = [
    plt.Line2D([0], [0], marker='o', color='w', markerfacecolor='#4F7C6A',
               markersize=10, label='Direct evidence'),
    plt.Line2D([0], [0], marker='o', color='w', markerfacecolor='#D4A574',
               markersize=10, label='Indirect / consistent with'),
    plt.Line2D([0], [0], marker='o', color='w', markerfacecolor='#8C8C8C',
               markersize=10, label='Not observed'),
    plt.Line2D([0], [0], marker='o', color='w', markerfacecolor='#C0C0C0',
               markersize=10, label='Not searched'),
]
ax.legend(handles=certainty_handles, loc='upper right', frameon=False, fontsize=8)
```

#### 4.3.8 Direct labels vs legend

Prefer **direct labels** over legends when there are ≤5 series and the lines
do not cross at the label position:

```python
# Instead of a legend, label lines directly
for line, label in zip(lines, ['Control', '5% epoxy', '10% epoxy', '15% epoxy']):
    ax.annotate(label, xy=(line.get_xdata()[-1], line.get_ydata()[-1]),
                xytext=(5, 0), textcoords='offset points',
                fontsize=8, va='center', color=line.get_color())
```

**When to use a legend**:
- >5 series
- Series cross each other (direct labels would overlap)
- The figure is dense (multi-panel) and direct labels would clutter

**When to use direct labels**:
- ≤5 series that don't cross
- The reader needs to trace individual lines across panels
- Space is tight (small single-column figures)

#### 4.3.9 Colorblind-safe legend design

- Never rely on color alone in the legend — pair with marker shapes or line
  styles when possible.
- Test: print the legend in grayscale. If two entries look identical, add
  shape/linestyle differentiation.
- Use these marker pairs for 2–4 series:
  - 2 series: `o` + `s`
  - 3 series: `o` + `s` + `^`
  - 4 series: `o` + `s` + `^` + `D`
- For >4 series, use linestyle as secondary channel:
  - Solid, dashed, dotted, dashdot

#### 4.3.10 Legend QA checklist

Before finalizing any figure:

- [ ] `frameon=False` on all legends.
- [ ] Legend font size matches tick label size (7–8 pt).
- [ ] Legend position is explicit (not `loc='best'` in final version).
- [ ] Legend does not obscure data — if it does, move outside or use direct labels.
- [ ] Legend entries follow logical sort order (ascending dosage/temp/time).
- [ ] Legend handles match plot elements (marker, linestyle, fill).
- [ ] Stacked bar legend order matches stack order (bottom to top).
- [ ] Dual-axis figures have a single combined legend.
- [ ] Colorblind test passed: all entries distinguishable in grayscale.
- [ ] Direct labels used where feasible (≤5 non-crossing series).

### 4.4 GridSpec patterns

#### Standard 2×2

```python
fig = plt.figure(figsize=(10, 8))
gs = fig.add_gridspec(2, 2, hspace=0.35, wspace=0.3)
ax_a = fig.add_subplot(gs[0, 0])
ax_b = fig.add_subplot(gs[0, 1])
ax_c = fig.add_subplot(gs[1, 0])
ax_d = fig.add_subplot(gs[1, 1])
```

#### Full-width header + 3 panels

```python
fig = plt.figure(figsize=(14, 10))
gs = fig.add_gridspec(2, 3, hspace=0.35, wspace=0.3,
                      height_ratios=[1.2, 1])
ax_header = fig.add_subplot(gs[0, :])   # spans all 3 columns
ax_1 = fig.add_subplot(gs[1, 0])
ax_2 = fig.add_subplot(gs[1, 1])
ax_3 = fig.add_subplot(gs[1, 2])
```

#### Sidebar legend + main plot

```python
fig = plt.figure(figsize=(12, 5))
gs = fig.add_gridspec(1, 2, width_ratios=[4, 1], wspace=0.05)
ax_main = fig.add_subplot(gs[0])
ax_legend = fig.add_subplot(gs[1])
ax_legend.set_axis_off()
# Place legend in ax_legend
```

### 4.5 Multi-panel information hierarchy and architecture

Each panel in a multi-panel figure must answer a **different** scientific
question. Covering any one panel should leave a gap that cannot be recovered
from the others.

#### Three-level progressive complexity

| Level | Question | Encoding |
|---|---|---|
| 1. Overview | "What is the overall trend?" | Grouped bar, composition |
| 2. Deviation | "What is different per group?" | Z-score heatmap, diverging cmap |
| 3. Relationship | "How do variables co-vary?" | Scatter, bubble plot |

#### Common redundancy traps

| Trap | Example | Fix |
|---|---|---|
| Absolute + absolute | Stacked bar (%) + heatmap of same % | Replace heatmap with z-score deviation |
| Subset of parent | Ranked bar of one column from a stacked bar | Swap for scatter: variable A vs variable B |
| Two rankings | Two ranked bars on related metrics | Replace one with bubble scatter |
| Different chart, same data | Pie + stacked bar of same data | Merge or replace with relationship plot |

#### Anti-redundancy checklist

- [ ] Each panel answers a different question.
- [ ] No panel is a subset of another.
- [ ] If two panels show the same trend from different angles, merge or replace one.
- [ ] Color assignments are consistent across panels.
- [ ] Panel labels (a, b, c) are present, bold, lowercase.

---

## 5. In-Cell / In-Bar Text Contrast

When annotating values inside colored bars or heatmap cells, text must be
readable against the background:

```python
def luminance_text_color(hex_color):
    """Return 'white' or '#333333' based on background luminance."""
    c = hex_color.lstrip('#')
    r, g, b = int(c[0:2], 16) / 255, int(c[2:4], 16) / 255, int(c[4:6], 16) / 255
    luminance = 0.299 * r + 0.587 * g + 0.114 * b
    return 'white' if luminance < 0.5 else '#333333'
```

**Rule**: If the bar/cell color luminance < 0.5, use white text; otherwise use
dark text (`#333333`). Never use mid-grey — it fails on both light and dark
backgrounds.

---

## 6. Materials-Specific Visual Patterns

### 6.1 Dosage / optimization curves

When plotting property vs. dosage (e.g., epoxy content, fiber fraction):

- Mark the **optimum region** with a vertical shaded band or arrow.
- Do **not** call one point "optimal" unless durability and cost are also tested.
- Use `fill_between` for uncertainty bands, not just error bars.

### 6.2 SEM / microscopy image panels

- Always include a **scale bar** with explicit length (e.g., 10 μm, 50 μm).
- State magnification in the caption.
- Use consistent brightness/contrast across panels — do not enhance one panel
  more than another.
- For morphology comparison: use identical scale bars across all panels.
- Label phases, pores, cracks, or interfaces with arrows or annotations.

### 6.3 FTIR / XRD overlay plots

- Invert X-axis for FTIR (wavenumber decreases left to right is convention).
- Offset stacked XRD patterns vertically for clarity (use `offset` parameter).
- Annotate key peaks with wavenumber or 2θ value.
- Do not claim mechanism from FTIR alone — note "consistent with" rather than
  "confirms."

### 6.4 Durability retention plots

- Always show **both** the retention ratio AND the original absolute value.
- A material with 95% retention of 2 MPa is worse than 80% retention of 10 MPa.
- Use grouped bars: one group for absolute values, one for retention %.

### 6.5 Mechanism schematics

- Use **solid arrows** for direct evidence, **dashed arrows** for inferred steps.
- Color-code by evidence tier: green = measured, orange = inferred, grey = speculative.
- Do not draw causal loops without mechanistic evidence.
- Label each step with the characterization technique that supports it.

### 6.6 Evidence heatmaps (review figures)

- Rows = claims or mechanisms
- Columns = evidence layers (FTIR, SEM, XRD, mechanical, durability, field)
- Cell values: ✓ (direct), ~ (indirect), ✗ (absent), ? (not searched)
- Do not treat empty cells as "no evidence" — distinguish from "not searched."

---

## 7. Export Policy

### 7.1 Primary output

- **SVG** with `bbox_inches='tight'` — primary vector output.
- Text stays as editable `<text>` nodes (requires `svg.fonttype='none'`).

### 7.2 Raster preview

- **PNG** at 300 dpi for review and web display.

### 7.3 Submission formats

| Publisher | Preferred format | Resolution | Width |
|---|---|---|---|
| Elsevier (CBM, CCC, Fuel, JCP) | TIFF, EPS, PDF | 300 dpi photos, 600 dpi combination, 1000 dpi line art | 85–90 mm single, 170–180 mm double |
| Taylor & Francis (RMPD, IJPE) | EPS, TIFF, PDF | ≥300 dpi | 82 mm single, 169 mm double |
| ASCE (JMCE) | TIFF, EPS, PDF | Per ASCE guide | Per template |
| Springer (JBE, JRE) | TIFF, EPS, PDF | ≥300 dpi | Per template |
| Wiley (JACERS) | TIFF, EPS, PDF | ≥300 dpi | Per template |

### 7.4 Post-export

- Always `plt.close(fig)` after save to free memory.
- Keep source data CSV alongside the figure.
- Keep the plotting script or notebook.
- Keep caption draft with test standard, replicate count, and statistics.

---

## 8. Figure QA Checklist

Before marking a figure as publication-ready:

### Technical

- [ ] `svg.fonttype = 'none'` is set.
- [ ] Font stack: Arial → DejaVu Sans → Liberation Sans.
- [ ] Text is editable in Illustrator/Inkscape (open SVG and check).
- [ ] All axis labels, tick labels, and legend text are legible at final print size.
- [ ] No top/right spines. Bottom/left spines are visible (1.5–2 pt).

### Color

- [ ] Color assignments are consistent across all panels.
- [ ] No rainbow colormaps (`jet`, `rainbow`, `hsv`).
- [ ] Colorblind-safe: no red-green-only contrast.
- [ ] Grayscale test passed: all groups distinguishable without color.

### Layout

- [ ] Panel labels (a, b, c) are present, bold, lowercase.
- [ ] Legend has no frame (`frameon=False`).
- [ ] Y-limits are tightened to data range.
- [ ] Each panel answers a different question (anti-redundancy passed).
- [ ] Figure size matches the target journal's column width.

### Evidence

- [ ] Error bars or confidence intervals are present where applicable.
- [ ] Replicate count (n) is stated in caption or axis.
- [ ] Statistical annotations (p-values, significance letters) are included if relevant.
- [ ] Scale bars are present on all microscopy images.
- [ ] Figure caption describes the conclusion, not just the axis labels.
- [ ] Source data is accessible (CSV or table in supplement).

### Materials-specific

- [ ] Dosage curves do not claim "optimal" without durability data.
- [ ] FTIR/XRD claims use "consistent with" not "confirms."
- [ ] Retention plots show both ratio and absolute values.
- [ ] Mechanism schematics distinguish measured vs. inferred steps.
- [ ] SEM images have consistent brightness/contrast across panels.
