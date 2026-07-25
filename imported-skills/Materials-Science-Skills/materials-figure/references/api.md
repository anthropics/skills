# API Reference — Materials Figure Making

Conventions, constants, and reusable code blocks for materials-science figure production. Implement in your script or adapt as needed.

---

## Constants

### PALETTE_MATERIALS

Materials-domain semantic color palette. Use when color carries material-system meaning (asphalt, cement, ceramics, metals, polymers).

```python
PALETTE_MATERIALS = {
    # Material-system semantic colors
    "asphalt_dark":    "#3A3A3A",   # dark gray for asphalt/binder
    "asphalt_light":   "#7A7A7A",   # light gray for aged asphalt
    "cement_gray":     "#B8B8B8",   # cement/concrete
    "ceramics_orange": "#D48A5C",   # warm orange for ceramics
    "ceramics_red":    "#B64342",   # strong red for ceramic emphasis
    "metals_blue":     "#4A7BA6",   # cool blue for metals
    "metals_silver":   "#A8A8B0",   # silver/steel gray
    "polymers_green":  "#5B9A5B",   # green for polymers
    "polymers_teal":   "#42949E",   # teal for polymer composites
    
    # Evidence-level semantic colors
    "measured":        "#2E6DA4",   # measured data (primary blue)
    "inferred":        "#8B8B8B",   # inferred/indirect evidence
    "literature":      "#C49A6C",   # literature values
    
    # Performance delta colors
    "improvement":     "#2E9E44",   # green for improvement
    "degradation":     "#E53935",   # red for degradation
    "neutral":         "#767676",   # gray for no change
    
    # Characterization technique colors
    "xrd_blue":        "#3775BA",   # XRD patterns
    "ftir_red":        "#B64342",   # FTIR spectra
    "sem_gray":        "#4D4D4D",   # SEM/TEM images
    "thermal_orange":  "#E07C3E",   # TGA/DSC curves
    
    # Neutrals
    "neutral_light":   "#CFCECE",
    "neutral_mid":     "#767676",
    "neutral_dark":    "#4D4D4D",
    "neutral_black":   "#272727",
    
    # Accent colors
    "gold":            "#FFD700",
    "teal":            "#42949E",
    "violet":          "#9A4D8E",
}

DEFAULT_COLORS_MATERIALS = [
    PALETTE_MATERIALS["measured"],
    PALETTE_MATERIALS["ceramics_orange"],
    PALETTE_MATERIALS["polymers_green"],
    PALETTE_MATERIALS["metals_blue"],
    PALETTE_MATERIALS["thermal_orange"],
    PALETTE_MATERIALS["neutral_light"],
]
```

Use `DEFAULT_COLORS_MATERIALS` when comparing material systems or characterization techniques. Reserve green/red for **performance delta** (improvement/degradation), not primary series identity.

### PALETTE_CHARACTERIZATION

Specialized palette for multi-technique characterization panels:

```python
PALETTE_CHARACTERIZATION = {
    "xrd_primary":   "#3775BA",
    "xrd_secondary": "#7AA6D4",
    "ftir_primary":  "#B64342",
    "ftir_secondary":"#E09A9A",
    "sem_primary":   "#4D4D4D",
    "sem_secondary": "#8B8B8B",
    "thermal_primary":   "#E07C3E",
    "thermal_secondary": "#F0B87C",
    "rheology":      "#9A4D8E",
    "fluorescence":  "#2E9E44",
}
```

### PALETTE_PERFORMANCE

Palette for performance comparison figures:

```python
PALETTE_PERFORMANCE = {
    "baseline":      "#767676",   # baseline/reference
    "optimized":     "#2E6DA4",   # optimized material
    "improvement":   "#2E9E44",   # improvement marker
    "degradation":   "#E53935",   # degradation marker
    "target":        "#FFD700",   # target/specification line
    "uncertainty":   "#CFCECE",   # uncertainty band
}
```

---

## MANDATORY font + SVG rules (always first, no exceptions)

These three lines are **non-negotiable** and must appear at the top of every script, before any figure is created. They guarantee editable text in SVG output:

```python
plt.rcParams['font.family'] = 'sans-serif'
plt.rcParams['font.sans-serif'] = ['Arial', 'DejaVu Sans', 'Liberation Sans']
plt.rcParams['svg.fonttype'] = 'none'   # keeps text as <text> nodes, not paths
```

**Why `svg.fonttype = 'none'`**: matplotlib's default (`'path'`) converts every glyph to a bezier path, making text unselectable, unsearchable, and impossible to re-align in Illustrator / Inkscape. With `'none'`, text stays as SVG `<text>` elements and font substitution happens at render time.

**Output format**: always save as `.svg` (primary). PNG/PDF are optional secondary exports. Never use `.png` alone when the figure contains text that may need adjustment.

---

## apply_publication_style()

```python
def apply_publication_style(font_size=16, axes_linewidth=2.5, use_tex=False):
    """Apply materials-science publication-style rcParams. Call once before creating any figures."""
    # ── MANDATORY: editable SVG text ──────────────────────────────────────────
    plt.rcParams['font.family'] = 'sans-serif'
    plt.rcParams['font.sans-serif'] = ['Arial', 'DejaVu Sans', 'Liberation Sans']
    plt.rcParams['svg.fonttype'] = 'none'
    # ── Layout & style ────────────────────────────────────────────────────────
    plt.rcParams['font.size'] = font_size
    plt.rcParams['axes.spines.right'] = False
    plt.rcParams['axes.spines.top'] = False
    plt.rcParams['axes.linewidth'] = axes_linewidth
    plt.rcParams['legend.frameon'] = False
    if use_tex:
        plt.rcParams['text.usetex'] = True
```

**Presets:**
- Large multi-panel figures: `apply_publication_style(font_size=24, axes_linewidth=3)`
- Compact single figures: `apply_publication_style(font_size=15, axes_linewidth=2)`
- Dense journal-width multi-panels: `apply_publication_style(font_size=8, axes_linewidth=1)`
- LaTeX labels: `apply_publication_style(use_tex=True)`

---

## is_dark(hex_color, threshold=128)

```python
def is_dark(hex_color, threshold=128):
    """Return True if hex color is dark (use white text on it)."""
    c = hex_color.lstrip('#')
    r, g, b = int(c[0:2], 16), int(c[2:4], 16), int(c[4:6], 16)
    return (0.299*r + 0.587*g + 0.114*b) < threshold
```

---

## add_panel_label(ax, label, ...)

```python
def add_panel_label(ax, label, x=-0.06, y=1.02, fontsize=14,
                    color='black', fontweight='bold'):
    """Place a Nature-style panel label near the top-left edge."""
    ax.text(
        x, y, label,
        transform=ax.transAxes,
        fontsize=fontsize,
        fontweight=fontweight,
        color=color,
        ha='left',
        va='bottom',
    )
```

For dark image plates (SEM/TEM), move the label inside the panel and switch to white:
`add_panel_label(ax, 'a', x=0.01, y=0.98, color='white')`

---

## style_dark_image_ax(ax, ...)

```python
def style_dark_image_ax(ax, facecolor='black'):
    """Prepare an axes for microscopy / rendering plates."""
    ax.set_facecolor(facecolor)
    ax.set_xticks([])
    ax.set_yticks([])
    for spine in ax.spines.values():
        spine.set_visible(False)
    return ax
```

---

## make_xrd_overlay(ax, patterns, labels, ...)

```python
def make_xrd_overlay(ax, patterns, labels, colors=None,
                     two_theta_range=None, normalize=True,
                     ylabel='Intensity (a.u.)', xlabel='2θ (°)'):
    """
    XRD pattern overlay plot.

    Parameters
    ----------
    ax         : matplotlib Axes
    patterns   : list[dict] — each dict has 'two_theta' and 'intensity' arrays
    labels     : list[str] — legend label per pattern
    colors     : list[str] | None — defaults to PALETTE_CHARACTERIZATION XRD colors
    two_theta_range : tuple | None — (min, max) 2θ to display
    normalize  : bool — normalize each pattern to max=1.0
    ylabel     : str
    xlabel     : str

    Returns
    -------
    list[Line2D]
    """
    import numpy as np
    if colors is None:
        colors = [PALETTE_CHARACTERIZATION['xrd_primary'],
                  PALETTE_CHARACTERIZATION['xrd_secondary']]
    
    lines = []
    for i, (pattern, label) in enumerate(zip(patterns, labels)):
        two_theta = np.array(pattern['two_theta'])
        intensity = np.array(pattern['intensity'])
        
        if normalize:
            intensity = intensity / intensity.max()
        
        if two_theta_range:
            mask = (two_theta >= two_theta_range[0]) & (two_theta <= two_theta_range[1])
            two_theta = two_theta[mask]
            intensity = intensity[mask]
        
        color = colors[i % len(colors)]
        line, = ax.plot(two_theta, intensity, color=color, lw=1.5, label=label)
        lines.append(line)
    
    ax.set_xlabel(xlabel)
    ax.set_ylabel(ylabel)
    ax.legend()
    return lines
```

---

## make_ftir_overlay(ax, spectra, labels, ...)

```python
def make_ftir_overlay(ax, spectra, labels, colors=None,
                      wavenumber_range=None, normalize=True,
                      ylabel='Absorbance (a.u.)', xlabel='Wavenumber (cm⁻¹)'):
    """
    FTIR spectrum overlay plot.

    Parameters
    ----------
    ax         : matplotlib Axes
    spectra    : list[dict] — each dict has 'wavenumber' and 'absorbance' arrays
    labels     : list[str] — legend label per spectrum
    colors     : list[str] | None — defaults to PALETTE_CHARACTERIZATION FTIR colors
    wavenumber_range : tuple | None — (min, max) wavenumber to display
    normalize  : bool — normalize each spectrum to max=1.0
    ylabel     : str
    xlabel     : str

    Returns
    -------
    list[Line2D]
    """
    import numpy as np
    if colors is None:
        colors = [PALETTE_CHARACTERIZATION['ftir_primary'],
                  PALETTE_CHARACTERIZATION['ftir_secondary']]
    
    lines = []
    for i, (spectrum, label) in enumerate(zip(spectra, labels)):
        wavenumber = np.array(spectrum['wavenumber'])
        absorbance = np.array(spectrum['absorbance'])
        
        if normalize:
            absorbance = absorbance / absorbance.max()
        
        if wavenumber_range:
            mask = (wavenumber >= wavenumber_range[0]) & (wavenumber <= wavenumber_range[1])
            wavenumber = wavenumber[mask]
            absorbance = absorbance[mask]
        
        color = colors[i % len(colors)]
        line, = ax.plot(wavenumber, absorbance, color=color, lw=1.5, label=label)
        lines.append(line)
    
    # FTIR x-axis is reversed (high wavenumber on left)
    ax.invert_xaxis()
    ax.set_xlabel(xlabel)
    ax.set_ylabel(ylabel)
    ax.legend()
    return lines
```

---

## make_performance_bar(ax, materials, properties, values, ...)

```python
def make_performance_bar(ax, materials, properties, values, errors=None,
                         colors=None, ylabel=None, xlabel=None,
                         annotate=False, bar_width=0.8):
    """
    Performance comparison bar chart for materials.

    Parameters
    ----------
    ax         : matplotlib Axes
    materials  : list[str] — material names (x-axis categories)
    properties : list[str] — property names (legend labels)
    values     : list[array] — one array per property (each length = len(materials))
    errors     : list[array] | None — error bars per property
    colors     : list[str] | None — defaults to DEFAULT_COLORS_MATERIALS
    ylabel     : str
    xlabel     : str
    annotate   : bool — print value above each bar
    bar_width  : float — total width for all bars in one category

    Returns
    -------
    list[BarContainer]
    """
    import numpy as np
    if colors is None:
        colors = DEFAULT_COLORS_MATERIALS
    
    n_properties = len(properties)
    n_materials = len(materials)
    w = bar_width / n_properties
    x = np.arange(n_materials)
    
    containers = []
    for i, (prop_vals, prop_name, color) in enumerate(zip(values, properties, colors)):
        offset = (i - (n_properties - 1) / 2) * w
        error_kw = None
        if errors is not None and i < len(errors):
            error_kw = {'yerr': errors[i], 'elinewidth': 2, 'capthick': 2, 'capsize': 6}
        
        bars = ax.bar(x + offset, prop_vals, width=w, label=prop_name,
                      color=color, edgecolor='black', linewidth=1.5,
                      **(error_kw or {}))
        containers.append(bars)
        
        if annotate:
            for bar, val in zip(bars, prop_vals):
                ax.text(bar.get_x() + bar.get_width() / 2,
                        bar.get_height() + 0.01,
                        f'{val:.2f}', ha='center', va='bottom', fontsize=10)
    
    ax.set_xticks(x)
    ax.set_xticklabels(materials)
    if ylabel:
        ax.set_ylabel(ylabel)
    if xlabel:
        ax.set_xlabel(xlabel)
    ax.legend()
    return containers
```

---

## make_mechanism_schematic(ax, components, connections, ...)

```python
def make_mechanism_schematic(ax, components, connections, layout='horizontal'):
    """
    Mechanism schematic with boxes and arrows.

    Parameters
    ----------
    ax         : matplotlib Axes
    components : list[dict] — each dict has 'label', 'position' (x, y), 'color'
    connections : list[dict] — each dict has 'from', 'to', 'label' (optional)
    layout     : str — 'horizontal' or 'vertical'

    Returns
    -------
    None
    """
    import matplotlib.patches as mpatches
    
    # Draw component boxes
    for comp in components:
        x, y = comp['position']
        label = comp['label']
        color = comp.get('color', PALETTE_MATERIALS['neutral_light'])
        
        rect = mpatches.FancyBboxPatch((x - 0.1, y - 0.05), 0.2, 0.1,
                                        boxstyle="round,pad=0.01",
                                        facecolor=color, edgecolor='black', linewidth=1.5)
        ax.add_patch(rect)
        ax.text(x, y, label, ha='center', va='center', fontsize=10, fontweight='bold')
    
    # Draw connections
    for conn in connections:
        from_comp = next(c for c in components if c['label'] == conn['from'])
        to_comp = next(c for c in components if c['label'] == conn['to'])
        
        x1, y1 = from_comp['position']
        x2, y2 = to_comp['position']
        
        ax.annotate('', xy=(x2 - 0.1, y2), xytext=(x1 + 0.1, y1),
                    arrowprops=dict(arrowstyle='->', lw=1.5, color='black'))
        
        if 'label' in conn:
            mid_x, mid_y = (x1 + x2) / 2, (y1 + y2) / 2
            ax.text(mid_x, mid_y + 0.02, conn['label'], ha='center', fontsize=8)
    
    ax.set_xlim(-0.2, 1.2)
    ax.set_ylim(-0.2, 0.8)
    ax.set_aspect('equal')
    ax.axis('off')
```

---

## make_evidence_heatmap(ax, matrix, techniques, mechanisms, ...)

```python
def make_evidence_heatmap(ax, matrix, techniques, mechanisms,
                          cmap='YlOrRd', cbar_label='Evidence strength',
                          annotate=True, fmt='{:.1f}'):
    """
    Review evidence heatmap: techniques × mechanisms.

    Parameters
    ----------
    ax         : matplotlib Axes
    matrix     : 2D array — evidence strength (rows=techniques, cols=mechanisms)
    techniques : list[str] — row labels
    mechanisms : list[str] — column labels
    cmap       : str — colormap name
    cbar_label : str
    annotate   : bool — show values in cells
    fmt        : str — value format string

    Returns
    -------
    None
    """
    import numpy as np
    import matplotlib as mpl
    
    im = ax.imshow(matrix, cmap=cmap, aspect='auto', vmin=0, vmax=matrix.max())
    cbar = ax.figure.colorbar(im, ax=ax)
    cbar.set_label(cbar_label)
    
    ax.set_xticks(range(len(mechanisms)))
    ax.set_xticklabels(mechanisms, rotation=30, ha='right')
    ax.set_yticks(range(len(techniques)))
    ax.set_yticklabels(techniques)
    
    if annotate:
        norm = mpl.colors.Normalize(vmin=matrix.min(), vmax=matrix.max())
        cm_obj = plt.get_cmap(cmap)
        for (i, j), val in np.ndenumerate(matrix):
            r, g, b, _ = cm_obj(norm(val))
            lum = 0.299*r + 0.587*g + 0.114*b
            color = 'white' if lum < 0.5 else 'black'
            ax.text(j, i, fmt.format(val), ha='center', va='center',
                    fontsize=10, color=color)
```

---

## finalize_figure(fig, out_path, ...)

```python
def finalize_figure(fig, out_path, formats=None, dpi=300,
                    pad=2, bbox_inches=None, close=True):
    """
    Apply tight_layout and save figure.

    Parameters
    ----------
    out_path : str   — path without extension, or with extension
    formats  : list  — e.g. ['png', 'pdf', 'svg']. If None, uses extension of out_path.
    dpi      : int   — 300 standard, 600 for dense bar panels
    pad      : float — tight_layout pad (2 default, 1 for compact multi-panel)
    """
    import os
    from pathlib import Path
    fig.tight_layout(pad=pad)
    base = Path(out_path)
    os.makedirs(base.parent, exist_ok=True)
    if formats is None:
        formats = [base.suffix.lstrip('.') or 'png']
        base = base.with_suffix('')
    saved = []
    for fmt in formats:
        p = str(base) + f'.{fmt}'
        kw = {}
        if bbox_inches is not None:
            kw['bbox_inches'] = bbox_inches
        fig.savefig(p, dpi=dpi, **kw)
        saved.append(p)
    if close:
        plt.close(fig)
    return saved
```

---

## Validation Rules

- `make_xrd_overlay`: each pattern dict must have 'two_theta' and 'intensity' keys with equal-length arrays.
- `make_ftir_overlay`: each spectrum dict must have 'wavenumber' and 'absorbance' keys with equal-length arrays.
- `make_performance_bar`: `len(materials)` must equal length of each array in `values`.
- `make_evidence_heatmap`: `matrix` must be 2D; `techniques` length = `matrix.shape[0]`; `mechanisms` length = `matrix.shape[1]`.
- `finalize_figure`: supported formats — `png`, `pdf`, `svg`, `eps`, `jpg`, `tif`.

---

## Conventions

- Save outputs under `./figures/` (or path given by user); `finalize_figure` creates parent dirs.
- In headless / batch runs, set non-interactive backend before importing pyplot:
  ```python
  import matplotlib
  matplotlib.use('Agg')
  import matplotlib.pyplot as plt
  ```
- Always `plt.close(fig)` after saving to free memory.
- For multi-panel figures, prefer one baseline family plus one hero family; reserve green/red for delta cues.
- When color roles, resolution, or layout are underspecified and would change the figure, confirm with user before finalizing.
- For materials-science figures, validate claims against `static/core/materials_kb.yaml` before plotting (see `references/materials-validation.md`).

---

## Related files

- [SKILL.md](../SKILL.md) — When to use this skill
- [common-patterns.md](common-patterns.md) — Reusable layout and encoding patterns
- [materials-validation.md](materials-validation.md) — Materials knowledge validation
- [figure-design-theory.md](figure-design-theory.md) — Rationale behind every pattern
- [tutorials.md](tutorials.md) — End-to-end walkthroughs
