# 2026 Materials Science Figure Observations

This note captures page-level figure archetypes commonly observed in materials science papers (Nature Materials, Advanced Materials, Acta Materialia, Cement and Concrete Composites, etc.). Unlike the nature-2026-observations.md which cites specific DOIs, this file uses generalized archetypes distilled from common materials-paper patterns. Users should supplement with specific examples from their target journal.

## Archetype 1: Performance-ladder composite

Common in performance-breakthrough papers where a new formulation or process is benchmarked against prior baselines.

Actionable rules:

- Let the performance comparison panel (bar chart or trend line) occupy `50–60%` of figure height.
- Annotate numerical values directly on bars or lines; avoid forcing readers back to a separate table.
- Render control/baseline groups in neutral grey and reserve the brand accent color for the experimental group only.
- Keep the mechanism inset schematic simplified to line art so it does not compete with the data panel.
- Use one repeated accent style for callouts (e.g. a single dashed outline family) across the composite.

Recommended accent set:

```python
PERF_BLUE = "#1F77B4"
PERF_GREEN = "#2CA02C"
NEUTRAL_GREY = "#9E9E9E"
```

## Archetype 2: Characterization plate + quant overlay

Common in mechanism-elucidation papers where SEM/TEM/XRD plates carry the primary evidence.

Actionable rules:

- Use a black facecolor only for the image plate region, not the surrounding quant panels.
- Overlay quantitative curves (peak markers, intensity profiles) semi-transparently so the underlying image stays visible.
- Keep scale bars geometrically consistent across rows and columns; reuse one bar length per magnification tier.
- Place channel labels and panel labels directly on the plate; avoid detached legends.
- Pair grayscale image context with a single accent color for annotations.

Recommended accent set:

```python
PLATE_ACCENT = "#FF2AD4"
PLATE_GREY = "#B8B8B8"
PLATE_WHITE = "#FFFFFF"
```

## Archetype 3: Trade-off dual-axis figure

Common in trade-off resolution papers (strength vs. ductility, cost vs. performance, permeability vs. strength).

Actionable rules:

- Assign the left y-axis to performance A in a cool color and the right y-axis to performance B in a warm color.
- Mark the optimal balance point with a distinct marker plus an inline annotation.
- Show the full declining branch without axis truncation so the trade-off shape is honest.
- Shade an "acceptable window" region to communicate the design tolerance, not just the optimum.
- Color both axis labels to match their series so readers map line-to-axis without a legend.

Recommended accent set:

```python
COOL_BLUE = "#2176AE"
WARM_ORANGE = "#F57F17"
WINDOW_SHADE = "#FFF3CD"
```

## Archetype 4: Process-structure-property chain

Common in methodology and review papers that trace causality from processing to microstructure to property.

Actionable rules:

- Arrange panels left-to-right in semantic order: process -> structure -> property; do not grid them arbitrarily.
- Connect panels with arrows or flow glyphs rather than equal whitespace gutters.
- Title each panel with its chain stage name (e.g. "Sintering", "Grain size", "Hardness").
- Make the property panel the rightmost and the largest, since it is the payoff of the chain.
- Use a cool-to-warm gradient across the chain so color itself encodes progression.

Recommended accent set:

```python
CHAIN_COOL = "#3B8EBC"
CHAIN_MID = "#9DB4C9"
CHAIN_WARM = "#D96941"
```

## Archetype 5: Durability timeline composite

Common in aging, corrosion, freeze-thaw, and long-term performance studies.

Actionable rules:

- Use one shared time axis across all conditions; do not let each condition define its own x-range.
- Plot each condition as a line with a shaded confidence-interval band in the same hue at lower alpha.
- Draw the retention-rate threshold (e.g. 80%) as a horizontal dashed reference line spanning the full axis.
- Separate degradation stages with pale background color bands labeled at the top edge.
- Embed small mechanism-evidence insets (micrograph, spectra) at the stage transitions where behavior changes.

Recommended accent set (Okabe-Ito derived, color-blind safe):

```python
OK_BLUE = "#0072B2"
OK_ORANGE = "#E69F00"
OK_GREEN = "#009E73"
OK_PURPLE = "#CC79A7"
```

## Archetype 6: Multi-performance radar/heatmap summary

Common in review and systematic-comparison papers that summarize many formulations across many properties.

Actionable rules:

- On radar plots, push axis labels outward and stagger angles to prevent overlap at the perimeter.
- On heatmaps, use a diverging colormap (e.g. RdBu) centered at the neutral baseline so over- and under-performance read symmetrically.
- State the normalization method (min-max, z-score, reference-value ratio) in the figure caption, not just the methods section.
- Highlight the optimal formulation with a bold border or annotation rather than a saturated fill.
- Limit radar overlays to 3-4 series; beyond that, switch to a heatmap to preserve legibility.

Recommended accent set:

```python
DIVERGING_RED = "#B2182B"
DIVERGING_WHITE = "#F7F7F7"
DIVERGING_BLUE = "#2166AC"
HIGHLIGHT_BORDER = "#222222"
```

## Cross-cutting materials-paper rules

- Panel labels are small bold lowercase letters near the top-left corner, not large badges.
- Keep axis-heavy quantitative panels visually quieter than schematics or imaging plates.
- Reuse the same physical/material color mapping across all panels of a composite; do not switch palettes mid-figure.
- Scale bars, axis units, and sample sizes must be explicit; materials reviewers flag missing units aggressively.
- Saturated colors should mean either a highlighted subgroup or a true experimental channel, never decoration.

## What not to copy blindly

- Do not force every materials figure onto a black background; reserve black for imaging plates only.
- Do not import a bright multi-hue palette just because a comparison has many categories — prefer direct labels plus one accent.
- Do not truncate the declining branch of a trade-off or durability curve to make a result look cleaner.
- Do not omit the normalization method on radar/heatmap summaries; an unnormalized heatmap is unreadable.
