# Figure QA Contract

Use this contract before sending a figure to a supervisor, co-author, or journal submission system.

## File and export

- DPI is at least 300 for raster images and higher for line art when rasterized.
- Vector output is retained for line charts, bar charts, radar charts, and schematics.
- Filenames identify the figure purpose, not only `Figure1`.

## Data and statistics

- Every error bars definition is stated as SD, SE, CI, or range.
- The replicate count is visible in caption or methods.
- Units are present in each axis label.
- Any normalized radar or retention figure has raw values available.
- **Source-Handoff Check**: every review-figure mark links to a reader handoff row, citation matrix row, source data row, or source_map anchor.
- **Certainty-Tier Check**: review figures label each visual claim as `measured`, `inferred`, `speculative`, or `missing`.
- **Missing-Evidence Marker Check**: absent tests, unreported durability/service data, and unsupported mechanism links use a visible missing marker instead of an empty or positive-looking cell.

## Image panels

- Every SEM, TEM, fluorescence, or optical panel has a scale bar.
- Contrast enhancement is applied consistently and documented.
- Representative images are not used as quantitative proof without repeated fields.

## Legend

- `frameon=False` on all legends.
- Legend font size matches tick label size (7–8 pt).
- Legend position is explicit (not `loc='best'` in final version).
- Legend does not obscure data — if it does, move outside or use direct labels.
- Legend entries follow logical sort order (ascending dosage/temp/time).
- Legend handles match plot elements (marker, linestyle, fill).
- Stacked bar legend order matches stack order (bottom to top).
- Dual-axis figures have a single combined legend.
- Colorblind test passed: all entries distinguishable in grayscale.
- Direct labels used where feasible (≤5 non-crossing series).
- **See [figure-design-theory.md §4.3](figure-design-theory.md) for full legend conventions.**

## Caption boundary

- The caption boundary states exactly what the figure supports.
- Mechanism claims link to at least two complementary evidence types when possible.
- Durability wording separates laboratory conditioning from field performance.
- **Caption-Boundary Check**: the caption names measured support, inferred interpretation, speculative schematic elements, and missing evidence without upgrading their strength.
