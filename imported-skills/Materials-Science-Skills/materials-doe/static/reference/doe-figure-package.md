# DOE Figure Package

## Purpose

Generate publication-ready figures for design-of-experiments results: main effects plots, interaction plots, contour/surface plots, and residual diagnostics.

## Required Figures

| Figure | When | Tool |
|--------|------|------|
| Main effects plot | Always | `experiment_plot.py` |
| Interaction plot | When interaction terms are significant | `experiment_plot.py` |
| Contour / surface plot | RSM or mixture designs | `experiment_plot.py` |
| Residual diagnostics | Always | `experiment_plot.py` |

## Conventions

- Use consistent factor colours across all figures.
- Label axes with factor name and unit; annotate optimal region on contour plots.
- Export at 300 dpi, single-column width (85 mm) unless the journal allows double-column.
- Include a caption block that references the matrix run number.

## Handoff Fields

| Field | Description |
|-------|-------------|
| `figure_path` | Relative path to generated figure |
| `figure_type` | main-effects / interaction / contour / residual |
| `matrix_run` | Associated run number from the test matrix |
