# Figure And Table Assets

Open this reference when selecting figures as evidence, extracting and
preparing assets, and running the figure-crop self-check.

## Select Figures As Evidence

Inspect the source for graphical abstracts, study design diagrams, central
result figures, microscopy panels, spectra, diffraction patterns, performance
curves, thermal analysis, calibration results, process diagrams, key tables,
validation figures, and control figures.

Prioritize figures that carry the paper's argument:

1. design/workflow,
2. main evidence,
3. validation or robustness,
4. mechanism/model/synthesis,
5. practical or conceptual implication.

Prefer a few readable key panels over many unreadable full figures.

## Extract And Prepare Assets

When the source contains usable figures:

- extract original images from the source package when possible,
- render high-resolution page images only for selected pages,
- crop relevant panels when full figures are too dense,
- keep original data visuals unchanged,
- save images under `output/assets/figures/`,
- use clear filenames such as `fig1_workflow.png` or `fig2b_main_result.png`,
- record source page, figure number, panel, crop status, and intended slide in
  `asset_manifest.json`.

For a standard 10-14 slide deck, usually select 4-8 figure/table assets. Add
more only when they support distinct evidence slides.

If extraction fails, use the best available fallback:

- rendered page screenshot with careful crop,
- recreated table only when values are explicitly available,
- clearly labeled placeholder only when the visual is unavailable.

## Figure Crop Self-Check

Before building the final HTML deck, create a contact sheet or inspect selected
crops directly.

Check every selected figure/table asset for:

- clipped titles, axis labels, legends, panel letters, or source labels,
- irrelevant surrounding paper text or captions included in the crop,
- too little margin around the crop,
- unreadable small text after planned slide scaling,
- dense multi-panel figures that should be split or cropped,
- low-resolution or blurry rendering.

Revise the crop before placing it in HTML when any scientific context is cut
off.
