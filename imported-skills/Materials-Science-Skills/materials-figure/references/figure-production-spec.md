# Figure Production Specification

Use this reference before preparing final manuscript figures for CBM, CCC, Fuel, JCP, RMPD, IJPE, JBE, JRE, and related materials journals. Always verify the current official guide for authors before final submission.

## Universal Production Checklist

- Export line charts, bar charts, and schematics as vector PDF/EPS/SVG when accepted.
- Export SEM, TEM, fluorescence, and optical images as TIFF when possible.
- Keep final-size text readable: usually >= 6 pt for Elsevier and >= 8 pt for Taylor & Francis after scaling.
- Use consistent axis style: `Property (unit)` or `Property / unit`, not both.
- Define all error bars in the caption.
- Add scale bars to all microscopy images.
- Use subfigure labels `(a)`, `(b)`, `(c)` consistently.
- Avoid red/green-only contrasts; use colorblind-safe palettes.

## Publisher-Oriented Defaults

| Journal family | Typical format | Resolution | Width guidance | Font guidance |
|---|---|---|---|---|
| Elsevier materials journals: CBM, CCC, Fuel, JCP, RCR | TIFF, EPS, PDF | 300 dpi for photos, 600 dpi for combination art, 1000 dpi for line art when rasterized | single column about 85-90 mm; double column about 170-180 mm | Arial, Helvetica, Times; keep >= 6 pt after scaling |
| Taylor & Francis: RMPD, IJPE | EPS, TIFF, PDF | >= 300 dpi; higher for line art | single column about 82 mm; double column about 169 mm | Times New Roman or journal-safe serif/sans; keep >= 8 pt |
| ASCE: JMCE | TIFF, EPS, PDF | check current ASCE author guide | single/double column according to ASCE template | clear engineering axis labels and units |

## Data Figures vs. Image Figures

Data figures:

- Prefer vector output.
- Use raw points or error bars for small `n`.
- Keep gridlines light and non-dominant.
- Avoid 3D bars, shadows, and decorative gradients.

SEM/optical/fluorescence image figures:

- Use TIFF or high-quality PNG/TIFF source images.
- Do not stretch images non-uniformly.
- Preserve scale bars after panel assembly.
- State magnification or scale bar in caption.
- For multi-panel images, submit both assembled figure and original panels if requested.

## Materials Science Caption Formula

Use:

```text
Figure X. [What is shown] for [material/system] under [condition]. Error bars
represent [SD/SE/95% CI] (n = [x]). [One cautious interpretation]. [Boundary
if mechanism or durability is inferred.]
```

Example:

```text
Figure 4. Pull-off bond strength of waterborne epoxy modified emulsified
asphalt at different epoxy contents after 7 d curing. Error bars represent
SD (n = 3). The 15% epoxy group showed the highest mean strength under the
tested condition; field performance requires additional moisture and traffic
exposure validation.
```

## Export Handoff

For each final figure, keep:

- source data CSV.
- plotting script or software project file.
- final vector/raster export.
- caption draft.
- notes on test standard, replicate count, and statistics.
