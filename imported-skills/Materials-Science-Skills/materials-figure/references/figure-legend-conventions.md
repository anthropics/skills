# Figure legend conventions

A figure legend is the bridge between the visual and the manuscript. For
materials-science submissions (CBM, CCC, JBE, RMPD, JMCA, Advanced Materials,
Nature family), follow these conventions.

## 1. Header line

```
Fig. N | Title. Description. n = X, error = SD/SEM, p < 0.05 by ANOVA. Scale bar: 200 nm.
```

- Title: 8–14 words, ends with a period.
- Description: 1–3 sentences, evidence-grounded, no overclaim.
- `n` value: required when applicable.
- Scale bar: required for any microscopy panel.
- `Source Data 1` reference at the end if applicable.

## 2. Panel labels

- Lowercase bold letters: **a**, **b**, **c**, placed top-left, outside the axes.
- For dark image plates (SEM/TEM): move inside, white text.
- Never use (a), (b) — always bare letter.

## 3. Statistics in legend

- p-values: `p < 0.05`, `p < 0.01`, `p < 0.001`. Never `p = 0.05`.
- Error type: SD, SEM, or 95 % CI. State it once in the legend.
- Test name: one-time in the legend (e.g., `one-way ANOVA with Tukey HSD`).
- For n < 3: state this explicitly and avoid significance claims.

## 4. Color and symbol consistency

- The same variable carries the same color across all panels and figures.
- Use the `PALETTE_MATERIALS` constants from `references/api.md`.
- Reserve green/red for performance deltas (improvement/degradation).
- Use shape (circle, square, triangle) to disambiguate overlapping series.

## 5. Source data boilerplate

If a figure has raw data:

> Source data are available for this figure. Primary data are deposited
> at <DOI or repository>.

If a figure has been generated from a workflow:

> Plot generated with `materials-figure` skill, manifest version 2.0,
> validate_materials_claims.py exit 0.

## 6. Multi-panel layout

- Hero panel: top-left, largest, contains the main claim.
- Supporting panels: smaller, arranged clockwise from the hero.
- Shared axes: only when the units and ranges match exactly.
- Figure-strip (1×N): for trends, panels share y-axis only if appropriate.

## 7. Caption boundary

- Match the claim to the evidence type:
  - **Morphology** (SEM, TEM, AFM): claim "morphology consistent with..."
  - **Spectroscopy** (XRD, FTIR, Raman): claim "X-ray diffraction pattern is
    consistent with..."
  - **Performance**: claim "X % improvement at Y condition"
  - **Mechanism**: require ≥2 independent evidence types (e.g., XRD + FTIR +
    in-situ); otherwise use "consistent with the proposed mechanism"
- Use `validate_materials_claims.py` exit code as the QA gate.
