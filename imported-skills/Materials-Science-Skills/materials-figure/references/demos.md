# End-to-end demos

Three worked examples that walk the full pipeline from user request to
journal-ready figure package. Each demo reuses an existing
`materials4papers/` example.

## Demo 1: Cement hydration XRD phase tracking

**Source:** `assets/materials4papers/cement_hydration_xrd/`

**Claim (one sentence):** Hydration of C₃S at 1, 7, 28 d shows progressive
consumption of alite peaks and growth of portlandite + C-S-H gel.

**Pipeline:**

1. **Read** `plot.py` and `data/synthetic.csv` to understand the input.
2. **Open** `static/core/contract.md` and write the eight-point contract:
   - Core conclusion: see above
   - Evidence chain: stacked area chart of phase fractions over time
   - Archetype: quantitative grid (3 stacked subplots)
   - Backend: Python only
   - Export: 300 dpi PNG + SVG, color-vision-safe
   - Statistics/image integrity: replicate count, error-bar definition, and image provenance
   - Claim boundary: phase evidence is not a complete mechanism claim
   - Reviewer risks: peak overlap, baseline correction, and incomplete phase matching
3. **Package** the demo in a working output directory with `source_data.csv`
   and `figure_contract.md`. The `materials4papers/` source directories are
   reference examples; they are not themselves complete validation packages.
4. **Validate** by running
   `python scripts/validate_materials_claims.py path/to/figure-package --kb static/core/materials_kb.yaml`.
   Fix errors before plotting; review any warnings.
5. **Plot** by adapting `plot.py` for the three time-points.
6. **QA** with `references/figure-legend-conventions.md`:
   - Panel labels **a, b, c** added.
   - Caption grounded in XRD evidence; no mechanism overclaim.
7. **Deliver** the figure package with `figure_contract.md`, `qa_report.md`,
   `caption.md`, `asset_manifest.md`, `source_data.csv`, `plot.py`, and
   locally generated figure exports.

## Demo 2: Composite fatigue S-N curves

**Source:** `assets/materials4papers/composite_fatigue_sn/`

**Claim:** CFRP shows a 2.5× higher endurance limit than GFRP at 10⁶ cycles
under tension-tension (R = 0.1) loading.

**Pipeline:**

1. **Read** `plot.py` and CSV (fatigue_cfrp.csv, fatigue_gfrp.csv).
2. **Contract** the eight required fields.
3. **Package and validate** with the KB engine after copying the relevant CSV
   into `source_data.csv` and writing `figure_contract.md`; CFRP and GFRP are
   polymers, and the endurance claim should not contradict the KB.
4. **Plot** with `apply_publication_style(font_size=15, axes_linewidth=2)`.
5. **QA** legend convention: panel label **a**, axes labels in SI,
   error bands = 95 % CI of log-N.
6. **Deliver** figure package.

## Demo 3: Ceramics Weibull reliability

**Source:** `assets/materials4papers/ceramics_weibull_reliability/`

**Claim:** Sintered ZrO₂ exhibits Weibull modulus m = 12.4, indicating
tight flaw population control.

**Pipeline:**

1. **Read** `plot.py` and the Weibull parameter CSV.
2. **Contract** including the Weibull fit as the hero panel and the
   probability plot as the supporting panel.
3. **Package and validate**: KB has ZrO2 sintered density range; measured
   density claims in `source_data.csv`/`figure_contract.md` should fall in
   `[5.5, 6.1]` g/cm³ ± 20 %.
4. **Plot** with `apply_publication_style(use_tex=False)` (text math via
   `matplotlib.mathtext`).
5. **QA**: caption says "m = 12.4 (95 % CI: 11.0, 14.1)", n = 30.
6. **Deliver** with the Weibull parameters written into `figure_contract.md`.

## Common mistakes to avoid

- Skipping the contract step ("just plot this CSV").
- Citing mechanism in the caption with only SEM evidence.
- Using raster-only PNG when SVG is required for editable text.
- Reporting m without n and CI.
- Using green for a non-delta series.
- Including a panel that does not carry a unique piece of evidence.
