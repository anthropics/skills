# LLM-Driven Figure Creation

Use this reference when the user provides a CSV/TSV data table and asks for
plotting, visualization, paper figures, or figure creation.

In LLM-as-artist mode, the LLM writes plotting code directly based on the
validated contract and source data. The workflow is contract-first and
Python-only:

```text
source table -> contract draft/review -> contract validation
  -> materials validation when material entities are present -> LLM writes plot.py
  -> SVG/PNG export -> QA review
```

## Workflow

### 1. Draft the figure contract

Write `figure_contract.md` from the source table and the user's goal, filling
all eight required fields with substantive content:

- core conclusion,
- evidence chain,
- archetype,
- Python backend readiness,
- journal/export contract,
- statistics and image integrity,
- materials claim boundary,
- reviewer risks.

### 2. Validate the contract

Confirm or revise the draft with the user/LLM until every point holds real
content. Validation passes -> proceed. Validation fails -> stop and revise.

### 3. Conditional materials knowledge validation

If the figure contains materials-science entities (XRD peaks/phases, FTIR
wavenumbers/functional groups, performance values), load
`static/core/materials_kb.yaml` and run `scripts/validate_materials_claims.py`
before plotting. Figures without those entities may skip this stage. Errors
block plotting; warnings flag claims for review.

### 4. LLM writes plot.py

The LLM writes `plot.py` directly using matplotlib or other Python plotting
libraries, following the contract and source data.

### 5. Generate exports and documentation

The LLM generates exports (SVG, PNG, PDF, TIFF) and writes `caption.md`,
`qa_report.md`, and `asset_manifest.md`.

## Generated Package

```text
figure-package/
  figure_contract.md
  source_data.csv
  plot.py
  figure.svg
  figure.png
  figure.pdf
  figure.tiff
  caption.md
  qa_report.md
  asset_manifest.md
```

`figure.svg` is the editable manuscript asset. `figure.png` is the quick
preview. `plot.py` is self-contained and rerunnable from `source_data.csv`.

## Chart Selection Guidelines

- Numeric x + numeric y + SD/SE/CI/error column -> errorbar trend.
- Categorical group + numeric response -> grouped bar.
- Repeated group keys -> boxplot.
- Four or more numeric property columns -> correlation heatmap.
- Otherwise use scatter plot as an association plot.

These are conservative defaults. They protect the claim boundary more than they
optimize visual novelty.

## QA Report Contract

`qa_report.md` must include:

- `Status`
- `Figure Identity`
- `Data Check`
- `Chart Choice Check`
- `Scientific Claim Boundary`
- `Visual QA`
- `Reviewer Risk`
- `Final Recommendation`

The report must state whether replicate count, units, error bar definition,
missing values, and source-data anchors are present. Mechanism, field
durability, and statistical significance claims remain unsupported unless the
source data explicitly provide that evidence.

## Boundaries

The LLM-driven workflow is allowed to generate a figure from measured columns.
It is not allowed to invent missing replicate counts, statistical tests,
mechanism evidence, field durability, or image scale bars. When those are
absent, the QA report should mark them as reviewer risks instead of hiding
the weakness.
