# Figure Hard Workflow

> **Figure contract is a blocking gate.** The contract is written and validated
> before any plotting code, data generation, preview, or rendered figure. This
> overrides general autonomy/default-execution behavior for figure tasks.

> **Python runtime gate**: check Python and required plotting packages before
> rendering. If unavailable, stop and report the blocker.

Run this workflow for any journal-ready figure, review figure, plotted data
figure, or figure audit. The eight stages below are ordered; skip only a stage
explicitly marked as conditional.

## 1. Build and validate the multi-figure storyboard (conditional)

For a task spanning more than one figure, write `figure_storyboard.yaml` (see
`assets/templates/figure-storyboard/`) and run `check_storyboard.py` before
writing any individual figure contract. The storyboard gate verifies:

- narrative arc completeness and role coverage,
- acyclic evidence dependencies (DAG),
- cross-figure non-redundancy,
- style consistency declarations.

The storyboard must pass before individual figure contracts are written. For a
single-figure task, skip this stage and proceed to the figure contract.

## 2. Build and validate the figure contract

Before plotting, write or update `figure_contract.md` with substantive content
for all eight required fields:

- core conclusion,
- evidence chain,
- archetype,
- Python backend readiness,
- journal/export contract,
- statistics and image-integrity needs,
- materials claim boundary,
- reviewer risks.

Then validate `figure_contract.md` manually or with the applicable validation
tools.

- Validation passes -> proceed to stage 3.
- Validation fails -> stop. Revise the contract so every field holds real
  content. Do not generate plotting scripts, mock data, previews, or rendered
  figures while the contract is invalid.

The contract always precedes plotting code. This is binding for both interactive
figure work and the automatic table-plotting loop.

## 3. Validate materials-science claims (conditional)

If the figure contains XRD peaks/phases, FTIR wavenumbers/functional groups, or
performance values, load `static/core/materials_kb.yaml` and run
`validate_materials_claims.py` against the figure package before plotting.

- Errors that contradict known material relations block plotting.
- Values far outside typical ranges are warnings for review.
- Figures without materials-science entities skip this stage.

## 4. Load the Python backend

Load `static/fragments/backend/python.md` and follow its execution rules.
Before rendering, confirm Python and the packages required by the requested
figure family. Do not use an alternate plotting backend.

## 5. Check source data and anchors

Use actual source data, a table-system row, a `source_map.json` anchor, or PDF
visual asset metadata. If the user has no evidence yet, produce a plan or
template only and label the package `template-only`. If source anchors are
missing, update the contract's evidence chain before proceeding; do not plot
against an unanchored contract.

## 6. Create the figure

In LLM-as-artist mode, write plotting code directly from the validated contract
and source data:

```text
storyboard (if multi-figure) -> contract draft -> contract validation
  -> materials validation (if applicable) -> Python backend check
  -> source-anchor check -> plot.py -> exports
```

The LLM writes `plot.py` using matplotlib or other Python plotting libraries
that run under the Python backend, following the contract and source data.

Stop for human clarification only when the source table lacks numeric response
columns, the scientific claim cannot be inferred safely, or the QA report has
critical issues. Contract, storyboard, materials-validation, and source-anchor
failures are stop conditions; they never fall back to plotting.

## 7. Create the figure package

Use `references/figure-package-protocol.md` and
`assets/templates/figure-package/`. A production package should contain the
contract, source data, Python plotting script, SVG/PDF/PNG/TIFF exports,
caption, QA report, and asset manifest.

## 8. Run visual QA and return the package

Apply `references/figure-qa-contract.md`. Check export formats, final size,
text readability, color choices, units, `n`/error bars/statistics, image scale
bars, image provenance, and caption boundary. Return the package path, a short
claim-evidence summary, the caption boundary, failed QA items, and reviewer-risk
notes. Do not call the package journal-ready while critical QA items remain.
