# Figure Package Protocol

Use this protocol for journal-ready materials figures, WER-EA review figures, or figure audits. The package makes the figure traceable from claim to source data to export and QA.

## Production Package Layout

```text
figure-package/
  figure_contract.md
  source_data.csv
  plot.py
  figure.svg
  figure.pdf
  figure.png
  figure.tiff
  caption.md
  qa_report.md
  asset_manifest.md
```

The Python plotting script is required: `plot.py`. A production package must
generate SVG, PDF, PNG, and TIFF exports before it can be called
`production-ready`.

## Required Fields

`figure_contract.md` must include:

- Core conclusion
- Evidence chain
- Archetype
- Python backend
- Journal/export contract
- Statistics and image integrity
- WER-EA boundary
- Reviewer risk

`caption.md` must include:

- Caption
- What the figure supports
- What the figure does not prove
- Source-data or source-map anchor

`qa_report.md` must include:

- Backend exclusivity
- Export check
- Source-data check
- Statistics check
- Image-integrity check
- Caption-boundary check
- QA status

`asset_manifest.md` must include:

- package name,
- Python backend,
- generated files,
- source data,
- template-only status,
- reviewer-risk note.

## Package Status

Use `template-only` only when the package is a layout or planning example. A template-only figure must not be presented as manuscript evidence.

Use `production-ready` only after visual QA has no unresolved critical issue and the package contains all required files.

## WER-EA Figure Families

The bundled WER-EA sample packages cover:

- `wer-ea-mechanism-map`
- `wer-ea-evidence-heatmap`
- `wer-ea-dosage-window`

Each package must preserve the boundary between direct performance evidence, direct mechanism evidence, inferred mechanism, and unverified durability or field claims.
