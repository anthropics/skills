# materials-reader

**Version:** 1.3.0

**What it does** — The source-grounded reading engine for the bundle. Use it
when the raw material is a paper, PDF, abstract, figure caption, or pasted
source text and you need structured notes you can trust downstream. It
produces standard reader packages with bilingual notes, source anchors,
figure/table evidence maps, and claim-evidence-mechanism-boundary matrices,
plus handoff rows for the citation and figure skills. It detects the source
format (pdf-text, scanned-pdf, doi-arxiv, html, pasted-text) and the output
type (full notes, literature matrix, evidence-chain audit, figure-anchored
reading, journal-club reading, microstructure interpretation) and loads only
the matching fragments.

The default core is limited to the reader contract, direction profile, and
workflow. Terminology and ethics rules are named on-demand routes; terminology
must be loaded for each paper reading, including bilingual notes, translation,
normalization, and intensive reader packages.

**Built from** — A source-grounded reading engine with 14 reference
protocols, schema-validated output packages, and reusable templates:

- `references/wer-ea-intensive-reading-package.md` — WER-EA intensive reading
  protocol (30-paper package, translation notes, mechanism-evidence table,
  dosage window, review handoff)
- `references/ceramics-intensive-reading-package.md` — ceramics intensive
  reading protocol
- `references/full-reader.md` — full bilingual notes protocol
- `references/fulltext-figure-anchored-reading.md` — figure/table-anchored
  full-text reading
- `references/evidence-chain-audit.md` — claim-evidence audit protocol
- `references/evidence-to-review-handoff.md` — citation/figure handoff
- `references/source-grounding.md` — source-anchor rules
- `references/standard-output-package.md` — package manifest and source map
- `references/pdf-reading.md`, `pdf-visual-asset-extraction.md`,
  `microstructure-interpretation.md`, `literature-matrix.md`,
  `journal-club-reading.md`, `table-system.md` — supporting protocols
- `assets/schemas/` — 4 JSON schemas (package manifest, source map, visual
  asset spec, visual asset report)
- `assets/templates/` — 15 templates (notes, handoffs, tables, QA)
- `scripts/` — build / audit / validate reader package, evidence-chain audit,
  PDF visual asset extraction, new-note scaffolding
- public verification through the repository release gate

**Key rules enforced**

- Source-anchor every claim to page, paragraph, or figure; no floating
  assertions.
- Build claim-evidence-mechanism-boundary rows: what the paper claims, what
  evidence supports it, the proposed mechanism, and the claim boundary.
- Distinguish what the paper says from what you infer; flag overclaim in the
  confidence note.
- Never interpret microstructure or mechanism without explicit evidence.
- Keep source anchors stable so citation and figure handoffs stay traceable.

**Reference files**

```text
skills/materials-reader/
├── README.md
├── SKILL.md
├── manifest.yaml
├── scripts/
│   ├── build_reader_package.py          assembles reader package
│   ├── validate_reader_package.py       package contract validator
│   ├── audit_reader_package.py          package QA auditor
│   ├── build_evidence_chain_audit.py    evidence-chain audit builder
│   ├── extract_pdf_visual_assets.py     PDF visual asset extractor
│   └── new_reader_note.py               new-note scaffolding
├── assets/
│   ├── schemas/                         4 JSON schemas (manifest, source-map, visual-asset)
│   └── templates/                       15 templates (notes, handoffs, tables, QA)
├── static/
│   ├── core/                            contract, reader-contract, workflow
│   └── fragments/
│       ├── domain/                      6 material-domain routing fragments
│       └── source/                      5 source-format fragments
└── references/
    ├── wer-ea-intensive-reading-package.md    WER-EA intensive reading protocol
    ├── ceramics-intensive-reading-package.md  ceramics intensive reading protocol
    ├── full-reader.md                         full bilingual notes protocol
    ├── fulltext-figure-anchored-reading.md    figure/table-anchored reading
    ├── evidence-chain-audit.md                claim-evidence audit protocol
    ├── evidence-to-review-handoff.md          citation/figure handoff
    ├── source-grounding.md                    source-anchor rules
    ├── standard-output-package.md             package manifest and source map
    ├── pdf-reading.md                         PDF reading guidance
    ├── pdf-visual-asset-extraction.md         PDF visual asset extraction
    ├── microstructure-interpretation.md       SEM/AFM/TG microstructure reading
    ├── literature-matrix.md                   literature matrix protocol
    ├── journal-club-reading.md                journal-club reading protocol
    └── table-system.md                        table-system templates
```

**Validation**

- Run reader package scripts directly when changing package generation:
  `build_reader_package.py`, `validate_reader_package.py`, and `audit_reader_package.py`.
- Bundle verification:
  `python .\scripts\run_release_checks.py --json`

The public GitHub package does not ship the internal reader regression suite.

## When To Use

Use `materials-reader` when the user request matches this skill's production surface and the needed inputs are available or can be explicitly marked as missing.

## Inputs

Typical inputs are the user prompt, material direction/profile, target journal or task mode when relevant, and any source text, data, figures, reviewer comments, or package artifacts needed by the skill.

## Outputs

Outputs are structured handoffs or artifacts described above in this README. Missing evidence, author input needs, and unsupported claims stay visible instead of being hidden in fluent prose.

## Example

```text
Build a source-grounded reader package from a pasted abstract and figures.
```

## Validation

Run the skill-specific scripts or tests listed above when they apply, then run the bundle gate from the repository root:

```powershell
python .\scripts\run_release_checks.py --json
```

## Boundaries

This skill does not invent experiments, citations, measurements, journal facts, private file paths, or completed actions. Time-sensitive journal or legal facts should be checked against official sources before submission or filing.
