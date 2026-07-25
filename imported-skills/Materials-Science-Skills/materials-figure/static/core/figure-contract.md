# Figure Contract Before Plotting

> **Figure contract is a blocking gate.** Before any plotting code, data
> generation, preview, or rendered figure, write `figure_contract.md` with all
> eight points carrying substantive content and pass validation.
> If validation fails, stop and revise the contract; do not plot. **This
> overrides general autonomy/default-execution behavior for figure tasks.**

A publication-quality materials figure is a visual argument, not an isolated pretty plot. Every figure starts from a claim, an evidence chain, a Python backend readiness check, and a reviewer-risk check before code or aesthetics.

## Python-Only Backend Gate

The Python backend is mandatory for plotting, previewing, exporting, and visual QA. Before rendering, check Python plus the packages required by the requested figure family. If the runtime or packages are unavailable, stop before rendering and report the exact blocker.

Do not generate mock data, write plotting scripts, create previews, or render placeholder figures until the claim, source-data anchor, figure contract, and Python backend readiness are clear.

## Eight-Point Contract

All eight points must carry substantive content — not template-only, placeholder,
or empty fields. A contract with any blank or placeholder point is treated as
unwritten and fails validation.

1. **Core conclusion**: one sentence naming the claim the figure must defend.
2. **Evidence chain**: each panel maps to a source-data column, table row, source_map anchor, or visual asset.
3. **Archetype**: classify the figure as `quantitative grid`, `image plate + quant`, `schematic-led composite`, `review heatmap`, `method/test matrix`, or `graphical abstract`.
4. **Backend**: Python backend, checked before plotting and used exclusively.
5. **Journal/export contract**: target journal family, final width, font size, editable vector needs, raster DPI, and required formats.
6. **Statistics and image integrity**: n, replicate definition, error-bar definition, test/correction, raw image provenance, scale bars, crop/contrast notes.
7. **WER-EA boundary**: explicitly separate performance evidence, direct mechanism evidence, inferred mechanism, durability/service evidence, and unsupported field claims.
8. **Reviewer risks**: list unresolved evidence gaps, ambiguity, or presentation risks that could change how the figure is interpreted.

## Contract Validation

Validate the eight-point completeness of
`figure_contract.md`: each point must be present and carry substantive content
(non-template, non-placeholder, non-empty). Validation runs before any plotting
script, data generation, preview, or rendered figure. When materials-science
entities are present, `scripts/validate_materials_claims.py` is a required
materials-domain check.

- Validation passes -> proceed to plotting under the Python-only backend gate.
- Validation fails -> stop. Revise the contract so every point holds real
  content. Do not generate code, data, or previews while the contract is
  invalid.

## Execution Order

The figure contract always precedes plotting code. The mandated order is:

1. For multi-figure work, write and validate the storyboard before individual contracts.
2. Write `figure_contract.md` with all eight points holding substantive content.
3. Validate the contract; stop if it fails.
4. If materials-science entities are present, run `validate_materials_claims.py`
   against `materials_kb.yaml`; stop on errors that contradict known material relations.
5. Only after applicable validations pass, check the Python backend and proceed to
   plotting, source-data assembly, exports, and QA.

This order is binding for both interactive figure work and the LLM-driven workflow. The LLM may draft the contract from the source
table and goal, but the draft must be confirmed and pass both validations
before any plotting script runs.

## Materials Knowledge Validation

After the contract passes validation, run
`validate_materials_claims.py` when materials-science entities are present. The validator extracts materials-science
entities from the contract's evidence chain and checks them against
`static/core/materials_kb.yaml`:

- **XRD**: declared 2θ peaks are matched to PDF cards (±0.5° tolerance). A
  peak assigned to the wrong phase (e.g. 30° 2θ called Al2O3 when it is
  t-ZrO2 101) is an error.
- **FTIR**: declared wavenumbers are matched to functional groups (±20 cm⁻¹
  tolerance). A wavenumber assigned to the wrong group (e.g. 915 cm⁻¹ called
  C=O when it is the oxirane ring) is an error.
- **Performance**: declared values are checked against typical ranges. Values
  far outside known ranges trigger a warning for review.

Figures without materials-science entities (e.g. pure flowcharts or workflow
diagrams) pass with no checks. Errors block plotting; warnings allow plotting
but flag the claim for review.

## Multi-Figure Storyboard

When a task spans more than one figure (e.g. a manuscript), the storyboard
gate sits above individual figure contracts. Write
`figure_storyboard.yaml` (see `assets/templates/figure-storyboard/`) defining:

- **Narrative arc**: ordered figures, each with a role
  (`establish_system` / `prove_mechanism` / `show_performance` /
  `validate_durability` / `summarize` / `compare` / `method_development`).
- **Evidence dependencies**: each figure lists the earlier figures its
  evidence builds on. Dependencies must form a DAG (no cycles).
- **Cross-figure constraints**: style consistency, evidence flow, no panel
  redundancy, claim progression, role coverage.

Run `check_storyboard.py` to verify narrative completeness, acyclic evidence
flow, role coverage, and cross-figure non-redundancy. The storyboard must
pass before individual figure contracts are written. This prevents a set of
individually-valid figures that are narratively incoherent or mutually
redundant.

## Claim Boundary

The caption and visual encoding must never imply stronger evidence than the source supports.

- Performance improvement is not mechanism proof.
- SEM/fluorescence morphology can suggest phase structure but does not prove chemistry alone.
- FTIR/DSR/BBR evidence is binder-level unless interface, mixture, conditioning, or field data are present.
- A review schematic must mark direct evidence and inferred links differently.

For a complete package, write the contract into `figure_contract.md` and validate
before plotting.

## Paper Production Handoff

When a figure request comes from the paper-production orchestrator, consume
`figure_handoff`, `caption_boundary`, `source_anchor`, and the paper `gate report`
before panel design. If source anchors or caption boundaries are
missing, emit a weakness-routing row instead of creating a visually convincing
but unsupported figure.
