# Review-Figure Intake Protocol

Use this protocol when a review figure consumes reader handoff rows, figure handoff CSVs, or a citation matrix. The goal is to turn evidence rows into panel decisions without inventing evidence.

## Required Intake Fields

Each row must include:

- `claim_id`: stable claim or row identifier from the reader/citation handoff.
- `source_anchor`: page, table, figure, DOI, note, or source_map anchor.
- `citation_key_or_doi`: citation key, DOI, or other source identifier.
- `evidence_layer`: performance, mechanism, material system, method, durability, service, or gap.
- `certainty_tier`: one of `measured`, `inferred`, `speculative`, or `missing`.
- `panel_role`: intended role in the figure panel.
- `visual_encoding`: heatmap cell, solid arrow, dashed arrow, outline node, absence marker, callout, or flow step.
- `caption_boundary`: exact wording boundary for what the visual can and cannot claim.
- `missing_evidence_marker`: how absence, untested conditions, or weak source support will be shown.
- `reviewer_risk`: concise risk label for overclaim, mixed systems, weak method, missing durability, or missing field validation.

Use `assets/templates/review-figure-intake-template.csv` as the CSV-safe starting point.

## Certainty Tiers

- `measured`: directly measured or reported evidence such as bonding strength, viscosity, FTIR peak change, fluorescence/SEM morphology, stability, or durability retention.
- `inferred`: interpretation drawn from measured evidence, such as compatibility, curing linkage, interfacial adhesion mechanism, or phase continuity.
- `speculative`: plausible schematic relationship that lacks direct support in the intake sources and must be drawn as a hypothesis or open question.
- `missing`: evidence that is absent, not reported, not comparable, or outside the source boundary.

Do not promote `inferred`, `speculative`, or `missing` rows into measured-looking marks. Mechanism maps should use line style, opacity, legend language, or annotation to separate tiers. Evidence heatmaps should encode `missing` explicitly rather than leaving blank cells ambiguous.

## Panel Decision Rules

1. Group rows by `evidence_layer` before choosing panels.
2. For mechanism maps, draw `measured` evidence as anchored nodes or solid links, `inferred` links as dashed or annotated links, `speculative` links as hypothesis callouts, and `missing` evidence as gap markers.
3. For evidence heatmaps, reserve a visible code for `missing` and avoid treating untested cells as negative results.
4. For dosage-window or performance-mechanism panels, keep performance rows separate from mechanism rows unless the same source provides both.
5. Any row with high `reviewer_risk` must appear in the caption boundary or figure note.

## Handoff Output

After intake, produce:

- a panel map that lists included and excluded rows,
- a source-data table or source_map anchors for every included mark,
- a caption boundary that names measured, inferred, speculative, and missing evidence,
- a reviewer-risk note for unresolved gaps.
