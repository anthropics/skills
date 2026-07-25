# WER-EA Review Figure Contract

Use this reference when planning figures for a WER-EA mini-review, waterborne epoxy emulsified asphalt review, or review-first graphical abstract.

## Figure contract

Every review figure must declare:

- core claim,
- evidence source,
- data/table source,
- figure type,
- visual encoding,
- claim boundary,
- reviewer risk,
- export target.

Do not create a figure that looks more certain than the evidence. A schematic mechanism map must distinguish measured evidence from inferred links.

## Evidence Certainty Tiers

All WER-EA review figures that consume reader handoff rows or citation matrices must use the review-figure intake fields in `references/review-figure-intake.md`.

- `measured`: directly reported tests, observations, or quantitative values.
- `inferred`: mechanism or relationship interpreted from measured evidence.
- `speculative`: plausible schematic element that remains a hypothesis or open question.
- `missing`: absent, untested, not comparable, or outside-scope evidence.

For mechanism maps and evidence heatmaps, make these tiers visible through encoding, legend text, and caption boundary. Do not allow speculative or missing evidence to appear as measured support.

## Required WER-EA review figures

### Mechanism map

Purpose: show how waterborne epoxy resin, curing agent, emulsifier, asphalt phase, and aggregate/interface behavior may connect.

Required boundaries:

- mark direct FTIR/rheology/microscopy evidence separately from inferred curing or compatibility links,
- label measured, inferred, speculative, and missing elements in the legend or callouts,
- avoid presenting bonding performance alone as mechanism proof,
- show missing chemical or microstructural evidence when absent.

### Evidence heatmap

Purpose: compare papers by evidence layers.

Rows should be papers or source groups. Columns should include bonding performance, emulsion stability, rheology, FTIR/chemistry, fluorescence/SEM morphology, durability, and field/service condition.

Required boundaries:

- encode measured, inferred, speculative, and missing cells differently,
- treat unreported evidence as `missing`, not as a negative result,
- keep caption wording tied to the intake `caption_boundary` fields.

### Material-system map

Purpose: group WER-EA formulations by asphalt/emulsion type, waterborne epoxy resin, curing agent, emulsifier, SBR or other modifier, dosage, and preparation route.

Use this to prevent mixing different material systems in one unsupported claim.

### Performance-mechanism boundary

Purpose: separate what performance tests show from what mechanism evidence can support.

The figure should make overclaim boundaries visible: performance improvement, mechanism suggestion, mechanism support, and mechanism confirmation should be different levels.

### Literature-screening flow

Purpose: document how papers move from search results to included WER-EA evidence, adjacent evidence, method evidence, durability evidence, or excluded records.

Use this with the literature-screening-table.

### Graphical abstract

Purpose: give a submission-ready visual story for the review.

The graphical abstract draft should include problem, material modification, evidence chain, application boundary, and remaining gap. It must not invent quantitative improvement or field validation.

## Visual QA

Before finalizing:

- link every panel to a table-system row or source_map.json anchor,
- confirm every included panel mark has a measured, inferred, speculative, or missing certainty tier,
- keep uncertainty visible,
- include units and test conditions for data panels,
- include scale bars for microscopy panels,
- avoid decorative visual elements that imply unsupported mechanism certainty,
- prepare a caption that states claim, evidence, and boundary.
