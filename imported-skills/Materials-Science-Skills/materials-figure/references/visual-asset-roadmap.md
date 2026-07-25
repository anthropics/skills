# Visual Asset Roadmap

The goal is not to imitate `nature-figure` by dumping random previews. Civil materials needs visual richness that maps to real reviewer questions.

## SVG-first strategy

Use an SVG-first asset library for fast loading, easy diffing, and low repository weight. Use PNG only when the asset is image-like, such as SEM, fluorescence, CT, or asphalt mixture texture plates.

## Growth targets

- 10 assets: rich gallery seed set for waterborne epoxy emulsified asphalt and cement/concrete writing.
- 30 assets: cover the main manuscript figure families for asphalt, cement/concrete, durability, mechanism, and sustainability, with reusable review-first patterns and generated examples for small reviews.
- 60 assets: add journal-specific CBM/CCC/RMPD/JBE variants, grayscale variants, and Chinese/English caption examples.
- 100 assets: approach nature-style richness with full visual archetype coverage, including image plates, mechanism schematics, radar/retention summaries, LCA visuals, and standards/test workflow diagrams.

## Asset families

1. performance comparison,
2. dosage optimization,
3. interface mechanism map,
4. FTIR/XRD/TG evidence panels,
5. SEM/fluorescence morphology plates,
6. durability retention,
7. construction workflow,
8. standards/test matrix,
9. sustainability/LCA boundary,
10. review taxonomy and research agenda.

## Quality rule

Every asset must include a claim boundary. The visual should teach what kind of claim is safe, what evidence is needed, and what a reviewer might challenge.

## Review-first package

Use `paper-derived-visual-patterns.md` for small review planning. The package
is based on sanitized local caption-family learning, not copied figures.

The pre-generated review-first assets have been removed in the transition to
LLM-as-artist mode. The LLM now writes plotting code directly using matplotlib,
following the patterns defined in `paper-derived-visual-patterns.md`. For
reference examples, see `assets/materials4papers/` and `examples/figure-packages/`.
