# Paper-Derived Visual Patterns

This reference records paper-derived visual patterns learned from local materials papers and notes. It is designed for a small review first, especially a review on waterborne epoxy modified emulsified asphalt, bonding performance, interface mechanisms, durability, and evidence chains.

## Boundary

These are reusable visual patterns, not copied paper figures. In short: do not copy paper figures.

- Use the patterns to plan original SVG or matplotlib templates.
- Do not copy paper figures, SEM images, mechanism sketches, captions, color palettes, or data.
- Replace every template with the author's own data, micrographs, test standards, and source-grounded captions before manuscript submission.
- Treat every asset as template only until real evidence is attached.

## Learning Basis

The local learning pass extracted figure and table caption candidates, then grouped them into reusable chart families. The release package keeps only sanitized family-level statistics and design rules. It does not include local file paths, paper images, private notes, or long copied captions.

High-frequency caption families:

- dosage-workability-window
- performance-comparison
- test-matrix-standard
- microstructure-image-plate
- construction-application-workflow
- interface-mechanism-map
- characterization-evidence-panel
- durability-retention
- sustainability-lca-boundary
- review-taxonomy-map

## Claim-Evidence-Boundary Rule

Every paper-derived visual pattern must carry a claim-evidence-boundary:

- Claim: what the figure is allowed to organize or demonstrate.
- Evidence: real data, test standards, micrographs, spectra, or citations required before the claim is manuscript-ready.
- Boundary: what the template must not imply without evidence.

This protects the small review from decorative figures and over-claiming. A taxonomy map can organize the literature, but it cannot prove performance. A mechanism map can show a hypothesis, but arrow strength requires FTIR, SEM, fluorescence microscopy, rheology, bonding, and durability evidence.

## Review-First Patterns

These patterns now inform review planning and the LLM-as-artist workflow. The
LLM writes plotting code directly using matplotlib, following the patterns
defined below. For reference examples, see `assets/materials4papers/` and
`examples/figure-packages/`.

The prioritized figure families remain:

- review framework and taxonomy maps for a small review,
- material-mechanism-performance-challenge structures,
- dosage-workability-window templates,
- performance-comparison templates,
- test-matrix-standard cards,
- microstructure-image-plate layouts,
- interface-mechanism-map schematics,
- characterization-evidence-panel layouts,
- durability-retention summaries,
- research gap and graphical abstract templates.

## Safe Use

Use these templates to ask better figure questions:

- What claim does this figure make?
- Which evidence is required?
- What boundary keeps the caption reviewer-safe?
- Which missing experiment would make the visual stronger?

Do not treat any generated asset as evidence. The assets are layout prompts for original review figures and manuscript planning.
