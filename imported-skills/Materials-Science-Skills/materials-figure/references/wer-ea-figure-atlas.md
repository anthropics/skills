# WER-EA Figure Atlas

This atlas defines reusable, reviewer-safe figure patterns for waterborne epoxy resin modified emulsified asphalt (WER-EA) reviews. The assets are data-driven or data-informed review figures with explicit claim boundaries, not stand-alone experimental proof.

## Core Rule

Every atlas figure must separate measured evidence, inferred interpretation, speculative mechanism, and missing evidence. A figure may be visually polished only after its source anchors, required evidence, caption boundary, and reviewer risk are explicit.

## Figure Families

| Family | Purpose | Evidence Boundary |
|---|---|---|
| `wer-ea-mechanism-map` | Map resin, curing, emulsion, asphalt phase, aggregate interface, and water pathway links. | Arrows are measured, inferred, speculative, or missing. Bonding strength alone is not mechanism proof. |
| `evidence-heatmap` | Compare papers or source groups by evidence layer and source quality. | Missing reports are marked missing, not interpreted as negative results. |
| `material-system-map` | Group formulations by asphalt, emulsifier, epoxy, curing agent, dosage, and preparation route. | Similar names do not imply comparable systems without formulation anchors. |
| `performance-mechanism-boundary` | Separate performance improvement from mechanism support. | Performance data can suggest but not prove mechanism unless characterization supports it. |
| `literature-screening-flow` | Show search, screening, inclusion, exclusion, and evidence classification. | Counts require transparent search records and exclusion reasons. |
| `graphical-abstract` | Summarize problem, material design, evidence chain, application boundary, and gaps. | Does not imply universal performance gain or field validation. |
| `dosage-workability-window` | Link WER dosage, viscosity, bonding, storage stability, and workability. | Optimum dosage is conditional on test protocol and construction temperature. |
| `emulsion-stability-timeline` | Show storage or demulsification stability over time. | Stability alone does not prove pavement bonding performance. |
| `curing-demulsification-sequence` | Show emulsion breaking, water escape, epoxy curing, and asphalt film formation. | Sequence is speculative unless time-resolved evidence exists. |
| `bonding-performance-comparison` | Compare bonding metrics under matched dry, wet, aged, or cured states. | Cross-study comparison requires matching method, units, and conditioning. |
| `pull-off-shear-method-comparison` | Compare pull-off, shear, direct tension, and failure mode evidence. | Test modes are not interchangeable without geometry and loading context. |
| `rheology-performance-link` | Link viscosity, modulus, phase angle, or flow to workability and bonding. | Correlation is not causation without controlled formulation. |
| `ftir-peak-assignment-card` | Summarize peak assignments and chemical evidence. | Peak shifts alone cannot prove macroscopic bonding improvement. |
| `sem-fluorescence-image-plate` | Organize morphology and phase-distribution images. | Qualitative images need scale bars and representative-image cautions. |
| `durability-retention-map` | Show retained properties after water, aging, heat, or freeze-thaw conditioning. | Retention needs baseline value, conditioned value, and protocol. |
| `water-aging-freeze-thaw-challenge-map` | Map durability challenge categories and missing service evidence. | Accelerated tests are not direct field validation. |
| `test-standard-condition-card` | Harmonize specimen, loading, curing, conditioning, and response fields. | Standards support methods, not novelty or mechanism claims. |
| `construction-application-workflow` | Show surface preparation, spraying, curing, overlay, and quality checks. | Workflow is contextual and site dependent. |
| `sustainability-lca-boundary-card` | Define functional unit, system boundary, inventory basis, and comparison limits. | Sustainability claims require quantified LCA. |
| `research-gap-matrix` | Separate mature laboratory evidence from missing field, durability, or mechanism validation. | Gap strength depends on transparent screening scope. |

## Required Files

The pre-generated atlas assets (SVG/PNG/CSV) have been removed in the
transition to LLM-as-artist mode. The LLM now writes plotting code directly
using matplotlib, following the figure families and evidence boundaries
defined above. For reference examples, see `assets/materials4papers/` and
`examples/figure-packages/`.

Generated SVG/PNG examples must preserve the claim boundary described in this atlas. Illustrative panels such as the graphical abstract, SEM/fluorescence plate, and LCA boundary card should stay explicitly labeled as data-informed or illustrative where applicable.

## Visual Encoding

Use a consistent certainty legend:

- `measured`: solid line or filled marker.
- `inferred`: dashed line or semi-filled marker.
- `speculative`: dotted line or outline marker.
- `missing`: grey absent marker or cross-hatched cell.

## QA Checklist

- [ ] Asset row has required evidence.
- [ ] Asset row has claim boundary.
- [ ] Asset row has source data template.
- [ ] Generated SVG includes a certainty legend.
- [ ] Generated example claim boundary matches the current atlas contract.
- [ ] No local absolute path appears in asset specs or SVG output.
