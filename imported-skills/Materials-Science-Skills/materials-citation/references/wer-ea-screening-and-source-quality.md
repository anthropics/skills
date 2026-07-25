# WER-EA Screening And Source Quality

Use this reference when screening waterborne epoxy resin modified emulsified asphalt (WER-EA) papers for citation matrices, mini-reviews, or reviewer-safe source packages.

## Source Roles

| source_role | Use for | Do not use for |
|---|---|---|
| primary experimental evidence | Direct WER-EA, emulsified asphalt, asphalt interface, rheology, chemistry, or durability measurements. | Broad field trends unless the study includes enough context. |
| review evidence | Background, research gap, taxonomy, and recent-progress claims. | Proving a specific measured performance result. |
| method evidence | Test methods, protocols, data processing, microscopy/FTIR/rheology setup, or precedent for a metric. | Claiming material superiority without matching results. |
| standard/specification | Standard test conditions, engineering requirements, and acceptance criteria. | Mechanism or novelty claims. |
| weak background | Adjacent asphalt, epoxy, polymer, or emulsion context that is not directly WER-EA. | Core claims, mechanism proof, or quantitative comparisons. |

## Evidence Layers

| evidence_layer | Reviewer-safe support |
|---|---|
| material_formulation | WER dosage, emulsifier, asphalt/resin ratio, modifier content, preparation route, and material-design rationale. |
| emulsion_stability | Storage stability, particle size, zeta potential, settlement, sieve residue, and emulsion-breaking stability before use. |
| bonding_interface_performance | Pull-off, shear, direct tension, interlayer bonding, tack coat adhesion, and aggregate-asphalt interface performance. |
| rheology | Viscosity, Brookfield data, flow curve, DSR, shear-rate response, and construction workability boundaries. |
| curing_demulsification | Demulsification, breaking behavior, epoxy curing, crosslinking, gel time, and phase compatibility during setting. |
| microstructure_chemistry | FTIR, SEM, fluorescence microscopy, AFM, phase morphology, functional groups, and chemical/microstructural evidence. |
| moisture_aging_durability | Moisture damage, water immersion, freeze-thaw, aging, fatigue, rutting, and retained performance after exposure. |
| service_field_relevance | Field trial, traffic/environment condition, pavement section, construction process, and in-service engineering relevance. |
| review_background | Review, bibliometric, recent progress, research gap, and field-positioning evidence. |

## Source Quality Labels

| source_quality | Minimum condition |
|---|---|
| high | Direct material match, clear methods, relevant measurements, complete metadata, and no obvious over-claiming risk. |
| medium | Relevant but partial material match, limited durability/mechanism depth, or missing some experimental boundary details. |
| low | Adjacent material system, weak method description, missing controls, or only short-term screening data. |
| screening needed | Candidate source has not yet been read deeply enough to assign quality. |

## Mechanism, Durability, And Service Directness

- `mechanism_directness = direct mechanism evidence` only when chemistry, microscopy, rheology, curing, or phase-compatibility data directly supports the mechanism.
- `mechanism_directness = inferred from performance` when the source reports performance changes but no direct mechanism measurement.
- `durability_relevance = direct durability evidence` only when moisture, aging, freeze-thaw, fatigue, rutting, or retained-performance data is reported.
- `service_relevance = direct service or field evidence` only when construction, traffic, climate, or field-section evidence is present.

## Exclusion Flags

Use one or more `exclusion flags` when a source should not anchor a core claim:

- `not WER-EA`: waterborne epoxy or emulsified asphalt is not part of the studied system.
- `adjacent material only`: epoxy asphalt, polymer-modified asphalt, or emulsion evidence is related but not directly transferable.
- `method only`: useful for protocol or standard precedent, not for performance conclusions.
- `review only`: useful for background, not direct experimental proof.
- `short-term only`: early strength, 24 h bonding, or fresh-property data without durability or service validation.
- `mechanism inferred`: performance is measured but mechanism is not directly characterized.
- `metadata incomplete`: DOI, year, journal, authors, or source provenance need verification before citation.

## Matrix Use

For each candidate source, fill `claim_id`, `evidence_layer`, `source_role`, `source_quality`, `mechanism_directness`, `durability_relevance`, `service_relevance`, `reader_anchor`, `figure_handoff`, and `reviewer_risk` before using it as a core citation. If the source has not been deep-read, keep `source_quality` as `screening needed` and set `reader_anchor` to `[reader anchor needed]`.
