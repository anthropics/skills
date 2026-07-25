# Claim-Citation Mapping

> **Domain context**: The `domain` axis has loaded domain-specific citation guidance for [detected domain]. The table below is universal; supplement with domain-specific evidence layers from the domain guide.

Map citations by claim type.

| Claim type | Strong evidence | Weak evidence |
|---|---|---|
| Novelty | recent reviews plus directly related studies | uncited "few studies" statements |
| Mechanism | characterization evidence (2+ complementary techniques) | performance-only speculation |
| Performance | test matrix with controls and statistics | single value without repeatability |
| Durability | standardized aging/environmental tests with conditions | short-term or single-condition data |
| Engineering use | standard tests, constructability, cost or feasibility | lab mechanism with no application boundary |

## Domain-specific evidence layers

- **Civil**: separate citations by emulsion/binder, interface/bonding, mixture, construction, service-condition layers.
- **Polymers**: separate by polymer class, thermal transitions, mechanical performance, rheology, composite interface, aging.
- **Metals**: separate by alloy class, processing, microstructure, mechanical, environmental performance.
- **Ceramics**: separate by processing (sintering), phase composition, microstructure, mechanical, functional properties.
- **Functional**: separate by synthesis, structure (XRD/Raman/XPS), functional property, device performance, stability.
- **Nanomaterials**: separate by synthesis, size/morphology, structural characterization, surface chemistry, size-dependent property.

## Citation Matrix Fields

Use `assets/templates/citation-matrix-template.csv` and fill these screening fields before treating a source as reviewer-safe:

- `claim_id`: stable claim key such as `CIT-001`.
- `evidence_layer`: one layer from the domain-specific evidence layers above.
- `source_role`: `primary experimental evidence`, `review evidence`, `method evidence`, `standard/specification`, or `weak background`.
- `source_quality`: `high`, `medium`, `low`, or `screening needed`.
- `mechanism_directness`: whether mechanism support is direct, inferred, absent, or not applicable.
- `durability_relevance`: whether durability support is direct, adjacent, absent, or not applicable.
- `service_relevance`: whether service/field relevance is direct, lab-scale only, adjacent, or absent.
- `reader_anchor`: page, table, figure, DOI, or note anchor produced by `materials-reader`.
- `figure_handoff`: panel or evidence row that can feed `materials-figure`, or `not assessed`.
- `reviewer_risk`: `must-fix`, `strengthen`, or `optional`.

Do not upgrade a weak background source into a core mechanism, durability, or service claim. If the matrix row still says `screening needed`, send it to reader before using it in manuscript prose.
