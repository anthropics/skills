# Ceramics Intensive Reading Package

Use this protocol when a ceramics paper (structural ceramics, functional ceramics, refractories, bioceramics) must become a reusable research asset.

## Required artifacts

Create one folder per paper:

```
<paper-id>/
  paper.md
  source_map.json
  translation_notes.md
  figure_table_cards.md
  mechanism_evidence_table.md
  processing_table.md
```

### paper.md

Structure:

1. **One-sentence takeaway**: what the paper contributes.
2. **Material system**: composition, powder source, purity, particle size.
3. **Processing**: forming method, sintering profile (T, ramp, dwell, atmosphere), post-processing.
4. **Characterization matrix**: what was measured (density, XRD, SEM, mechanical, thermal, functional).
5. **Key results**: density, phase, microstructure features, mechanical/functional properties.
6. **Mechanism claim**: what evidence supports the claimed mechanism.
7. **Limitations**: specimen size, statistics, test conditions, reproducibility.

### source_map.json

Anchor every claim to a source location (page, section, figure/table label).

### mechanism_evidence_table

| Claim | Evidence type | Characterization | Certainty | Missing evidence |
|---|---|---|---|---|
| Phase purity | XRD | Pattern matching, Rietveld | Strong if Rietveld R < 10% | No reference pattern cited |
| Grain size effect | SEM + statistics | Linear intercept method | Moderate n ≥ 200 grains | No distribution reported |
| Toughening mechanism | Fractography + KIC | Crack path analysis | Strong if both trans/intergranular | No KIC standard cited |

### processing_table

| Parameter | Value | Notes |
|---|---|---|
| Powder purity | 99.9% | Supplier reported but not verified |
| Forming method | Uniaxial pressing | 200 MPa, no binder |
| Sintering T | 1600°C | Heating rate 5°C/min reported |
| Atmosphere | Air | — |
| Dwell | 2 h | — |
| Cooling | Furnace cool | Rate not specified |

## Domain-specific reading priorities

1. **Sintering profile**: the most critical processing parameter; must be fully reported.
2. **Density**: relative density is the most fundamental quality indicator.
3. **Phase identification**: XRD with reference pattern matching or Rietveld.
4. **Microstructure**: grain size, grain boundary phase, porosity distribution.
5. **Mechanical testing**: test standard, specimen geometry, number of specimens.
6. **Weibull statistics**: required for any brittle material strength claim.

## Reviewer-risk flags

| Red flag | Severity | Action |
|---|---|---|
| Sintering profile incomplete (no ramp/dwell) | Major | Flag in notes, mark processing as incomplete |
| Density reported without method | Major | Cannot verify; mark as unconfirmed |
| Weibull modulus with n < 10 | Major | Note insufficient statistics |
| Phase ID without reference pattern | Moderate | Flag as unconfirmed identification |
| Mechanical data without standard | Major | Cannot reproduce; mark as unverified |
| Single SEM image as "representative" | Minor | Note need for multiple fields |
