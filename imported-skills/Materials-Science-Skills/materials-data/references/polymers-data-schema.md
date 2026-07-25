# Polymers Data Schema

Use this schema for thermoplastic, thermoset, rubber, and polymer composite datasets covering synthesis, processing, characterization, and performance.

## Core Fields

- sample_id
- polymer_type
- grade_or_formulation
- molecular_weight_Mw
- molecular_weight_Mn
- PDI
- filler_type
- filler_content_wt_pct
- filler_surface_treatment
- processing_method
- processing_temperature_degC
- processing_pressure_MPa
- cooling_rate_C_per_min
- curing_schedule
- test_standard
- test_temperature_degC
- aging_condition
- replicate_count
- measured_property
- value
- unit
- processing_note

## Field Specifications

| Field | Type | Unit or format | Typical/allowed values | Sanity check |
|---|---|---|---|---|
| sample_id | string | stable unique ID | `PP-20GF-R2`, `EP-0.5CNT-A3` | Must not change between raw and processed data. |
| polymer_type | categorical | polymer family | `PP`, `PE`, `PA6`, `PA66`, `PET`, `PC`, `PEEK`, `epoxy`, `PU`, `silicone`, `SBR`, `NBR` | Use standard abbreviations; spell out on first use in metadata. |
| grade_or_formulation | string | commercial grade or lab recipe | `SABIC 56M10`, `DGEBA/DDS 1:0.85` | Record supplier or stoichiometric ratio for lab formulations. |
| molecular_weight_Mw | numeric | g/mol | 50,000–500,000 for thermoplastics | Report GPC method and calibration standard. |
| molecular_weight_Mn | numeric | g/mol | typically Mw / PDI | Required for PDI calculation. |
| PDI | numeric | dimensionless | 1.0–3.0 for most thermoplastics | If PDI > 4, explain broadening source (branching, blending). |
| filler_type | categorical/string | filler identity | `glass fiber`, `carbon fiber`, `nano-SiO2`, `CNT`, `clay`, `CaCO3`, `graphene` | Record geometry (fiber, particle, platelet) and aspect ratio when available. |
| filler_content_wt_pct | numeric | wt% | 0–60 | Values > 50 wt% need justification for processability. |
| filler_surface_treatment | string | coupling agent or treatment | `silane KH-550`, `MAH-g-PP`, `acid-treated`, `untreated` | Critical for interface claims. |
| processing_method | categorical | fabrication route | `injection molding`, `extrusion`, `compression molding`, `hand lay-up`, `RTM`, `3D printing (FDM)`, `electrospinning` | Determines residual stress and morphology. |
| processing_temperature_degC | numeric | degC | melt temp for thermoplastics, cure temp for thermosets | Record barrel zone temps for injection molding. |
| processing_pressure_MPa | numeric | MPa | injection/holding pressure | Omit for hand lay-up or ambient cure. |
| cooling_rate_C_per_min | numeric | degC/min | 1–200 | Critical for crystallinity; report quench vs controlled cooling. |
| curing_schedule | string | temperature/time/atmosphere | `80 degC/2h + 150 degC/4h`, `RT/24h + post-cure 120 degC/2h` | Split into curing_temperature_degC, curing_time_h, post_cure_temp_degC when possible. |
| test_standard | string | standard number/year | `ASTM D638`, `ISO 527`, `ASTM D256`, `ASTM D790` | State specimen type and dimensions. |
| test_temperature_degC | numeric | degC | 23 (room temp), -40, 80, 150 | Must match mechanical or thermal test condition. |
| aging_condition | string | exposure protocol | `UV 500h (ASTM G154)`, `thermal 150 degC/1000h`, `hydrolysis 70 degC/95%RH/1000h` | Do not claim durability without exposure details. |
| replicate_count | integer | n | minimum 5 for tensile, minimum 10 for impact | If n < 5, use descriptive language only. |
| measured_property | categorical | property name | tensile_strength, elongation_at_break, tensile_modulus, impact_strength, HDT, Tg, Tm, crystallinity, gel_content, crosslink_density | Keep names consistent across datasets. |
| value | numeric | property-specific | measured value | Do not mix units in one column. |
| unit | string | property-specific | MPa, %, J/m, degC, g/mol, wt% | Required for FAIR reuse. |

## Recommended Split Columns

For high-quality datasets, split compound fields:

- `curing_temperature_degC`
- `curing_time_h`
- `post_cure_temp_degC`
- `barrel_zone_temps_degC`
- `mold_temperature_degC`
- `injection_speed_mm_per_s`
- `holding_pressure_MPa`
- `specimen_type` (e.g., Type I, Type V for ASTM D638)
- `specimen_thickness_mm`
- `failure_mode` (brittle, ductile, delamination)

## Common Tests

- Tensile: strength, modulus, elongation at break (ASTM D638, ISO 527)
- Impact: Izod notched, Charpy notched (ASTM D256, ISO 179)
- Flexural: strength, modulus (ASTM D790, ISO 178)
- Thermal: DSC (Tg, Tm, crystallinity), TGA (degradation onset, char yield), DMA (storage/loss modulus, tan delta)
- HDT and Vicat (ASTM D648, ISO 306)
- Rheology: MFI (ASTM D1238), capillary rheometry, oscillatory shear (G', G'')
- Gel content / crosslink density (solvent extraction, swelling ratio)
- FTIR, Raman, NMR, XPS
- SEM (fracture surfaces), TEM, AFM, WAXD/SAXS

## Boundary Rule

Mechanical property data do not prove structure-property relationships. Morphology (SEM, WAXD), thermal history (DSC protocol), and processing conditions must be present for mechanism claims. Filler dispersion evidence (SEM/TEM) is required before attributing property gains to nanoscale reinforcement.
