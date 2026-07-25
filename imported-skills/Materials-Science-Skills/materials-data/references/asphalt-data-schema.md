# Asphalt And Pavement Data Schema

Use this schema for emulsified asphalt, waterborne epoxy modified emulsified asphalt, tack coat, bonding, and pavement-material datasets.

## Core Fields

- sample_id
- formulation_id
- asphalt_type
- emulsifier_type
- waterborne_epoxy_type
- epoxy_dosage
- curing_condition
- demulsification_condition
- storage_condition
- test_standard
- temperature
- humidity
- aging_condition
- replicate_count
- measured_property
- value
- unit
- processing_note

## Field Specifications

| Field | Type | Unit or format | Typical/allowed values | Sanity check |
|---|---|---|---|---|
| sample_id | string | stable unique ID | `WEA-15-R2` | Must not change between raw and processed data. |
| formulation_id | string | mix/formulation code | `EA-control`, `WEA-10`, `WEA-15` | Link to modifier dosage and emulsion recipe. |
| asphalt_type | categorical | grade/name | `70# base asphalt`, `SBS-modified asphalt`, `bitumen emulsion residue` | State penetration grade or source when possible. |
| emulsifier_type | categorical/string | chemical or supplier label | cationic, anionic, nonionic, [supplier code] | Do not omit charge type for emulsified asphalt. |
| waterborne_epoxy_type | string | resin + curing agent | `bisphenol-A epoxy / amine curing agent` | Record solid content and mixing ratio when available. |
| epoxy_dosage | numeric | `% by dry residue weight of emulsified asphalt` | 2-15% common exploratory range | Values >20% need explanation because storage stability and workability often decline. |
| curing_condition | string or split numeric fields | `25 degC / 50% RH / 7 d` | `23 degC/50%RH/7d`, `60 degC/water bath/48h` | Prefer split fields: curing_temperature_degC, curing_humidity_percent, curing_days. |
| demulsification_condition | string | time/temperature/substrate | `25 degC / 24 h on aggregate substrate` | Needed before linking curing to bonding. |
| storage_condition | string | temperature + duration | `25 degC / 5 d sealed` | Report before claiming storage stability. |
| test_standard | string | standard number/year or lab method | `JTG E20`, `ASTM D244`, `lab pull-off fixture` | If lab method, describe fixture and loading rate. |
| temperature | numeric | degC | 5, 25, 40, 60 | Must match viscosity or bond test condition. |
| humidity | numeric/string | `% RH` | 50% RH, >95% RH | Important for curing and moisture conditioning. |
| aging_condition | string | exposure protocol | `water immersion 24 h`, `freeze-thaw 5 cycles`, `UV 72 h` | Do not call durability without exposure details. |
| replicate_count | integer | n | minimum 3, recommended 5 for pull-off | If n < 3, use descriptive language only. |
| measured_property | categorical | property name | pull_off_strength, shear_strength, viscosity, storage_stability_index | Keep names consistent across datasets. |
| value | numeric | property-specific | measured value | Do not mix units in one column. |
| unit | string | property-specific | MPa, mPa.s, %, mm | Required for FAIR reuse. |

## Recommended Split Columns

For high-quality datasets, split compound fields:

- `curing_temperature_degC`
- `curing_humidity_percent`
- `curing_days`
- `epoxy_dosage_percent_residue`
- `application_rate_L_per_m2`
- `loading_rate_mm_per_min`
- `failure_mode`

## Common Tests

- bonding strength or pull-off strength
- interlayer shear strength
- viscosity
- storage stability
- demulsification or breaking behavior
- FTIR, SEM, fluorescence microscopy, rheology
- moisture damage and aging retention

## Boundary Rule

Bonding strength data do not prove curing mechanism. FTIR, SEM, fluorescence microscopy, rheology, or curing evidence must be present for mechanism claims.
