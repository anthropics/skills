# Cement And Concrete Data Schema

Use this schema for cement paste, mortar, concrete, UHPC, geopolymer, recycled materials, and durability datasets.

## Core Fields

- sample_id
- mix_id
- binder_type
- water_binder_ratio
- admixture_type
- admixture_dosage
- aggregate_type
- curing_condition
- specimen_geometry
- test_age
- test_standard
- temperature
- humidity
- exposure_condition
- replicate_count
- measured_property
- value
- unit
- processing_note

## Field Specifications

| Field | Type | Unit or format | Typical/allowed values | Sanity check |
|---|---|---|---|---|
| sample_id | string | stable unique ID | `C30-FA20-R1` | Must trace to raw specimen and processed average. |
| mix_id | string | mixture code | `OPC`, `FA20`, `GGBFS40`, `UHPC-SF` | Use the same code in figures and tables. |
| binder_type | categorical | binder family | OPC, SRC, GGBFS, fly_ash, silica_fume, geopolymer, composite | If composite, specify proportions in formulation notes. |
| water_binder_ratio | numeric | mass ratio | 0.18-0.60 depending system | Values outside common range need explanation. |
| admixture_type | string | chemical/mineral admixture | PCE, air entrainer, shrinkage reducer, nano-silica | Include supplier or solid content if important. |
| admixture_dosage | numeric | `% by binder mass` or g/L | 0.1-2.0% for many PCE systems | State basis of percentage. |
| aggregate_type | string | type + grading | limestone, basalt, river sand, recycled aggregate | Report maximum size and moisture condition if relevant. |
| curing_condition | string or split numeric fields | `20 degC / >95% RH / 28 d` | standard curing, steam curing, sealed curing | Prefer split fields for temperature, humidity, and days. |
| specimen_geometry | string | dimensions | `100 mm cube`, `50 mm mortar cube`, `100x200 mm cylinder` | Geometry controls comparability. |
| test_age | numeric | days | 1, 3, 7, 28, 56, 90 | Align age with curing condition. |
| test_standard | string | standard number/year | GB/T 50081, ASTM C39, EN 12390 | Add standard year when possible. |
| exposure_condition | string | durability exposure | chloride, sulfate, carbonation, freeze-thaw, wet-dry | Include concentration, RH, temperature, and cycles. |
| replicate_count | integer | n | minimum 3 | If n < 3, avoid significance wording. |
| measured_property | categorical | property name | compressive_strength, flexural_strength, chloride_migration_coefficient | Keep names machine-readable. |
| value | numeric | property-specific | measured value | Do not mix raw and averaged values without `raw_or_processed`. |
| unit | string | property-specific | MPa, mm, C, m2/s, % | Required for FAIR reuse. |

## Recommended Split Columns

- `curing_temperature_degC`
- `curing_humidity_percent`
- `curing_days`
- `specimen_width_mm`
- `specimen_height_mm`
- `specimen_diameter_mm`
- `loading_rate_MPa_per_s`
- `exposure_cycles`
- `solution_concentration`

## Binder Type Allowed Values

Use `binder_type` as a controlled category when possible:

- `allowed_values`:
- OPC
- SRC
- GGBFS
- fly_ash
- silica_fume
- geopolymer
- composite

If `binder_type` is `composite`, record the exact proportions in `mix_id`, `formulation_notes`, or a separate mixture-design table. Do not hide fly ash, slag, silica fume, or activator content inside an untraceable sample name.

## Common Tests

- fresh properties
- compressive, flexural, or tensile strength
- shrinkage or creep
- chloride penetration, carbonation, sulfate attack, freeze-thaw
- hydration, XRD, FTIR, SEM, MIP, TG/DTG

## Boundary Rule

Strength data alone do not prove hydration mechanism or durability improvement.
