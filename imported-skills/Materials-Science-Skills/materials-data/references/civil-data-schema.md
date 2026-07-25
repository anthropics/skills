# Civil / Construction Materials Data Schema

Use this schema for soils, aggregates, asphalt binders, asphalt mixtures, cementitious materials, concrete, masonry, geotechnical, and construction-site datasets covering composition, processing, field conditions, and performance.

## Core Fields

- sample_id
- material_type
- project_location
- sample_date
- supplier_source
- gradation_or_sieve_data
- binder_type
- binder_content_pct
- water_content_pct
- compaction_method
- compaction_energy
- curing_or_aging_condition
- test_age_or_service_time
- test_standard
- test_temperature_degC
- replicate_count
- measured_property
- value
- unit
- processing_note

## Field Specifications

| Field | Type | Unit or format | Typical/allowed values | Sanity check |
|---|---|---|---|---|
| sample_id | string | stable unique ID | `AC-13-SBS-R1`, `CLSM-Field-A-7d` | Must trace to source and conditioning. |
| material_type | categorical | material family | soil, aggregate, asphalt_binder, asphalt_mixture, concrete, mortar, masonry, geosynthetic | Determines applicable standards. |
| project_location | string | site or lab | `Highway G42 km 120`, `lab cast` | Field samples need climate and traffic context. |
| sample_date | date | ISO 8601 | `2024-06-15` | Aging and weathering claims need date. |
| supplier_source | string | source | `Local quarry A`, `SBS modifier B`, `OPC CEM I 42.5` | Affects reproducibility. |
| gradation_or_sieve_data | string | percent passing | `19 mm: 100%, 12.5 mm: 85%, 2.36 mm: 35%` | Use standard sieve series. |
| binder_type | string | binder specification | `PG 64-22`, `SBS-modified PG 76-22`, `OPC`, `lime` | Include grade and modifier when relevant. |
| binder_content_pct | numeric | % by mass | 3.5–6.5 (asphalt), 10–15 (cementitious) | State basis (total mix or aggregate mass). |
| water_content_pct | numeric | % | moisture content or w/c ratio | Distinguish total water from effective water. |
| compaction_method | categorical | compaction protocol | Marshall, Superpave gyratory, Proctor, vibratory hammer, field roller | Affects density and mechanical properties. |
| compaction_energy | numeric | gyrations or blows | 75 gyrations, 50 blows/side | Must match standard. |
| curing_or_aging_condition | string | conditioning | `20°C / >95% RH / 28 d`, `RTFO + PAV`, `field aging 2 yr` | Required for binder/asphalt durability. |
| test_age_or_service_time | string | age or time in service | `28 d`, `5 yr`, `after 10^6 load cycles` | Align with curing/aging condition. |
| test_standard | string | standard number/year | `ASTM D6927`, `AASHTO T312`, `GB/T 50081`, `ASTM D1557` | State specimen geometry. |
| test_temperature_degC | numeric | degC | -20, 5, 25, 60 | Binder and asphalt tests are highly temperature-sensitive. |
| replicate_count | integer | n | minimum 3 for most tests | If n < 3, avoid statistical wording. |
| measured_property | categorical | property name | compressive_strength, stability_kN, flow_mm, rutting_depth_mm, resilient_modulus_MPa, permeability | Keep names machine-readable. |
| value | numeric | property-specific | measured value | Do not mix field and lab data without flag. |
| unit | string | property-specific | MPa, kN, mm, mm/mm, %, cycles | Required for FAIR reuse. |

## Recommended Split Columns

For high-quality datasets, split compound fields:

- `air_voids_pct`
- `voids_in_mineral_aggregate_pct`
- `voids_filled_with_asphalt_pct`
- `theoretical_maximum_specific_gravity`
- `bulk_specific_gravity`
- `compaction_temperature_degC`
- `mixing_temperature_degC`
- `specimen_diameter_mm`
- `specimen_height_mm`
- `loading_rate_mm_per_min`
- `wheel_load_kN`
- `number_of_cycles`
- `climate_zone`
- `traffic_level_ESALs`

## Common Tests

- Asphalt binder: penetration, softening point, ductility, DSR, BBR, RTFOT/PAV aging
- Asphalt mixture: Marshall stability/flow, IDT, rutting (wheel tracking), moisture susceptibility, fatigue
- Concrete/mortar: slump, air content, compressive/flexural/tensile strength, chloride penetration, carbonation
- Soil/aggregate: sieve analysis, Atterberg limits, Proctor compaction, CBR, resilient modulus
- Field performance: roughness, distress survey, FWD deflection, skid resistance

## Boundary Rule

Lab mechanical data do not automatically transfer to field performance. Field validation or calibrated performance models are required for service-life claims. Binder/modifier content and aging condition must be reported for any durability or rheological claim.
