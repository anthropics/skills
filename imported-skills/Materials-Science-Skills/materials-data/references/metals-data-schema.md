# Metals Data Schema

Use this schema for ferrous alloys, nonferrous alloys, high-temperature alloys, and additively manufactured metal datasets covering composition, processing, microstructure, and performance.

## Core Fields

- sample_id
- alloy_grade
- standard_designation
- composition_major
- composition_trace
- processing_route
- heat_treatment_schedule
- austenitizing_temp_degC
- austenitizing_time_min
- quench_medium
- tempering_temp_degC
- tempering_time_min
- test_standard
- test_temperature_degC
- specimen_orientation
- strain_rate_per_s
- aging_condition
- replicate_count
- measured_property
- value
- unit
- processing_note

## Field Specifications

| Field | Type | Unit or format | Typical/allowed values | Sanity check |
|---|---|---|---|---|
| sample_id | string | stable unique ID | `4340-QT-R2`, `316L-AM-0.8vol` | Must not change between raw and processed data. |
| alloy_grade | categorical | commercial designation | `AISI 4340`, `316L`, `Inconel 718`, `AA 7075-T6`, `Ti-6Al-4V` | Use standard abbreviations; state UNS number when available. |
| standard_designation | string | ASTM/EN/GB standard | `ASTM A370`, `EN 10002-1`, `GB/T 228.1` | State edition year. |
| composition_major | string | major elements with wt% | `Fe-0.4C-1.8Ni-0.8Cr-0.25Mo` | List all alloying elements > 0.1 wt%. |
| composition_trace | string | trace elements with ppm or wt% | `S: 0.003%, P: 0.015%, V: 0.05%` | Report S and P for steels. |
| processing_route | categorical | fabrication method | `casting`, `hot rolling`, `cold rolling`, `forging`, `extrusion`, `additive manufacturing (SLM/LPBF/DED)`, `welding` | Determines residual stress and texture. |
| heat_treatment_schedule | string | full HT protocol | `850°C/30min/oil quench + 550°C/2h/air cool` | Split into sub-fields when possible. |
| austenitizing_temp_degC | numeric | degC | 800–1250 (steel), 480–540 (Al solution) | Must be above Ac3 for hypoeutectoid steels. |
| austenitizing_time_min | numeric | min | 15–120 | Depends on section thickness. |
| quench_medium | categorical | cooling medium | `water`, `oil`, `air`, `polymer`, `brine`, `N₂ gas` | Critical for hardenability. |
| tempering_temp_degC | numeric | degC | 150–650 | Report if tempering was performed. |
| tempering_time_min | numeric | min | 30–360 | Report holding time at temperature. |
| test_standard | string | standard number/year | `ASTM E8`, `ASTM E23`, `ASTM E399`, `ASTM E647`, `ASTM G48` | State specimen type and dimensions. |
| test_temperature_degC | numeric | degC | 23 (room temp), -40, 300, 600, 800 | Must match mechanical or corrosion test condition. |
| specimen_orientation | categorical | rolling direction | `LT`, `TL`, `ST`, `L`, `T`, `S` | Critical for anisotropic properties. |
| strain_rate_per_s | numeric | 1/s | 10⁻³ (quasi-static), 10¹ (intermediate), 10³ (high strain rate) | Report for dynamic tests. |
| aging_condition | string | exposure protocol | `salt spray 500h (ASTM B117)`, `creep 600°C/1000h`, `fatigue R=0.1, 10⁷ cycles` | Do not claim durability without exposure details. |
| replicate_count | integer | n | minimum 3 for tensile, minimum 3 for fracture toughness | If n < 3, use descriptive language only. |
| measured_property | categorical | property name | yield_strength, UTS, elongation, hardness_HV, impact_energy, K_IC, J_IC, da_dN, corrosion_rate, grain_size | Keep names consistent across datasets. |
| value | numeric | property-specific | measured value | Do not mix units in one column. |
| unit | string | property-specific | MPa, %, J, HV, MPa√m, mm/year | Required for FAIR reuse. |

## Recommended Split Columns

For high-quality datasets, split compound fields:

- `rolling_temperature_degC`
- `rolling_reduction_pct`
- `forging_temperature_degC`
- `solution_treatment_temp_degC`
- `solution_treatment_time_h`
- `aging_temp_degC`
- `aging_time_h`
- `welding_current_A`
- `welding_speed_mm_per_s`
- `laser_power_W` (for AM)
- `scan_speed_mm_per_s` (for AM)
- `layer_thickness_um` (for AM)
- `specimen_diameter_mm`
- `gauge_length_mm`
- `fracture_mode` (ductile, brittle, intergranular, transgranular, mixed)

## Common Tests

- Tensile: yield strength (Rp0.2), UTS, elongation, reduction of area (ASTM E8, ISO 6892)
- Impact: Charpy V-notch (ASTM E23, ISO 148)
- Hardness: Vickers, Rockwell, Brinell (ASTM E92, ASTM E18, ASTM E10)
- Fracture toughness: K_IC, J_IC (ASTM E399, ASTM E1820)
- Fatigue: S-N curve, da/dN vs ΔK (ASTM E466, ASTM E647)
- Creep: creep rate, rupture life (ASTM E139)
- Corrosion: potentiodynamic polarization, salt spray, intergranular corrosion (ASTM G5, ASTM B117, ASTM A262)
- Metallography: optical microscopy, SEM, EBSD, TEM, XRD
- Thermal: DSC/DTA (phase transformation), dilatometry (CTE, Ms/Mf)

## Boundary Rule

Mechanical property data do not prove processing-microstructure relationships. Metallography (grain size, phase fraction, precipitate characterization via SEM/TEM/EBSD) and heat treatment parameters must be present for mechanism claims. Fracture toughness data require fractography evidence (SEM) to support failure mode interpretation.
