# Ceramics Data Schema

Use this schema for oxide ceramics, non-oxide ceramics, structural ceramics, electronic ceramics, refractories, and ceramic-matrix composites covering composition, powder processing, sintering, microstructure, and properties.

## Core Fields

- sample_id
- material_class
- composition_major
- composition_minor
- powder_source
- processing_route
- forming_method
- sintering_temp_degC
- sintering_time_h
- sintering_atmosphere
- relative_density_pct
- grain_size_um
- secondary_phase
- test_standard
- test_temperature_degC
- specimen_geometry
- replicate_count
- measured_property
- value
- unit
- processing_note

## Field Specifications

| Field | Type | Unit or format | Typical/allowed values | Sanity check |
|---|---|---|---|---|
| sample_id | string | stable unique ID | `Al2O3-1600-2h-R1` | Must trace to powder lot and sintering batch. |
| material_class | categorical | ceramic family | oxide, nitride, carbide, boride, silicate, composite | Determines baseline property expectations. |
| composition_major | string | major components with mol% or wt% | `Al2O3-99.7%`, `Si3N4-6wt%Y2O3-2wt%Al2O3` | Report sintering aids explicitly. |
| composition_minor | string | additives, dopants, impurities | `MgO 0.05 wt%`, `Fe2O3 0.02 wt%` | Critical for grain growth and color. |
| powder_source | string | supplier or synthesis | `Sumitomo AKP-50`, `in-house sol-gel`, `commercial TiO2` | Affects reproducibility. |
| processing_route | categorical | synthesis path | solid-state reaction, sol-gel, co-precipitation, hydrothermal | Links to impurity and homogeneity. |
| forming_method | categorical | shaping method | uniaxial pressing, cold isostatic pressing, tape casting, slip casting, injection molding | Determines green density and texture. |
| sintering_temp_degC | numeric | degC | 1200–2200 depending on system | Must be below melting/decomposition point. |
| sintering_time_h | numeric | h | 0.5–24 | Report hold time at peak temperature. |
| sintering_atmosphere | categorical | gas environment | air, N2, Ar, vacuum, reducing | Critical for non-oxide ceramics. |
| relative_density_pct | numeric | % | 90–100 | Below 95% needs explanation for structural claims. |
| grain_size_um | numeric | um | 0.1–50 | Report measurement method (SEM, AFM, XRD line broadening). |
| secondary_phase | string | identified phases | `YAG`, `glass phase`, `Si2N2O` | Quantify by image analysis or Rietveld when possible. |
| test_standard | string | standard number/year | `ASTM C1161`, `ASTM C1421`, `ASTM E384`, `ISO 14704` | State specimen geometry and test rate. |
| test_temperature_degC | numeric | degC | 23, 800, 1200, 1500 | High-temperature data require atmosphere control. |
| specimen_geometry | string | dimensions | `3x4x45 mm bend bar`, `10x10x10 mm cube` | Geometry affects strength distribution. |
| replicate_count | integer | n | minimum 5 for strength (Weibull) | If n < 5, avoid Weibull modulus claims. |
| measured_property | categorical | property name | flexural_strength, fracture_toughness, hardness_HV, dielectric_constant, thermal_conductivity | Keep names machine-readable. |
| value | numeric | property-specific | measured value | Do not mix units in one column. |
| unit | string | property-specific | MPa, MPa√m, HV, W/m·K, % | Required for FAIR reuse. |

## Recommended Split Columns

For high-quality datasets, split compound fields:

- `powder_particle_size_um`
- `powder_specific_surface_area_m2_per_g`
- `green_density_pct`
- `heating_rate_degC_per_min`
- `cooling_rate_degC_per_min`
- `sintering_aid_type`
- `sintering_aid_content_wt%`
- `pore_size_um`
- `pore_volume_fraction`
- `specimen_width_mm`
- `specimen_height_mm`
- `specimen_span_mm`
- `loading_rate_MPa_per_s`
- `weibull_modulus`
- `weibull_characteristic_strength_MPa`

## Common Tests

- Density: Archimedes method (ASTM C373)
- Mechanical: 3-point or 4-point flexure (ASTM C1161, ISO 14704), fracture toughness (ASTM C1421), hardness (ASTM E384, Vickers)
- Microstructure: SEM, TEM, XRD, EBSD, Raman
- Thermal: DSC/TGA, dilatometry, thermal conductivity (laser flash), thermal shock
- Electrical: impedance spectroscopy, dielectric breakdown, piezoelectric coefficient

## Boundary Rule

Mechanical strength data without density and grain size do not prove processing control. Weibull analysis requires at least 15 specimens for reliable modulus estimates. Sintering aids must be reported because they strongly affect high-temperature properties and dielectric loss.
