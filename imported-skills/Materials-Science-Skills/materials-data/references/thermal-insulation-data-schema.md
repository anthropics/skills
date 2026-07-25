# Thermal Insulation Materials Data Schema

Use this schema for fibrous insulation, foam insulation, aerogels, vacuum insulation panels, reflective insulation, and thermally insulating coatings covering composition, microstructure, thermal performance, and mechanical/durability properties.

## Core Fields

- sample_id
- material_class
- product_form
- density_kg_per_m3
- nominal_thickness_mm
- operating_temperature_range_degC
- thermal_conductivity_W_per_mK
- thermal_resistance_m2K_per_W
- measurement_method
- test_standard
- test_temperature_degC
- mean_temperature_degC
- humidity_condition
- aging_condition
- replicate_count
- measured_property
- value
- unit
- processing_note

## Field Specifications

| Field | Type | Unit or format | Typical/allowed values | Sanity check |
|---|---|---|---|---|
| sample_id | string | stable unique ID | `GW-80kg-50mm-R1` | Must trace to product batch and conditioning. |
| material_class | categorical | insulation family | mineral_wool, glass_wool, rock_wool, EPS, XPS, PUR, PIR, aerogel, VIP, reflective | Determines typical conductivity range. |
| product_form | categorical | shape | board, blanket, loose_fill, spray_foam, panel, coating | Affects measurement geometry. |
| density_kg_per_m3 | numeric | kg/m³ | 10–300 (fibrous/foam), 100–400 (aerogel) | Density strongly correlates with conductivity. |
| nominal_thickness_mm | numeric | mm | 20–200 | Thickness determines thermal resistance. |
| operating_temperature_range_degC | string | temperature range | `-50 to 100`, `up to 650` | Claims above catalog range need data. |
| thermal_conductivity_W_per_mK | numeric | W/(m·K) | 0.015–0.100 | Report at stated mean temperature. |
| thermal_resistance_m2K_per_W | numeric | m²·K/W | 0.5–5.0 | Requires thickness and conductivity consistency. |
| measurement_method | categorical | technique | guarded_hot_plate, heat_flow_meter, hot_box, transient_plane_source | Method affects accuracy and applicable thickness. |
| test_standard | string | standard number/year | `ASTM C518`, `ASTM C177`, `ISO 8301`, `ISO 8302` | State specimen size and edge conditions. |
| test_temperature_degC | numeric | degC | 10, 23, 50 | Conductivity is temperature-dependent. |
| mean_temperature_degC | numeric | degC | 10, 23, 50 | Required for reporting thermal conductivity. |
| humidity_condition | string | RH or moisture content | `50% RH`, `conditioned at 23°C/50% RH` | Moisture drastically affects performance. |
| aging_condition | string | conditioning | `none`, `90 d at 70°C/95% RH`, `freeze-thaw 30 cycles` | Long-term performance claims need aging data. |
| replicate_count | integer | n | minimum 3 | If n < 3, avoid statistical wording. |
| measured_property | categorical | property name | thermal_conductivity, thermal_resistance, compressive_strength, water_absorption, dimensional_stability | Keep names machine-readable. |
| value | numeric | property-specific | measured value | Do not mix different test temperatures in one column. |
| unit | string | property-specific | W/(m·K), m²·K/W, MPa, %, kg/m² | Required for FAIR reuse. |

## Recommended Split Columns

For high-quality datasets, split compound fields:

- `specimen_length_mm`
- `specimen_width_mm`
- `specimen_thickness_mm`
- `cold_surface_temperature_degC`
- `hot_surface_temperature_degC`
- `temperature_difference_K`
- `edge_loss_correction_applied`
- `compressive_strength_kPa`
- `tensile_strength_perpendicular_to_faces_kPa`
- `water_absorption_short_term_kg_per_m2`
- `water_vapor_permeance_ng_per_Pa_s_m2`
- `dimensional_stability_pct`
- `reaction_to_fire_class`
- `smoke_development_index`

## Common Tests

- Thermal: guarded hot plate (ASTM C177), heat flow meter (ASTM C518), hot box (ASTM C1363)
- Mechanical: compressive strength (ASTM C165, ISO 29469), tensile strength perpendicular to faces
- Moisture: water absorption (ASTM C209, ASTM C272), water vapor transmission (ASTM E96)
- Durability: aging, freeze-thaw, dimensional stability
- Fire: reaction to fire, smoke development, surface burning characteristics

## Boundary Rule

Thermal conductivity must be reported with mean temperature and measurement method. Claims about long-term performance require aging or field exposure data. Density and thickness must be reported because they control thermal resistance and mechanical behavior.
