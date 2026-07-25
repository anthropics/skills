# Functional Materials Data Schema

Use this schema for semiconductor, dielectric, piezoelectric, photonic, and optoelectronic material datasets covering composition, processing, characterization, and device performance.

## Core Fields

- sample_id
- material_system
- base_material
- dopant_type
- dopant_concentration
- synthesis_method
- sintering_temp_degC
- sintering_time_h
- sintering_atmosphere
- relative_density_pct
- grain_size_um
- crystal_structure
- measurement_frequency_Hz
- measurement_temperature_degC
- applied_field_kV_per_cm
- specimen_geometry
- test_standard
- aging_condition
- replicate_count
- measured_property
- value
- unit
- processing_note

## Field Specifications

| Field | Type | Unit or format | Typical/allowed values | Sanity check |
|---|---|---|---|---|
| sample_id | string | stable unique ID | `BaTiO3-1molNb-R2`, `ZnO-0.5Al-TCO` | Must not change between raw and processed data. |
| material_system | categorical | functional class | `ferroelectric`, `piezoelectric`, `dielectric`, `semiconductor`, `thermoelectric`, `ionic conductor`, `photovoltaic`, `phosphor`, `luminescent` | Defines primary property of interest. |
| base_material | string | host compound | `BaTiO₃`, `PZT`, `ZnO`, `GaN`, `SiC`, `Bi₂Te₃`, `YAG`, `CsPbBr₃` | Use chemical formula; state crystal system. |
| dopant_type | string | dopant identity | `Nb⁵⁺`, `La³⁺`, `Al³⁺`, `Mn²⁺`, `Er³⁺`, `none` | State valence when relevant. |
| dopant_concentration | string | mol% or at% | `0.5 mol%`, `2 at%`, `x=0.03` | Report solid solution limit if known. |
| synthesis_method | categorical | preparation route | `solid-state reaction`, `sol-gel`, `co-precipitation`, `hydrothermal`, `PLD`, `sputtering`, `MBE`, `CVD`, `MOCVD`, `pulsed laser deposition` | Report calcination step for solid-state. |
| sintering_temp_degC | numeric | degC | 1000–1400 (ceramics), 200–600 (thin films) | Report ramp rate and dwell time. |
| sintering_time_h | numeric | h | 1–24 (ceramics), 0.1–2 (thin films) | Critical for grain growth. |
| sintering_atmosphere | categorical | gas environment | `air`, `O₂`, `N₂`, `Ar`, `vacuum`, `forming gas (Ar/H₂)` | Critical for defect chemistry. |
| relative_density_pct | numeric | % | 90–100 | Report theoretical density reference. |
| grain_size_um | numeric | µm | 0.1–50 | State measurement method (intercept, EBSD, AFM). |
| crystal_structure | string | phase identification | `perovskite (cubic)`, `wurtzite`, `zinc blende`, `spinel`, `fluorite`, `rutile` | Report XRD conditions. |
| measurement_frequency_Hz | numeric | Hz | 10²–10⁹ | Critical for dielectric/impedance data. |
| measurement_temperature_degC | numeric | degC | -100–600 | Must match property measurement condition. |
| applied_field_kV_per_cm | numeric | kV/cm | 0.1–100 (ferroelectric), 0–50 (dielectric breakdown) | Report for polarization and dielectric measurements. |
| specimen_geometry | string | dimensions and form | `disk 10mm × 1mm`, `thin film 500nm on Si`, `bar 3×4×20mm` | Report electrode type and area. |
| test_standard | string | standard number | `IEEE 176` (piezoelectric), `IEC 60250` (dielectric), `ASTM E1461` (thermal diffusivity) | State instrument model. |
| aging_condition | string | exposure protocol | `thermal 200°C/1000h`, `humidity 85%RH/500h`, `UV 1000h` | Do not claim stability without exposure details. |
| replicate_count | integer | n | minimum 3 for dielectric, minimum 5 for Weibull | If n < 3, use descriptive language only. |
| measured_property | categorical | property name | dielectric_constant, loss_tangent, d33, piezoelectric_d31, remanent_polarization, coercive_field, band_gap, conductivity_ionic, Seebeck_coefficient, thermal_conductivity | Keep names consistent across datasets. |
| value | numeric | property-specific | measured value | Do not mix units in one column. |
| unit | string | property-specific | dimensionless, pC/N, µC/cm², kV/cm, eV, S/cm, µV/K, W/m·K | Required for FAIR reuse. |

## Recommended Split Columns

For high-quality datasets, split compound fields:

- `calcination_temp_degC`
- `calcination_time_h`
- `ramp_rate_degC_per_min`
- `electrode_material` (e.g., Ag paste, Au sputtered, Pt)
- `electrode_area_mm2`
- `specimen_thickness_mm`
- `poling_field_kV_per_cm`
- `poling_temperature_degC`
- `poling_time_min`
- `Curie_temperature_degC`

## Common Tests

- Dielectric: permittivity (εr), loss tangent (tan δ) vs frequency and temperature (IEC 60250)
- Ferroelectric: P-E hysteresis loop, remanent polarization (Pr), coercive field (Ec)
- Piezoelectric: d₃₃ (Berlincourt), d₃₁ (impedance), coupling factor (k)
- Impedance: Nyquist plot, grain/grain-boundary resistance, activation energy
- Optical: UV-Vis (band gap via Tauc plot), PL emission/excitation, refractive index
- Electrical: Hall effect (carrier concentration, mobility), four-point probe (resistivity)
- Thermal: thermal diffusivity (laser flash), thermal conductivity, specific heat
- Ferroelectric: Curie temperature, depolarization temperature

## Boundary Rule

Dielectric constant data alone do not prove composition-structure-property relationships. Phase purity (XRD), grain size (SEM), density, and measurement conditions (frequency, temperature, field) must be reported before claiming compositional effects. Impedance spectroscopy is required to separate grain and grain-boundary contributions.
