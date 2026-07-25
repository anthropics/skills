# Nano Data Schema

Use this schema for nanoparticle, nanocomposite, 2D material, and thin film datasets covering synthesis, characterization, and performance.

## Core Fields

- sample_id
- nanomaterial_type
- synthesis_method
- precursor
- synthesis_temperature_degC
- synthesis_duration_h
- atmosphere
- particle_size_nm
- size_distribution_PDI
- surface_area_m2_per_g
- aspect_ratio
- surface_functionalization
- zeta_potential_mV
- crystal_structure
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
| sample_id | string | stable unique ID | `AgNP-20-citrate-R2`, `GO-0.5wt%-epoxy` | Must not change between raw and processed data. |
| nanomaterial_type | categorical | nano form | `nanoparticle`, `nanorod`, `nanotube`, `nanofiber`, `nanosheet`, `2D material`, `quantum dot`, `nanocomposite`, `thin film` | State dimensionality (0D/1D/2D/3D). |
| synthesis_method | categorical | preparation route | `sol-gel`, `hydrothermal`, `solvothermal`, `CVD`, `PVD`, `ball milling`, `liquid-phase exfoliation`, `chemical reduction`, `co-precipitation`, `electrospinning` | Report key parameters for each method. |
| precursor | string | chemical identity | `AgNO₃ + sodium citrate`, `tetraethyl orthosilicate (TEOS)`, `graphite + H₂SO₄/KMnO₄` | Record molar ratios when applicable. |
| synthesis_temperature_degC | numeric | degC | 25–800 | Report ramp rate for hydrothermal/solvothermal. |
| synthesis_duration_h | numeric | h | 0.5–72 | Critical for nucleation/growth kinetics. |
| atmosphere | categorical | gas environment | `air`, `N₂`, `Ar`, `H₂/N₂`, `vacuum`, `O₂` | Report for CVD/PVD/annealing. |
| particle_size_nm | numeric | nm | 1–500 | State measurement method (TEM, DLS, XRD Scherrer). |
| size_distribution_PDI | numeric | dimensionless | 0.05–0.5 (DLS) | Values > 0.7 indicate broad polydispersity. |
| surface_area_m2_per_g | numeric | m²/g | BET method | State degassing conditions. |
| aspect_ratio | numeric | dimensionless | 1 (sphere) to >1000 (CNT) | Report for anisotropic nanostructures. |
| surface_functionalization | string | ligand or treatment | `citrate`, `PEG-2000`, `silane APTMS`, `oleylamine`, `none` | Critical for dispersion and biocompatibility claims. |
| zeta_potential_mV | numeric | mV | -60 to +60 | Report pH, ionic strength, and solvent. |
| crystal_structure | string | phase identification | `FCC`, `BCC`, `HCP`, `wurtzite`, `rutile`, `anatase`, `graphene (sp2)` | Report XRD conditions (Cu Kα, scan range, step size). |
| test_standard | string | standard number or lab method | `ISO 13321` (DLS), `ASTM B822` (particle size), `ISO 9277` (BET) | If lab method, describe instrument and settings. |
| test_temperature_degC | numeric | degC | 23 (room temp), 37 (biological), 500 (thermal stability) | Must match characterization condition. |
| aging_condition | string | exposure protocol | `UV 200h`, `thermal 300°C/50h`, `biological 37°C/7d` | Do not claim stability without exposure details. |
| replicate_count | integer | n | minimum 3 for DLS, minimum 10 particles for TEM sizing | If n < 3, use descriptive language only. |
| measured_property | categorical | property name | particle_size, zeta_potential, BET_surface_area, tensile_strength, thermal_conductivity, UV_absorption_peak, photoluminescence_intensity | Keep names consistent across datasets. |
| value | numeric | property-specific | measured value | Do not mix units in one column. |
| unit | string | property-specific | nm, mV, m²/g, MPa, W/m·K, nm, a.u. | Required for FAIR reuse. |

## Recommended Split Columns

For high-quality datasets, split compound fields:

- `hydrothermal_pressure_MPa`
- `calcination_temperature_degC`
- `calcination_time_h`
- `CVD_gas_flow_rate_sccm`
- `spin_coating_speed_rpm`
- `film_thickness_nm`
- `dispersion_solvent`
- `dispersion_concentration_mg_per_mL`
- `TEM_accelerating_voltage_kV`
- `XRD_2theta_range`

## Common Tests

- Particle size: TEM, DLS, XRD Scherrer, AFM (for 2D)
- Surface area: BET nitrogen adsorption (ISO 9277)
- Crystal structure: XRD, SAED (TEM)
- Morphology: TEM, SEM, AFM, HRTEM
- Surface chemistry: FTIR, Raman, XPS, TGA (grafting density)
- Optical: UV-Vis, photoluminescence (PL), Raman mapping
- Thermal: TGA, DSC (decomposition, phase transition)
- Mechanical: nanoindentation, tensile (nanocomposites)
- Electrical: four-point probe, Hall effect, impedance spectroscopy

## Boundary Rule

Particle size data alone do not prove size-property relationships. Size distribution (PDI or histogram), measurement method (TEM vs DLS), and surface chemistry must be reported before claiming size-dependent effects. Agglomeration state evidence (TEM at working concentration) is required before attributing properties to individual nanoparticles.
