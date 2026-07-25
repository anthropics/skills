# Functional Materials Experiment Reference

Common experiment types, typical factor-response pairs, and standard references for semiconductor, dielectric, piezoelectric, and photonic material research.

## Experiment Type 1: Dielectric Ceramic Sintering Optimization

Optimize sintering conditions for maximum density and dielectric performance.

### Factors and Responses

| Factor | Unit | Typical Range |
|--------|------|---------------|
| Sintering temperature (°C) | °C | 1100–1400 |
| Sintering time (h) | h | 2–12 |
| Heating rate (°C/min) | °C/min | 2–10 |
| Atmosphere | — | air, O₂, N₂ |
| Dopant concentration (mol%) | mol% | 0–5 |

| Response | Unit | Standard |
|----------|------|----------|
| Relative density | % | Archimedes |
| Grain size | µm | SEM intercept (ASTM E112) |
| Dielectric constant (εr) | — | IEC 60250 |
| Loss tangent (tan δ) | — | IEC 60250 |
| Curie temperature (Tc) | °C | DSC or εr vs T |

### Standards

- IEC 60250 — Dielectric constant and loss measurement
- IEEE 176 — Piezoelectric crystals
- ASTM E112 — Grain size determination

## Experiment Type 2: Thin Film Deposition for Optoelectronics

Optimize deposition and annealing parameters for optical and electrical performance.

### Factors and Responses

| Factor | Unit | Typical Range |
|--------|------|---------------|
| Deposition method | — | PLD, sputtering, spin coating, MBE, CVD |
| Substrate temperature (°C) | °C | 25–800 |
| Annealing temperature (°C) | °C | 200–600 |
| Annealing atmosphere | — | air, N₂, O₂, vacuum |
| Film thickness (nm) | nm | 50–2000 |
| Doping level (mol%) | mol% | 0–10 |

| Response | Unit | Standard |
|----------|------|----------|
| Optical band gap | eV | UV-Vis (Tauc plot) |
| Transmittance (550 nm) | % | UV-Vis |
| Sheet resistance | Ω/sq | four-point probe (ASTM F390) |
| Carrier concentration | cm⁻³ | Hall effect |
| Mobility | cm²/V·s | Hall effect |
| Surface roughness (Ra) | nm | AFM |

### Standards

- ASTM F390 — Sheet resistance by four-point probe
- ASTM E308 — CIE color computation
- IEC 62805 — Measurement of PV module transmittance

## Experiment Type 3: Piezoelectric Performance Optimization

Optimize composition, poling, and processing for maximum piezoelectric response.

### Factors and Responses

| Factor | Unit | Typical Range |
|--------|------|---------------|
| Composition (dopant x) | mol% | 0–10 |
| Sintering temperature (°C) | °C | 1100–1350 |
| Poling field (kV/cm) | kV/cm | 10–60 |
| Poling temperature (°C) | °C | 25–150 |
| Poling time (min) | min | 5–30 |

| Response | Unit | Standard |
|----------|------|----------|
| d₃₃ | pC/N | Berlincourt meter (IEEE 176) |
| d₃₁ | pC/N | impedance method |
| Coupling factor (k₃₃, kₚ) | — | IEEE 176 |
| Dielectric constant (εr) | — | IEC 60250 |
| Coercive field (Ec) | kV/cm | P-E loop |
| Remanent polarization (Pr) | µC/cm² | P-E loop |

### Standards

- IEEE 176 — Piezoelectric crystals
- IEC 61094 — Measurement microphones
- IEC 60250 — Dielectric measurements

## Typical Orthogonal Setup: BaTiO₃ Doping (L9)

4 factors, 3 levels each, 9 runs.

| Factor | Level 1 | Level 2 | Level 3 |
|--------|---------|---------|---------|
| Nb doping (mol%) | 0.5 | 1.0 | 2.0 |
| Sintering temp (°C) | 1250 | 1300 | 1350 |
| Sintering time (h) | 2 | 4 | 6 |
| Atmosphere | air | O₂ | N₂ |

| Run | Nb (mol%) | Temp (°C) | Time (h) | Atm |
|-----|-----------|-----------|----------|-----|
| 1 | 0.5 | 1250 | 2 | air |
| 2 | 0.5 | 1300 | 4 | O₂ |
| 3 | 0.5 | 1350 | 6 | N₂ |
| 4 | 1.0 | 1250 | 4 | N₂ |
| 5 | 1.0 | 1300 | 6 | air |
| 6 | 1.0 | 1350 | 2 | O₂ |
| 7 | 2.0 | 1250 | 6 | O₂ |
| 8 | 2.0 | 1300 | 2 | N₂ |
| 9 | 2.0 | 1350 | 4 | air |

Responses: relative density, grain size, dielectric constant, loss tangent, d₃₃.


---

## Experiment Type 5: Piezoelectric Ceramic Formulation Optimization (RSM Template)

Optimize piezoelectric ceramic formulation and sintering parameters for maximum
piezoelectric coefficient and dielectric properties using response surface methodology.

### Factors and Responses (Central Composite, 4 factors)

Face-centered CCD for piezoelectric ceramics formulation and processing.

| Factor | Unit | Low (-1) | Center (0) | High (+1) |
|--------|------|----------|-----------|-----------|
| Dopant content | mol% | 0.5 | 1.5 | 2.5 |
| Sintering temperature | °C | 1100 | 1200 | 1300 |
| Dwell time | h | 1 | 3 | 6 |
| Heating rate | °C/min | 2 | 5 | 10 |

| Response | Unit | Standard |
|----------|------|----------|
| Piezoelectric coefficient d₃₃ | pC/N | ASTM E1453 |
| Electromechanical coupling kₚ | — | IEEE 176 |
| Dielectric constant εᵣ | — | ASTM D150 |
| Mechanical quality factor Qₘ | — | IEEE 176 |
| Density | g/cm³ | Archimedes |

### Face-Centered CCD Design (30 runs, 4 factors)

| Run | Dopant (A) | Temp (B) | Time (C) | Rate (D) | Type |
|-----|------------|---------|----------|----------|------|
| 1 | -1 | -1 | -1 | -1 | factorial |
| 2 | +1 | -1 | -1 | -1 | factorial |
| 3 | -1 | +1 | -1 | -1 | factorial |
| 4 | +1 | +1 | -1 | -1 | factorial |
| 5 | -1 | -1 | +1 | -1 | factorial |
| 6 | +1 | -1 | +1 | -1 | factorial |
| 7 | -1 | +1 | +1 | -1 | factorial |
| 8 | +1 | +1 | +1 | -1 | factorial |
| 9 | -1 | -1 | -1 | +1 | factorial |
| 10 | +1 | -1 | -1 | +1 | factorial |
| 11 | -1 | +1 | -1 | +1 | factorial |
| 12 | +1 | +1 | -1 | +1 | factorial |
| 13 | -1 | -1 | +1 | +1 | factorial |
| 14 | +1 | -1 | +1 | +1 | factorial |
| 15 | -1 | +1 | +1 | +1 | factorial |
| 16 | +1 | +1 | +1 | +1 | factorial |
| 17 | -1 | 0 | 0 | 0 | axial (face) |
| 18 | +1 | 0 | 0 | 0 | axial (face) |
| 19 | 0 | -1 | 0 | 0 | axial (face) |
| 20 | 0 | +1 | 0 | 0 | axial (face) |
| 21 | 0 | 0 | -1 | 0 | axial (face) |
| 22 | 0 | 0 | +1 | 0 | axial (face) |
| 23 | 0 | 0 | 0 | -1 | axial (face) |
| 24 | 0 | 0 | 0 | +1 | axial (face) |
| 25 | 0 | 0 | 0 | 0 | center |
| 26 | 0 | 0 | 0 | 0 | center |
| 27 | 0 | 0 | 0 | 0 | center |
| 28 | 0 | 0 | 0 | 0 | center |
| 29 | 0 | 0 | 0 | 0 | center |
| 30 | 0 | 0 | 0 | 0 | center |

### Analysis Plan

1. Fit full quadratic model for each piezoelectric response
2. ANOVA with backward elimination
3. Check model diagnostics: R², adj-R², lack-of-fit
4. Contour and surface plots for dopant content vs temperature
5. Multi-response optimization: maximize d₃₃ and kₚ, maintain εᵣ in range
6. Desirability function optimization
7. Confirmation at 2-3 optimal conditions

---

## Experiment Type 6: Multi-Factor Screening for Battery Electrode Screening (Plackett-Burman Template)

Screen many formulation and processing factors for battery electrode
performance optimization.

### Factors (L12 Plackett-Burman, 11 factors)

| Factor | Unit | Low (-) | High (+) |
|--------|------|---------|----------|
| A: Active material type | — | NMC | LFP |
| B: Active material content | wt% | 85 | 95 |
| C: Conductive carbon content | wt% | 1 | 5 |
| D: Binder content | wt% | 2 | 8 |
| E: Carbon type | — | Super P | CNT |
| F: Binder type | — | PVDF | SBR/CMC |
| G: Coating thickness | µm | 50 | 150 |
| H: Drying temperature | °C | 80 | 120 |
| I: Calendaring pressure | MPa | 10 | 50 |
| J: Electrolyte type | — | LiPF₆ EC/DMC | LiFSI EC/EMC |
| K: Formation rate | C-rate | 0.1 | 1.0 |

### Responses

| Response | Unit | Standard |
|----------|------|----------|
| Specific capacity | mAh/g | Galvanostatic cycling |
| Rate capability (1C/0.2C) | % | Rate test |
| Cycle life (100 cycles) | % | Cycle test |
| Internal resistance | Ω | EIS |
| Coulombic efficiency | % | Galvanostatic cycling |

### L12 Design Matrix

| Run | A | B | C | D | E | F | G | H | I | J | K |
|-----|---|---|---|---|---|---|---|---|---|---|---|
| 1 | + | + | - | + | + | + | - | - | - | + | - |
| 2 | - | + | + | - | + | + | + | - | - | - | + |
| 3 | + | - | + | + | - | + | + | + | - | - | - |
| 4 | - | + | - | + | + | - | + | + | + | - | - |
| 5 | - | - | + | - | + | + | - | + | + | + | - |
| 6 | - | - | - | + | - | + | + | - | + | + | + |
| 7 | + | - | - | - | + | - | + | + | - | + | + |
| 8 | + | + | - | - | - | + | - | + | + | - | + |
| 9 | + | + | + | - | - | - | + | - | + | + | - |
| 10 | - | + | + | + | - | - | - | + | - | + | + |
| 11 | + | - | + | + | + | - | - | - | + | - | + |
| 12 | - | - | - | - | - | - | - | - | - | - | - |

### Analysis Guidance

1. Calculate main effects for capacity, rate capability, and cycle life
2. Pareto chart across responses
3. Identify most influential formulation vs processing factors
4. Typically 3-5 factors emerge as active
5. Plan follow-up RSM on key variables

---

## Experiment Type 7: Multi-Component Piezoelectric Composition (Mixture Design Template)

Optimize multi-component piezoelectric ceramic composition
using statistical mixture design.

### Components (3-component simplex centroid)

Example: PZT-based multi-component system

| Component | Range | Typical |
|-----------|-------|---------|
| x₁: PZT base (Pb(Zr,Ti)O₃ | 85 – 98% | ~94% |
| x₂: Dopant A (Nb/Sb/Bi) | 1 – 8% | ~4% |
| x₃: Dopant B (Mn/Co/Fe) | 0.5 – 3% | ~2% |

**Constraint:** x₁ + x₂ + x₃ = 100% (by mole percent)

Note: These are constrained components. For realistic bounds, use extreme
vertices design. Below is a standard simplex centroid for reference.

### Simplex Centroid Design (3 components, 7 runs)

| Run | x₁ Base | x₂ Dopant A | x₃ Dopant B | Description |
|-----|----------|------------|-------------|-------------|
| 1 | 100% | 0% | 0% | Undoped base |
| 2 | 0% | 100% | 0% | Pure dopant A (ref) |
| 3 | 0% | 0% | 100% | Pure dopant B (ref) |
| 4 | 50% | 50% | 0% | Base-A binary |
| 5 | 50% | 0% | 50% | Base-B binary |
| 6 | 0% | 50% | 50% | A-B binary |
| 7 | 33.3% | 33.3% | 33.3% | Ternary blend |

### Constrained Version (Feasible Region Points)

For realistic constraints (base 85-98%, dopant A 1-8%, dopant B 0.5-3%):

| Run | x₁ Base | x₂ Dopant A | x₃ Dopant B | Description |
|-----|----------|------------|-------------|-------------|
| 1 | 98.5% | 1% | 0.5% | Max base, min A, min B |
| 2 | 96% | 1% | 3% | Max base-min A, max B |
| 3 | 91.5% | 8% | 0.5% | Min base, max A, min B |
| 4 | 89% | 8% | 3% | Min base, max A, max B |
| 5 | 93.8% | 4.5% | 1.75% | Center of feasible region |

Note: Calculate exact extreme vertices for your specific constraints.

### Responses

| Response | Unit | Standard |
|----------|------|----------|
| d₃₃ | pC/N | ASTM E1453 |
| kₚ | — | IEEE 176 |
| εᵣ | — | ASTM D150 |
| Qₘ | — | IEEE 176 |
| T_Curie | °C | Dielectric measurement |

### Analysis Plan

1. Fit quadratic mixture model
2. ANOVA for component effects and interactions
3. Ternary contour plots for each response
4. Multi-response optimization using desirability function
5. Confirmation at optimal composition
