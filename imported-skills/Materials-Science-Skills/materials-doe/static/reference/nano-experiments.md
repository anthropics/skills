# Nano Experiment Reference

Common experiment types, typical factor-response pairs, and standard references for nanomaterial research.

## Experiment Type 1: Nanoparticle Synthesis Optimization

Control size, morphology, and monodispersity of nanoparticles via wet-chemical synthesis.

### Factors and Responses

| Factor | Unit | Typical Range |
|--------|------|---------------|
| Precursor concentration (mol/L) | mol/L | 0.001–0.5 |
| Reducing/capping agent ratio | — | 0.5–10 (agent:precursor) |
| Reaction temperature (°C) | °C | 25–300 |
| Reaction time (min) | min | 5–720 |
| pH | — | 2–12 |
| Stirring rate (rpm) | rpm | 200–1500 |

| Response | Unit | Standard |
|----------|------|----------|
| Mean particle size | nm | TEM / DLS (ISO 13321) |
| Polydispersity index (PDI) | — | DLS |
| Surface area (BET) | m²/g | ISO 9277 |
| Zeta potential | mV | electrophoretic light scattering |
| Yield | % | gravimetric |

### Standards

- ISO 13321 — Particle size analysis by DLS
- ISO 9277 — BET specific surface area
- ISO 22412 — Particle size analysis by DLS (updated)
- ASTM B822 — Particle size by light scattering

## Experiment Type 2: Nanocomposite Preparation and Property Enhancement

Evaluate the effect of nanofiller loading, dispersion method, and surface treatment on polymer or ceramic matrix composites.

### Factors and Responses

| Factor | Unit | Typical Range |
|--------|------|---------------|
| Filler type | — | MMT clay, nano-SiO₂, CNT, graphene, nano-Al₂O₃, nano-TiO₂ |
| Filler loading (wt%) | wt% | 0.1–10 (nano), 5–50 (micro) |
| Surface treatment | — | silane, surfactant, polymer grafting, acid treatment |
| Dispersion method | — | ultrasonication, high-shear mixing, three-roll mill, in-situ polymerization |
| Dispersion time (min) | min | 5–120 |
| Matrix type | — | epoxy, PP, PA6, HDPE, PVA, alumina |

| Response | Unit | Standard |
|----------|------|----------|
| Tensile strength | MPa | ASTM D638 |
| Tensile modulus | GPa | ASTM D638 |
| Thermal conductivity | W/m·K | ASTM D5930 / laser flash |
| Tg (DSC) | °C | ASTM D3418 |
| Barrier permeability | cm³·mm/m²·d·atm | ASTM D1434 |
| Filler dispersion quality | — | TEM image rating |

### Standards

- ASTM D638 — Tensile properties
- ASTM D3418 — Tg by DSC
- ASTM D5930 — Thermal conductivity of plastics
- ASTM D1434 — Gas transmission rate

## Experiment Type 3: Thin Film Deposition and Characterization

Optimize thin film deposition parameters for optical, electrical, or functional coatings.

### Factors and Responses

| Factor | Unit | Typical Range |
|--------|------|---------------|
| Deposition method | — | spin coating, dip coating, sputtering, CVD, ALD, PLD |
| Substrate type | — | Si wafer, glass, ITO, FTO, PET, sapphire |
| Deposition temperature (°C) | °C | 25–800 |
| Deposition time (min) | min | 1–120 |
| Precursor/Target | — | solution, solid target, gas precursor |
| Annealing condition | — | none, 300°C/1h in air, 500°C/2h in N₂ |

| Response | Unit | Standard |
|----------|------|----------|
| Film thickness | nm | profilometer / ellipsometry |
| Surface roughness (Ra) | nm | AFM |
| Optical band gap | eV | UV-Vis (Tauc plot) |
| Sheet resistance | Ω/sq | four-point probe |
| Transmittance (550 nm) | % | UV-Vis spectrophotometry |
| Crystallinity | — | XRD |

### Standards

- ISO 4524 — Electrodeposited metallic coatings
- ASTM E284 — Terminology of appearance
- ASTM F390 — Sheet resistance by four-point probe

## Typical Orthogonal Setup: AgNP Synthesis (L9)

4 factors, 3 levels each, 9 runs.

| Factor | Level 1 | Level 2 | Level 3 |
|--------|---------|---------|---------|
| AgNO₃ concentration (mmol/L) | 5 | 10 | 20 |
| Citrate:Ag molar ratio | 1.5 | 3.0 | 5.0 |
| Reaction temperature (°C) | 60 | 80 | 100 |
| Reaction time (min) | 15 | 30 | 60 |

| Run | AgNO₃ (mmol/L) | Citrate:Ag | Temp (°C) | Time (min) |
|-----|----------------|------------|-----------|------------|
| 1 | 5 | 1.5 | 60 | 15 |
| 2 | 5 | 3.0 | 80 | 30 |
| 3 | 5 | 5.0 | 100 | 60 |
| 4 | 10 | 1.5 | 80 | 60 |
| 5 | 10 | 3.0 | 100 | 15 |
| 6 | 10 | 5.0 | 60 | 30 |
| 7 | 20 | 1.5 | 100 | 30 |
| 8 | 20 | 3.0 | 60 | 60 |
| 9 | 20 | 5.0 | 80 | 15 |

Responses: mean particle size, PDI, zeta potential, UV-Vis peak wavelength.

---

## Experiment Type 5: Nanoparticle Synthesis Optimization (RSM Template)

Optimize nanoparticle synthesis parameters for controlled particle size,
size distribution, and yield using response surface methodology.

### Factors and Responses (Box-Behnken, 4 factors)

| Factor | Unit | Low (-1) | Center (0) | High (+1) |
|--------|------|----------|-----------|-----------|
| Precursor concentration | mol/L | 0.05 | 0.15 | 0.25 |
| Reaction temperature | °C | 60 | 80 | 100 |
| Reaction time | h | 2 | 6 | 12 |
| Surfactant/precursor ratio | mol/mol | 0.05 | 0.15 | 0.25 |

| Response | Unit | Measurement |
|----------|------|-------------|
| Average particle size | nm | DLS / TEM |
| Size distribution (PDI) | — | DLS |
| Yield | % | Gravimetric |
| Zeta potential | mV | Zeta analyzer |
| Specific surface area | m²/g | BET |

### Box-Behnken Design (27 runs, 4 factors)

Use the standard 4-factor BBD matrix in `static/core/response-surface.md` with:
A = precursor concentration, B = reaction temperature, C = reaction time,
D = reagent ratio. The design has 24 edge-midpoint runs plus 3 center points;
each non-center run varies exactly two factors at ±1 and holds the other two at 0.

### Analysis Plan

1. Fit quadratic model for each response
2. ANOVA with backward elimination
3. Check model diagnostics: R², adj-R², lack-of-fit
4. Response surface and contour plots for key factor pairs
5. Multi-response optimization: target particle size, minimize PDI, maximize yield
6. Desirability function optimization
7. Confirmation at optimal synthesis conditions

---

## Experiment Type 6: Nanomaterial Synthesis Factor Screening (Plackett-Burman Template)

Screen many synthesis and processing factors to identify those most
affecting nanomaterial properties.

### Factors (L12 Plackett-Burman, 11 factors)

| Factor | Unit | Low (-) | High (+) |
|--------|------|---------|----------|
| A: Precursor type | — | Nitrate | Chloride |
| B: Precursor concentration | mol/L | 0.05 | 0.25 |
| C: Surfactant type | — | CTAB | PVP |
| D: Surfactant concentration | mol/L | 0.01 | 0.1 |
| E: pH | — | 5 | 10 |
| F: Reaction temperature | °C | 60 | 100 |
| G: Reaction time | h | 2 | 12 |
| H: Stirring speed | rpm | 200 | 800 |
| I: Drying temperature | °C | 60 | 120 |
| J: Calcination temperature | °C | 300 | 600 |
| K: Post-treatment | — | None | Hydrothermal |

### Responses

| Response | Unit | Measurement |
|----------|------|-------------|
| Average particle size | nm | DLS / TEM |
| Specific surface area | m²/g | BET |
| Crystallite size | nm | XRD (Scherrer) |
| Yield | % | Gravimetric |
| Zeta potential | mV | Zeta analyzer |

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

1. Estimate main effects for particle size, surface area, and yield
2. Pareto chart analysis across responses
3. Identify factors with strongest influence
4. Typically 3-5 factors emerge as active
5. Follow up with RSM on key variables

---

## Experiment Type 7: Multi-Component Nanocomposite (Mixture Design Template)

Optimize multi-component nanocomposite formulation
using statistical mixture design.

### Components (4-component simplex centroid)

Example: Multi-component nanocomposite system

| Component | Range | Typical |
|-----------|-------|---------|
| x₁: Matrix material (polymer/ceramic) | 60 – 90% | ~75% |
| x₂: Nanoparticle filler | 5 – 25% | ~15% |
| x₃: Dispersant/surfactant | 0.5 – 5% | ~2% |
| x₄: Crosslinker/binder | 2 – 10% | ~5% |

**Constraint:** x₁ + x₂ + x₃ + x₄ = 100% (by total mass)

Note: With constraints, use extreme vertices design rather than standard simplex.
Below is a standard simplex centroid for reference.

### Simplex Centroid Design (4 components, 15 runs)

| Run | x₁ Matrix | x₂ Nanoparticle | x₃ Dispersant | x₄ Binder | Description |
|-----|----------|-----------------|---------------|-----------|-------------|
| 1 | 100% | 0% | 0% | 0% | Pure matrix |
| 2 | 0% | 100% | 0% | 0% | Pure nanoparticle (ref) |
| 3 | 0% | 0% | 100% | 0% | Pure dispersant (ref) |
| 4 | 0% | 0% | 0% | 100% | Pure binder (ref) |
| 5 | 50% | 50% | 0% | 0% | Matrix-filler binary |
| 6 | 50% | 0% | 50% | 0% | Matrix-dispersant binary |
| 7 | 50% | 0% | 0% | 50% | Matrix-binder binary |
| 8 | 0% | 50% | 50% | 0% | Filler-dispersant binary |
| 9 | 0% | 50% | 0% | 50% | Filler-binder binary |
| 10 | 0% | 0% | 50% | 50% | Dispersant-binder binary |
| 11 | 33.3% | 33.3% | 33.3% | 0% | Ternary 1-2-3 |
| 12 | 33.3% | 33.3% | 0% | 33.3% | Ternary 1-2-4 |
| 13 | 33.3% | 0% | 33.3% | 33.3% | Ternary 1-3-4 |
| 14 | 0% | 33.3% | 33.3% | 33.3% | Ternary 2-3-4 |
| 15 | 25% | 25% | 25% | 25% | Overall centroid |

### Responses

| Response | Unit | Measurement |
|----------|------|-------------|
| Mechanical strength | MPa | Tensile/flexural |
| Electrical conductivity | S/m | Four-point probe |
| Thermal conductivity | W/m·K | Laser flash |
| Particle dispersion quality | — | TEM/SEM image analysis |
| Optical transmittance | % | UV-Vis |

### Analysis Plan

1. Fit quadratic mixture model (special cubic if ternary points available)
2. ANOVA for component effects and interactions
3. Ternary contour plots for key combinations
4. Multi-response optimization using desirability function
5. Confirmation at optimal formulation
