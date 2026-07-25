# Thermal Insulation Experiment Reference

Common experiment types, typical factor-response pairs, and standard references for thermal insulation materials research.

## Experiment Type 1: Thermal Conductivity Optimization

Minimize thermal conductivity while maintaining mechanical integrity and meeting fire-resistance requirements.

### Factors and Responses

| Factor | Unit | Typical Range |
|--------|------|---------------|
| Density (kg/m³) | kg/m³ | 20–200 |
| Porosity | % | 50–95 |
| Pore size | μm | 10–500 |
| Binder content (%) | % | 5–30 |
| Additive type | — | aerogel, hollow microspheres, vermiculite |
| Additive content (%) | % | 5–40 |
| Sample thickness (mm) | mm | 10–50 |

| Response | Unit | Standard |
|----------|------|----------|
| Thermal conductivity | W/(m·K) | ASTM C518 (heat flow meter) |
| Compressive strength | kPa | ASTM C165 |
| Flexural strength | kPa | ASTM C203 |
| Water absorption | kg/m² | ASTM C1104 |
| Fire rating | class | ASTM E119 / GB 8624 |
| Linear shrinkage | % | ASTM C356 |

### Standards

- ASTM C518 — Steady-state thermal transmission properties by heat flow meter
- ASTM C165 — Measuring compressive properties of thermal insulations
- ASTM C203 — Flexural properties of block-type thermal insulation
- ASTM C533 — Calcium silicate block and pipe thermal insulation
- GB/T 10295 — Determination of steady-state thermal resistance (Chinese, equivalent to ISO 8301)
- GB 8624 — Classification for burning behavior of building materials

## Experiment Type 2: Aerogel Composite Insulation

Optimize the formulation of aerogel-enhanced insulation materials (blanket, board, or coating).

### Factors and Responses

| Factor | Unit | Typical Range |
|--------|------|---------------|
| Aerogel content (%) | % | 10–60 |
| Aerogel particle size (mm) | mm | 0.1–5 |
| Binder type | — | cement, gypsum, polymer, fiber |
| Binder content (%) | % | 10–40 |
| Fiber reinforcement (%) | % | 0–5 |
| Pressing density (kg/m³) | kg/m³ | 80–200 |
| Curing temperature (°C) | °C | 20–80 |

| Response | Unit | Standard |
|----------|------|----------|
| Thermal conductivity | W/(m·K) | ASTM C518 |
| Compressive strength | kPa | ASTM C165 |
| Tensile strength | kPa | ASTM C686 |
| Hydrophobicity | contact angle | — |
| Density | kg/m³ | ASTM C303 |
| Service temperature | °C | — |

### Standards

- ASTM C1728 — Flexible aerogel insulation
- ASTM C518 — Thermal conductivity measurement
- ISO 9229 — Thermal insulation vocabulary
- GB/T 34336 — Aerogel composite insulation blanket (Chinese)

## Experiment Type 3: Foam Material Insulation

Optimize foaming parameters and formulation for polyurethane, phenolic, or cement-based foam insulation.

### Factors and Responses

| Factor | Unit | Typical Range |
|--------|------|---------------|
| Foaming agent type | — | pentane, HFC-245fa, water, CO₂ |
| Foaming agent content (%) | % | 2–15 |
| Surfactant content (%) | % | 0.5–3 |
| Catalyst content (%) | % | 0.1–2 |
| Isocyanate index | — | 80–120 (for PU) |
| Mixing ratio (A:B) | — | 1:1 to 1:2 |
| Mold temperature (°C) | °C | 20–60 |
| Free rise density (kg/m³) | kg/m³ | 25–60 |

| Response | Unit | Standard |
|----------|------|----------|
| Thermal conductivity | W/(m·K) | ASTM C518 |
| Closed-cell content | % | ASTM D6226 |
| Density | kg/m³ | ASTM D1622 |
| Compressive strength | kPa | ASTM D1621 |
| Dimensional stability | % | ASTM D2126 |
| Water vapor permeability | perm | ASTM E96 |
| Oxygen index | % | ASTM D2863 |
| Flame spread index | — | ASTM E84 |

### Standards

- ASTM D1621 — Compressive properties of rigid cellular plastics
- ASTM D1622 — Apparent density of rigid cellular plastics
- ASTM D2126 — Dimensional stability of rigid cellular plastics
- ASTM D6226 — Open-cell content of rigid cellular plastics
- ASTM D2863 — Minimum oxygen concentration to sustain candle-like combustion
- GB/T 8813 — Rigid cellular plastics compression test method (Chinese)
- GB/T 10801.1 — Rigid polyurethane foam for thermal insulation (Chinese)

## Typical Orthogonal Setup: Foam Insulation (L9)

4 factors, 3 levels each, 9 runs.

| Factor | Level 1 | Level 2 | Level 3 |
|--------|---------|---------|---------|
| Foaming agent content (%) | 4 | 7 | 10 |
| Surfactant content (%) | 0.8 | 1.2 | 1.6 |
| Catalyst content (%) | 0.3 | 0.6 | 1.0 |
| Mold temperature (°C) | 25 | 35 | 45 |

| Run | Foaming (%) | Surfactant (%) | Catalyst (%) | Temp (°C) |
|-----|-------------|---------------|--------------|-----------|
| 1 | 4 | 0.8 | 0.3 | 25 |
| 2 | 4 | 1.2 | 0.6 | 35 |
| 3 | 4 | 1.6 | 1.0 | 45 |
| 4 | 7 | 0.8 | 0.6 | 45 |
| 5 | 7 | 1.2 | 1.0 | 25 |
| 6 | 7 | 1.6 | 0.3 | 35 |
| 7 | 10 | 0.8 | 1.0 | 35 |
| 8 | 10 | 1.2 | 0.3 | 45 |
| 9 | 10 | 1.6 | 0.6 | 25 |

Responses: thermal conductivity, density, compressive strength, closed-cell content.

---

## Experiment Type 5: Thermal Insulation Formulation Optimization (RSM Template)

Optimize insulation material formulation for minimum thermal conductivity
and balanced mechanical properties using response surface methodology.

### Factors and Responses (Central Composite, 3 factors)

Face-centered CCD for insulation material formulation and processing.

| Factor | Unit | Low (-1) | Center (0) | High (+1) |
|--------|------|----------|-----------|-----------|
| Porogen content | wt% | 5 | 15 | 25 |
| Fiber content | wt% | 5 | 15 | 25 |
| Curing temperature | °C | 80 | 120 | 160 |

| Response | Unit | Standard |
|----------|------|----------|
| Thermal conductivity | W/m·K | ASTM C518 |
| Compressive strength | MPa | ASTM C165 |
| Density | kg/m³ | ASTM C303 |
| Water absorption | % | ASTM C272 |
| Flexural strength | MPa | ASTM C203 |

### Face-Centered CCD Design (20 runs, 3 factors)

| Run | Porogen (A) | Fiber (B) | Temp (C) | Type |
|-----|------------|-----------|----------|------|
| 1 | -1 | -1 | -1 | factorial (corner) |
| 2 | +1 | -1 | -1 | factorial (corner) |
| 3 | -1 | +1 | -1 | factorial (corner) |
| 4 | +1 | +1 | -1 | factorial (corner) |
| 5 | -1 | -1 | +1 | factorial (corner) |
| 6 | +1 | -1 | +1 | factorial (corner) |
| 7 | -1 | +1 | +1 | factorial (corner) |
| 8 | +1 | +1 | +1 | factorial (corner) |
| 9 | -1 | 0 | 0 | axial (face center) |
| 10 | +1 | 0 | 0 | axial (face center) |
| 11 | 0 | -1 | 0 | axial (face center) |
| 12 | 0 | +1 | 0 | axial (face center) |
| 13 | 0 | 0 | -1 | axial (face center) |
| 14 | 0 | 0 | +1 | axial (face center) |
| 15 | 0 | 0 | 0 | center |
| 16 | 0 | 0 | 0 | center |
| 17 | 0 | 0 | 0 | center |
| 18 | 0 | 0 | 0 | center |
| 19 | 0 | 0 | 0 | center |
| 20 | 0 | 0 | 0 | center |

### Analysis Plan

1. Fit full quadratic model for each response
2. ANOVA with backward elimination
3. Check model diagnostics: R², adj-R², lack-of-fit
4. Contour and surface plots for porogen vs fiber content
5. Multi-response optimization: minimize thermal conductivity, maintain strength
6. Desirability function optimization
7. Confirmation at 2-3 optimal formulations

---

## Experiment Type 6: Insulation Material Factor Screening (Plackett-Burman Template)

Screen many formulation and processing factors to identify those most
affecting insulation performance.

### Factors (L12 Plackett-Burman, 11 factors)

| Factor | Unit | Low (-) | High (+) |
|--------|------|---------|----------|
| A: Matrix material | — | Cement | Gypsum |
| B: Porogen type | — | EPS | Perlite |
| C: Porogen content | wt% | 5 | 25 |
| D: Fiber type | — | Glass | Cellulose |
| E: Fiber content | wt% | 2 | 10 |
| F: Binder content | wt% | 5 | 20 |
| G: Foaming agent content | wt% | 0.5 | 3 |
| H: Curing temperature | °C | 80 | 160 |
| I: Curing time | h | 4 | 24 |
| J: Drying temperature | °C | 60 | 120 |
| K: Surface treatment | — | None | Silane |

### Responses

| Response | Unit | Standard |
|----------|------|----------|
| Thermal conductivity | W/m·K | ASTM C518 |
| Compressive strength | MPa | ASTM C165 |
| Density | kg/m³ | ASTM C303 |
| Water absorption | % | ASTM C272 |
| Fire resistance | min | ASTM E119 |

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

1. Calculate main effects for thermal conductivity and strength
2. Pareto chart analysis across responses
3. Identify factors with strongest influence
4. Typically 3-5 factors emerge as active
5. Follow up with RSM on key variables
6. Special attention to conductivity-strength trade-off

---

## Experiment Type 7: Multi-Component Insulation Formulation (Mixture Design Template)

Optimize multi-component thermal insulation formulation
using statistical mixture design.

### Components (4-component simplex centroid)

Example: Multi-component insulation system

| Component | Range | Typical |
|-----------|-------|---------|
| x₁: Matrix (cement/gypsum/resin) | 40 – 70% | ~55% |
| x₂: Lightweight filler (perlite/vermiculite) | 15 – 35% | ~25% |
| x₃: Fiber reinforcement | 3 – 12% | ~7% |
| x₄: Binder/additive | 3 – 10% | ~6% |

**Constraint:** x₁ + x₂ + x₃ + x₄ = 100% (by total mass)

Note: With constraints, use extreme vertices design rather than standard simplex.
Below is a standard simplex centroid for reference.

### Simplex Centroid Design (4 components, 15 runs)

| Run | x₁ Matrix | x₂ Filler | x₃ Fiber | x₄ Binder | Description |
|-----|----------|-----------|----------|-----------|-------------|
| 1 | 100% | 0% | 0% | 0% | Pure matrix |
| 2 | 0% | 100% | 0% | 0% | Pure filler (ref) |
| 3 | 0% | 0% | 100% | 0% | Pure fiber (ref) |
| 4 | 0% | 0% | 0% | 100% | Pure binder (ref) |
| 5 | 50% | 50% | 0% | 0% | Matrix-filler binary |
| 6 | 50% | 0% | 50% | 0% | Matrix-fiber binary |
| 7 | 50% | 0% | 0% | 50% | Matrix-binder binary |
| 8 | 0% | 50% | 50% | 0% | Filler-fiber binary |
| 9 | 0% | 50% | 0% | 50% | Filler-binder binary |
| 10 | 0% | 0% | 50% | 50% | Fiber-binder binary |
| 11 | 33.3% | 33.3% | 33.3% | 0% | Ternary 1-2-3 |
| 12 | 33.3% | 33.3% | 0% | 33.3% | Ternary 1-2-4 |
| 13 | 33.3% | 0% | 33.3% | 33.3% | Ternary 1-3-4 |
| 14 | 0% | 33.3% | 33.3% | 33.3% | Ternary 2-3-4 |
| 15 | 25% | 25% | 25% | 25% | Overall centroid |

### Responses

| Response | Unit | Standard |
|----------|------|----------|
| Thermal conductivity | W/m·K | ASTM C518 |
| Compressive strength | MPa | ASTM C165 |
| Density | kg/m³ | ASTM C303 |
| Flexural strength | MPa | ASTM C203 |
| Water absorption | % | ASTM C272 |

### Analysis Plan

1. Fit quadratic mixture model (special cubic if ternary points available)
2. ANOVA for component effects and interactions
3. Ternary contour plots for key combinations
4. Multi-response optimization using desirability function
5. Confirmation at optimal formulation
