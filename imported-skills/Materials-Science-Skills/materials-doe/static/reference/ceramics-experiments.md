# Ceramics Experiment Design Reference

## Typical factors and levels

| Factor | Low | Medium | High | Notes |
|---|---|---|---|---|
| Sintering temperature (°C) | 1400 | 1500 | 1600 | Dependent on ceramic system |
| Heating rate (°C/min) | 2 | 5 | 10 | Affects grain growth |
| Dwell time (h) | 1 | 2 | 4 | Longer → denser but coarser |
| Dopant content (wt%) | 0 | 0.5 | 2 | System-dependent optimum |
| Forming pressure (MPa) | 50 | 150 | 250 | Green density affects sintered density |

## Typical responses and measurement methods

| Response | Method | Standard | Units |
|---|---|---|---|
| Relative density | Archimedes | ASTM C373 / ISO 18754 | % of theoretical |
| Open/closed porosity | Archimedes | ASTM C373 | % |
| Linear shrinkage | Caliper (before/after) | — | % |
| Flexural strength | 3-point or 4-point bending | ASTM C1161 / ISO 14704 | MPa |
| Fracture toughness | SENB, SEPB, IF, CNB | ASTM C1421 | MPa·m^(1/2) |
| Vickers hardness | Indentation | ASTM C1327 / ISO 14705 | GPa |
| Weibull modulus | Maximum likelihood | ASTM C1239 | — |
| Thermal conductivity | Laser flash, guarded hot plate | ASTM E1461 | W m⁻¹ K⁻¹ |
| Thermal expansion | Dilatometry | ASTM E228 | 10⁻⁶ K⁻¹ |
| Grain size | Linear intercept | ASTM E112 | µm |

## Recommended experimental designs

### 1. Composition screening: Full factorial

**Purpose**: Identify which component significantly affects density/strength.
**Design**: 2^k factorial, where k = number of composition variables.
**Example**: 3 dopants × 2 levels = 8 runs + 2 center points.
**Analysis**: ANOVA, Pareto chart of standardized effects.

### 2. Sintering optimization: Central Composite Design (CCD)

**Purpose**: Find the optimal sintering T, ramp, and dwell for maximum density.
**Design**: CCD with 3 factors (T, ramp, dwell), 2^3 = 8 factorial + 6 axial + 2 center = 16 runs.
**Response surface**: Fit quadratic model; contour plot of density vs T and dwell.
**Verification**: Run 3 confirmation trials at predicted optimum.

### 3. Robust sintering: Taguchi L9

**Purpose**: Minimize sensitivity to uncontrollable factors (furnace variation, powder batch).
**Design**: L9 orthogonal array with 4 factors at 3 levels.
**Signal-to-noise**: Larger-the-better for density and strength.
**Confirmation**: Run at optimal levels; compare with initial condition.

### 4. Multi-component formulation: Mixture design

**Purpose**: Optimize ternary/ quaternary ceramic composition.
**Design**: Simplex centroid or D-optimal mixture design.
**Constraints**: Component fractions sum to 1; lower/upper bounds on each.
**Analysis**: Ternary contour plot of the target property.

## Replication and statistics

| Response | Minimum replicates | Notes |
|---|---|---|
| Density | 3 specimens | Per condition |
| Flexural strength | 10 specimens (30 recommended) | For Weibull analysis |
| Hardness | 5 indentations | Per specimen |
| Fracture toughness | 5 specimens | Valid KIC requires precrack verification |
| Thermal conductivity | 3 measurements | At each temperature |
| Grain size | ≥200 grains | From ≥3 SEM images |

## Standard reporting checklist

- [ ] Sintering profile: ramp rate, target T, dwell time, cooling rate, atmosphere
- [ ] Theoretical density and calculation basis
- [ ] Density measurement method (Archimedes, geometric, He pycnometry)
- [ ] XRD: 2θ range, step size, reference pattern source (ICDD/JCPDS numbers)
- [ ] SEM: accelerating voltage, working distance, magnification, scale bar
- [ ] Mechanical test: standard number, specimen geometry, span, crosshead speed
- [ ] Weibull: number of specimens, estimator method, confidence bounds

---

## Experiment Type 5: Sintering Process Optimization (RSM Template)

Optimize sintering parameters for maximum density and mechanical properties
using response surface methodology.

### Factors and Responses (Central Composite, 3 factors)

Face-centered CCD (α = 1) is used because sintering temperature and time
cannot be extrapolated beyond practical limits.

| Factor | Unit | Low (-1) | Center (0) | High (+1) |
|--------|------|----------|-----------|-----------|
| Sintering temperature | °C | 1400 | 1500 | 1600 |
| Heating rate | °C/min | 2 | 5 | 10 |
| Dwell time | h | 1 | 2 | 4 |

| Response | Unit | Standard |
|----------|------|----------|
| Relative density | % | ASTM C373 |
| Flexural strength | MPa | ASTM C1161 |
| Fracture toughness | MPa·m^(1/2) | ASTM C1421 |
| Vickers hardness | GPa | ASTM C1327 |
| Grain size | µm | ASTM E112 |

### Face-Centered CCD Design (20 runs, 3 factors)

| Run | Temp (A) | Rate (B) | Time (C) | Type |
|-----|---------|----------|----------|------|
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
2. ANOVA with backward elimination of non-significant terms
3. Check model diagnostics: R², adj-R², pred-R², lack-of-fit
4. Contour and surface plots for temperature vs time (at fixed heating rate)
5. Numerical optimization: maximize density and strength, minimize grain growth
6. Multi-response desirability optimization
7. Confirmation at 2-3 optimal conditions

---

## Experiment Type 6: Multi-Factor Sintering Screening (Plackett-Burman Template)

Screen many composition and processing factors to identify those most
affecting ceramic sintering behavior and final properties.

### Factors (L12 Plackett-Burman, 11 factors)

| Factor | Unit | Low (-) | High (+) |
|--------|------|---------|----------|
| A: Dopant type | — | Y₂O₃ | Al₂O₃ |
| B: Dopant content | wt% | 0.5 | 2.0 |
| C: Powder particle size | µm | 0.2 | 1.0 |
| D: Forming pressure | MPa | 50 | 200 |
| E: Binder content | wt% | 2 | 8 |
| F: Sintering temperature | °C | 1400 | 1600 |
| G: Heating rate | °C/min | 2 | 10 |
| H: Dwell time | h | 1 | 4 |
| I: Sintering atmosphere | — | Air | Vacuum |
| J: Cooling rate | °C/min | 5 | 20 |
| K: Post-sintering treatment | — | None | HIP |

### Responses

| Response | Unit | Standard |
|----------|------|----------|
| Relative density | % | ASTM C373 |
| Flexural strength | MPa | ASTM C1161 |
| Weibull modulus | — | ASTM C1239 |
| Hardness | GPa | ASTM C1327 |

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

1. Estimate main effects for density and strength
2. Compare Pareto charts across responses
3. Identify factors with the strongest influence on sintered properties
4. Typically 3-5 factors emerge as active
5. Plan follow-up factorial or RSM study on the key variables

---

## Experiment Type 7: Multi-Component Ceramic Formulation (Mixture Design Template)

Optimize multi-component ceramic composition using statistical mixture design.
Appropriate when component proportions sum to 100%.

### Components (3-component simplex centroid)

Example: Zirconia-toughened alumina (ZTA) system

| Component | Range | Typical |
|-----------|-------|---------|
| x₁: Al₂O₃ (matrix) | 70 – 95% | ~85% |
| x₂: ZrO₂ (toughener) | 5 – 20% | ~12% |
| x₃: Sintering aid (Y₂O₃/MgO) | 0.5 – 3% | ~1.5% |

**Constraint:** x₁ + x₂ + x₃ = 100% (by total composition mass)

Note: These are constrained components. For realistic bounds, use extreme
vertices design. Below is a standard simplex centroid for reference.

### Simplex Centroid Design (3 components, 7 runs)

| Run | x₁ Al₂O₃ | x₂ ZrO₂ | x₃ Aid | Description |
|-----|----------|---------|--------|-------------|
| 1 | 100% | 0% | 0% | Pure alumina (reference) |
| 2 | 0% | 100% | 0% | Pure zirconia (reference) |
| 3 | 0% | 0% | 100% | Pure aid (reference) |
| 4 | 50% | 50% | 0% | Al₂O₃-ZrO₂ binary |
| 5 | 50% | 0% | 50% | Al₂O₃-aid binary |
| 6 | 0% | 50% | 50% | ZrO₂-aid binary |
| 7 | 33.3% | 33.3% | 33.3% | Ternary blend |

### Constrained Version (Extreme Vertices Concept)

For the realistic constraints above (Al₂O₃ 70-95%, ZrO₂ 5-20%, aid 0.5-3%),
the feasible region is a small polygon. Representative points:

| Run | x₁ Al₂O₃ | x₂ ZrO₂ | x₃ Aid | Description |
|-----|----------|---------|--------|-------------|
| 1 | 94.5% | 5% | 0.5% | Max alumina, min ZrO₂, min aid |
| 2 | 92.5% | 5% | 2.5% | Max alumina, min ZrO₂, max aid |
| 3 | 79.5% | 20% | 0.5% | Min alumina, max ZrO₂, min aid |
| 4 | 77.5% | 20% | 2.5% | Min alumina, max ZrO₂, max aid |
| 5 | 86% | 12.5% | 1.5% | Center of feasible region |
| 6 | 87% | 10% | 3% | Interior check point |

Note: Calculate exact extreme vertices for your specific constraints.

### Responses

| Response | Unit | Standard |
|----------|------|----------|
| Relative density | % | ASTM C373 |
| Flexural strength | MPa | ASTM C1161 |
| Fracture toughness | MPa·m^(1/2) | ASTM C1421 |
| Hardness | GPa | ASTM C1327 |
| Weibull modulus | — | ASTM C1239 |

### Analysis Plan

1. Fit quadratic mixture model (special cubic if center point available)
2. ANOVA for significance of component effects and interactions
3. Ternary contour plots for each response
4. Multi-response optimization (desirability function)
5. Confirmation at optimal composition
