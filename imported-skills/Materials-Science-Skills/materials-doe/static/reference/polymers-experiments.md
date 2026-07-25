# Polymers Experiment Reference

Common experiment types, typical factor-response pairs, and standard references for polymer, rubber, and polymer composite research.

## Experiment Type 1: Injection Molding Process Optimization

Optimize processing parameters to maximize mechanical performance of injection-molded thermoplastic parts.

### Factors and Responses

| Factor | Unit | Typical Range |
|--------|------|---------------|
| Melt temperature (°C) | °C | 200–300 (PP), 260–320 (PA6), 300–380 (PEEK) |
| Mold temperature (°C) | °C | 20–120 |
| Injection speed (mm/s) | mm/s | 20–150 |
| Holding pressure (MPa) | MPa | 30–100 |
| Cooling time (s) | s | 10–60 |

| Response | Unit | Standard |
|----------|------|----------|
| Tensile strength | MPa | ASTM D638 / ISO 527 |
| Elongation at break | % | ASTM D638 / ISO 527 |
| Impact strength (Izod) | J/m | ASTM D256 |
| Warpage | mm | visual / CMM |
| Surface roughness | µm | profilometer |

### Standards

- ASTM D638 — Tensile properties of plastics
- ISO 527 — Tensile test for plastics
- ASTM D256 — Izod impact resistance
- ISO 294 — Injection molding test specimens

## Experiment Type 2: Filler Reinforcement and Interface Design

Evaluate the effect of filler type, content, and surface treatment on mechanical and thermal properties of polymer composites.

### Factors and Responses

| Factor | Unit | Typical Range |
|--------|------|---------------|
| Filler type | — | glass fiber, carbon fiber, nano-SiO2, CNT, clay, CaCO3, graphene |
| Filler content (wt%) | wt% | 5–50 (micro), 0.1–5 (nano) |
| Surface treatment | — | untreated, silane KH-550, MAH-g-PP, acid-treated |
| Mixing method | — | melt compounding, solution blending, in-situ polymerization |
| Mixing time (min) | min | 5–30 |
| Screw speed (rpm) | rpm | 50–200 (twin-screw extruder) |

| Response | Unit | Standard |
|----------|------|----------|
| Tensile strength | MPa | ASTM D638 |
| Tensile modulus | GPa | ASTM D638 |
| Flexural strength | MPa | ASTM D790 |
| Impact strength | J/m | ASTM D256 |
| HDT at 0.45 MPa | °C | ASTM D648 |
| Filler dispersion quality | — | SEM image rating (1–5) |

### Standards

- ASTM D638 — Tensile properties
- ASTM D790 — Flexural properties
- ASTM D256 — Impact resistance
- ASTM D648 — Heat deflection temperature
- ISO 178 — Flexural test for plastics

## Experiment Type 3: Thermo-Oxidative and UV Aging

Evaluate long-term thermal stability and UV resistance of polymers under accelerated aging conditions.

### Factors and Responses

| Factor | Unit | Typical Range |
|--------|------|---------------|
| Stabilizer type | — | hindered amine (HALS), hindered phenol, phosphite, benzotriazole UV absorber |
| Stabilizer content (wt%) | wt% | 0.1–2.0 |
| Exposure type | — | thermal oven, UV chamber (ASTM G154), xenon arc (ASTM G155) |
| Exposure temperature (°C) | °C | 70–150 (thermal), 50–70 (UV panel) |
| Exposure duration (h) | h | 500, 1000, 2000, 3000 |
| Atmosphere | — | air, nitrogen |

| Response | Unit | Standard |
|----------|------|----------|
| Retained tensile strength | % | ASTM D638 (before/after) |
| Retained elongation at break | % | ASTM D638 |
| Carbonyl index (FTIR) | — | absorbance ratio 1715 cm⁻¹ / reference peak |
| Color change (ΔE) | — | ASTM D2244 |
| Weight loss | % | gravimetric |
| Tg shift | °C | DSC (ASTM D3418) |

### Standards

- ASTM G154 — Fluorescent UV lamp exposure
- ASTM G155 — Xenon arc exposure
- ASTM D3045 — Heat aging of plastics (no load)
- ASTM D2244 — Color difference calculation
- ISO 4892 — Plastics — Methods of exposure to laboratory light sources

## Experiment Type 4: Thermoset Cure Kinetics and Gel Point

Optimize the curing schedule of thermoset systems (epoxy, unsaturated polyester, phenolic) by mapping cure kinetics.

### Factors and Responses

| Factor | Unit | Typical Range |
|--------|------|---------------|
| Hardener type | — | amine (DDS, DDM), anhydride (MNA), peroxide (BPO) |
| Hardener stoichiometric ratio | — | 0.7–1.2 (amine/epoxy equivalents) |
| Cure temperature (°C) | °C | 80–200 |
| Cure time (min) | min | 30–480 |
| Post-cure temperature (°C) | °C | 120–220 |
| Post-cure time (h) | h | 1–8 |

| Response | Unit | Standard |
|----------|------|----------|
| Gel time | min | ASTM D2471 (gel timer) |
| Degree of cure (DSC) | % | DSC residual enthalpy |
| Tg (onset) | °C | DSC (ASTM D3418) |
| Storage modulus (25°C) | MPa | DMA (ASTM D4065) |
| Gel content | % | solvent extraction (ASTM D2765) |
| Crosslink density | mol/m³ | swelling equilibrium (Flory–Rehner) |

### Standards

- ASTM D2471 — Gel time and peak exotherm of thermosetting resins
- ASTM D3418 — Tg and Tm by DSC
- ASTM D4065 — DMA measurement
- ASTM D2765 — Gel content of crosslinked plastics

## Typical Orthogonal Setup: PA6/GF Composite (L9)

4 factors, 3 levels each, 9 runs.

| Factor | Level 1 | Level 2 | Level 3 |
|--------|---------|---------|---------|
| Glass fiber content (wt%) | 10 | 20 | 30 |
| Melt temperature (°C) | 240 | 260 | 280 |
| Injection speed (mm/s) | 40 | 80 | 120 |
| Mold temperature (°C) | 40 | 80 | 120 |

| Run | GF (wt%) | Temp (°C) | Speed (mm/s) | Mold (°C) |
|-----|----------|-----------|--------------|-----------|
| 1 | 10 | 240 | 40 | 40 |
| 2 | 10 | 260 | 80 | 80 |
| 3 | 10 | 280 | 120 | 120 |
| 4 | 20 | 240 | 80 | 120 |
| 5 | 20 | 260 | 120 | 40 |
| 6 | 20 | 280 | 40 | 80 |
| 7 | 30 | 240 | 120 | 80 |
| 8 | 30 | 260 | 40 | 120 |
| 9 | 30 | 280 | 80 | 40 |

Responses: tensile strength, impact strength, warpage, surface roughness.

---

## Experiment Type 5: Polymer Composite Formulation Optimization (RSM Template)

Optimize filled polymer composite formulation using response surface methodology
for balanced mechanical and thermal properties.

### Factors and Responses (Box-Behnken, 4 factors)

| Factor | Unit | Low (-1) | Center (0) | High (+1) |
|--------|------|----------|-----------|-----------|
| Filler content | wt% | 10 | 20 | 30 |
| Coupling agent content | wt% | 0.5 | 1.5 | 2.5 |
| Processing temperature | °C | 180 | 200 | 220 |
| Screw speed | rpm | 100 | 150 | 200 |

| Response | Unit | Standard |
|----------|------|----------|
| Tensile strength | MPa | ASTM D638 |
| Tensile modulus | GPa | ASTM D638 |
| Impact strength (Izod) | J/m | ASTM D256 |
| HDT at 0.45 MPa | °C | ASTM D648 |

### Box-Behnken Design (27 runs, 4 factors)

Use the standard 4-factor BBD matrix in `static/core/response-surface.md` with:
A = filler content, B = coupling agent content, C = processing temperature,
D = screw speed. The design has 24 edge-midpoint runs plus 3 center points;
each non-center run varies exactly two factors at ±1 and holds the other two at 0.

### Analysis Plan

1. Fit quadratic model for each response
2. ANOVA with backward elimination
3. Check model adequacy (R², adj-R², lack-of-fit)
4. Response surface and contour plots for key factor pairs
5. Multi-response optimization using desirability function
6. Confirmation runs at predicted optimum

---

## Experiment Type 6: Processing Parameter Screening (Plackett-Burman Template)

Screen many processing and formulation factors to identify those most
affecting final part quality. Use this BEFORE detailed optimization.

### Factors (L12 Plackett-Burman, 11 factors)

| Factor | Unit | Low (-) | High (+) |
|--------|------|---------|----------|
| A: Filler type | — | CaCO₃ | Glass fiber |
| B: Filler content | wt% | 10 | 30 |
| C: Coupling agent type | — | Stearate | Silane KH-550 |
| D: Coupling agent content | wt% | 0.5 | 2.0 |
| E: Melt temperature | °C | 190 | 230 |
| F: Injection speed | mm/s | 30 | 100 |
| G: Holding pressure | MPa | 40 | 80 |
| H: Mold temperature | °C | 30 | 80 |
| I: Cooling time | s | 15 | 40 |
| J: Screw speed | rpm | 80 | 180 |
| K: Drying time | h | 2 | 8 |

### Responses

| Response | Unit | Standard |
|----------|------|----------|
| Tensile strength | MPa | ASTM D638 |
| Impact strength | J/m | ASTM D256 |
| Warpage | mm | CMM |
| Surface roughness | µm | Profilometer |

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

1. Calculate main effects for each response
2. Create Pareto charts of absolute effect magnitudes
3. Use normal probability plot or Lenth's method to identify active effects
4. Typically 3-5 factors emerge as important
5. Follow up with full factorial or RSM on the key subset

---

## Experiment Type 7: Multi-Component Blend Mixture Design (Simplex Template)

Optimize polymer blend or multicomponent composite formulation
using statistical mixture design.

### Components (4-component simplex centroid)

| Component | Range | Typical |
|-----------|-------|---------|
| x₁: Matrix polymer (PP/PA6/epoxy) | 60 – 90% | ~75% |
| x₂: Elastomer/rubber toughener | 5 – 20% | ~10% |
| x₃: Rigid filler (GF/CaCO₃) | 5 – 25% | ~15% |
| x₄: Compatibilizer/coupling agent | 0 – 5% | ~2% |

**Constraint:** x₁ + x₂ + x₃ + x₄ = 100% (by total mass)

Note: With constraints, use extreme vertices design rather than standard simplex.
Below is a standard simplex centroid for reference — adjust as needed.

### Simplex Centroid Design (4 components, 15 runs)

| Run | x₁ Matrix | x₂ Rubber | x₃ Filler | x₄ Compat. | Description |
|-----|----------|-----------|-----------|------------|-------------|
| 1 | 100% | 0% | 0% | 0% | Pure matrix |
| 2 | 0% | 100% | 0% | 0% | Pure rubber |
| 3 | 0% | 0% | 100% | 0% | Pure filler (reference) |
| 4 | 0% | 0% | 0% | 100% | Pure compatibilizer (reference) |
| 5 | 50% | 50% | 0% | 0% | Matrix-rubber binary |
| 6 | 50% | 0% | 50% | 0% | Matrix-filler binary |
| 7 | 50% | 0% | 0% | 50% | Matrix-compatibilizer binary |
| 8 | 0% | 50% | 50% | 0% | Rubber-filler binary |
| 9 | 0% | 50% | 0% | 50% | Rubber-compatibilizer binary |
| 10 | 0% | 0% | 50% | 50% | Filler-compatibilizer binary |
| 11 | 33.3% | 33.3% | 33.3% | 0% | Ternary 1-2-3 |
| 12 | 33.3% | 33.3% | 0% | 33.3% | Ternary 1-2-4 |
| 13 | 33.3% | 0% | 33.3% | 33.3% | Ternary 1-3-4 |
| 14 | 0% | 33.3% | 33.3% | 33.3% | Ternary 2-3-4 |
| 15 | 25% | 25% | 25% | 25% | Overall centroid |

### Responses

| Response | Unit | Standard |
|----------|------|----------|
| Tensile strength | MPa | ASTM D638 |
| Elongation at break | % | ASTM D638 |
| Impact strength | J/m | ASTM D256 |
| HDT | °C | ASTM D648 |
| Melt flow index | g/10min | ASTM D1238 |

### Analysis Plan

1. Fit quadratic mixture model (special cubic if ternary points available)
2. ANOVA for significance of component effects
3. Ternary contour plots for key combinations (hold one component constant)
4. Multi-response optimization using desirability function
5. Confirmation at optimal blend composition
