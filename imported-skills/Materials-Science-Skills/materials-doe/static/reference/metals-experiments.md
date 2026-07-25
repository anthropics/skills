# Metals Experiment Reference

Common experiment types, typical factor-response pairs, and standard references for metals and alloys research.

## Experiment Type 1: Heat Treatment Optimization

Optimize quenching and tempering parameters to achieve target strength-toughness balance in structural steels.

### Factors and Responses

| Factor | Unit | Typical Range |
|--------|------|---------------|
| Austenitizing temperature (°C) | °C | 820–950 (low-alloy), 1000–1200 (stainless/tool) |
| Austenitizing time (min) | min | 15–120 |
| Quench medium | — | water, oil, air, polymer, brine |
| Tempering temperature (°C) | °C | 150–650 |
| Tempering time (min) | min | 30–360 |

| Response | Unit | Standard |
|----------|------|----------|
| Yield strength (Rp0.2) | MPa | ASTM E8 / ISO 6892 |
| UTS | MPa | ASTM E8 / ISO 6892 |
| Elongation | % | ASTM E8 / ISO 6892 |
| Hardness | HRC / HV | ASTM E18 / ASTM E92 |
| Impact energy (Charpy V) | J | ASTM E23 / ISO 148 |

### Standards

- ASTM E8 — Tension testing of metallic materials
- ISO 6892 — Metallic materials — Tensile testing
- ASTM E23 — Notched bar impact testing
- ASTM E18 — Rockwell hardness
- ASTM E92 — Vickers hardness

## Experiment Type 2: Additive Manufacturing Process Optimization

Optimize laser powder bed fusion (LPBF/SLM) parameters for density, microstructure, and mechanical properties.

### Factors and Responses

| Factor | Unit | Typical Range |
|--------|------|---------------|
| Laser power (W) | W | 100–400 |
| Scan speed (mm/s) | mm/s | 400–1600 |
| Layer thickness (µm) | µm | 20–60 |
| Hatch spacing (µm) | µm | 80–200 |
| Scan strategy | — | stripe, chessboard, 67° rotation |
| Energy density (J/mm³) | J/mm³ | 30–150 (calculated from above) |

| Response | Unit | Standard |
|----------|------|----------|
| Relative density | % | Archimedes (ASTM B311) |
| Surface roughness (Ra) | µm | profilometer |
| Yield strength | MPa | ASTM E8 |
| Elongation | % | ASTM E8 |
| Residual porosity | % | metallographic cross-section |
| Microhardness | HV | ASTM E92 |

### Standards

- ASTM B311 — Density of powder metallurgy materials
- ASTM E8 — Tensile testing
- ISO/ASTM 52900 — Additive manufacturing — General principles
- ISO/ASTM 52901 — Requirements for purchased AM parts

## Experiment Type 3: Corrosion Resistance

Evaluate the pitting and general corrosion resistance of stainless steels or coated alloys in chloride environments.

### Factors and Responses

| Factor | Unit | Typical Range |
|--------|------|---------------|
| Alloy type | — | 304, 316, 316L, 2205 duplex, 2507 super duplex |
| Cl⁻ concentration (mol/L) | mol/L | 0.01–6.0 (NaCl solution) |
| Temperature (°C) | °C | 20, 40, 60, 80 |
| pH | — | 1–10 |
| Surface finish | — | ground, polished, pickled, passivated |
| Exposure time (h) | h | 24, 168, 720, 3000 |

| Response | Unit | Standard |
|----------|------|----------|
| Corrosion rate | mm/year | ASTM G102 (from polarization) |
| Pitting potential (E_pit) | mV vs SCE | ASTM G61 |
| Repassivation potential (E_rp) | mV vs SCE | ASTM G61 |
| Critical pitting temperature (CPT) | °C | ASTM G48 |
| Mass loss | mg/cm² | ASTM G31 |

### Standards

- ASTM G5 — Potentiodynamic anodic polarization
- ASTM G61 — Cyclic potentiodynamic polarization
- ASTM G48 — Pitting and crevice corrosion (FeCl₃)
- ASTM B117 — Salt spray (fog) testing
- ASTM A262 — Intergranular corrosion testing

## Experiment Type 4: Welding Parameter Optimization

Optimize welding parameters for defect-free joints with balanced strength and toughness.

### Factors and Responses

| Factor | Unit | Typical Range |
|--------|------|---------------|
| Welding method | — | GTAW, GMAW, SMAW, SAW, laser, EBW |
| Current (A) | A | 80–300 (GTAW), 150–400 (GMAW) |
| Voltage (V) | V | 10–30 |
| Travel speed (mm/s) | mm/s | 2–15 |
| Preheat temperature (°C) | °C | 25–300 |
| Interpass temperature (°C) | °C | 150–250 |
| Post-weld heat treatment | — | none, stress relief, PWHT |

| Response | Unit | Standard |
|----------|------|----------|
| Weld metal tensile strength | MPa | AWS D1.1 / ISO 4136 |
| HAZ hardness | HV | ASTM E92 |
| Charpy impact (weld metal) | J | ASTM E23 |
| Charpy impact (HAZ) | J | ASTM E23 |
| Defect rate (porosity, crack) | — | radiography (ASTM E94) |
| Dilution ratio | % | metallographic cross-section |

### Standards

- AWS D1.1 — Structural welding code — Steel
- ISO 4136 — Destructive tests on welds — Transverse tensile test
- ASTM E94 — Radiographic examination
- ISO 17637 — Visual testing of welds

## Typical Orthogonal Setup: 4340 Steel Q&T (L9)

4 factors, 3 levels each, 9 runs.

| Factor | Level 1 | Level 2 | Level 3 |
|--------|---------|---------|---------|
| Austenitizing temp (°C) | 830 | 860 | 890 |
| Quench medium | oil | water | polymer |
| Tempering temp (°C) | 200 | 400 | 600 |
| Tempering time (min) | 60 | 120 | 180 |

| Run | Aus. (°C) | Quench | Temp. (°C) | Time (min) |
|-----|-----------|--------|------------|------------|
| 1 | 830 | oil | 200 | 60 |
| 2 | 830 | water | 400 | 120 |
| 3 | 830 | polymer | 600 | 180 |
| 4 | 860 | oil | 400 | 180 |
| 5 | 860 | water | 600 | 60 |
| 6 | 860 | polymer | 200 | 120 |
| 7 | 890 | oil | 600 | 120 |
| 8 | 890 | water | 200 | 180 |
| 9 | 890 | polymer | 400 | 60 |

Responses: yield strength, UTS, elongation, hardness, Charpy impact energy.

---

## Experiment Type 5: Heat Treatment Process Optimization (RSM Template)

Optimize quenching and tempering parameters for optimal strength-toughness
balance using response surface methodology.

### Factors and Responses (Box-Behnken, 4 factors)

| Factor | Unit | Low (-1) | Center (0) | High (+1) |
|--------|------|----------|-----------|-----------|
| Austenitizing temperature | °C | 820 | 870 | 920 |
| Austenitizing time | min | 20 | 45 | 90 |
| Tempering temperature | °C | 200 | 400 | 600 |
| Tempering time | min | 60 | 120 | 240 |

| Response | Unit | Standard |
|----------|------|----------|
| Yield strength (Rp0.2) | MPa | ASTM E8 |
| UTS | MPa | ASTM E8 |
| Elongation | % | ASTM E8 |
| Hardness | HRC | ASTM E18 |
| Charpy V impact energy | J | ASTM E23 |

### Box-Behnken Design (27 runs, 4 factors)

Use the standard 4-factor BBD matrix in `static/core/response-surface.md` with:
A = austenitizing temperature, B = austenitizing time, C = tempering temperature,
D = tempering time. The design has 24 edge-midpoint runs plus 3 center points;
each non-center run varies exactly two factors at ±1 and holds the other two at 0.

### Analysis Plan

1. Fit quadratic model for each response
2. ANOVA with backward elimination
3. Check model diagnostics: R², adj-R², lack-of-fit
4. Response surface plots for key factor pairs (e.g., tempering temp vs tempering time)
5. Multi-response optimization: find strength-toughness trade-off frontier
6. Desirability function optimization with target properties
7. Confirmation at 2-3 optimal heat treatment schedules

---

## Experiment Type 6: LPBF Process Parameter Screening (Plackett-Burman Template)

Screen many laser powder bed fusion (LPBF) parameters to identify those most
affecting density, surface quality, and mechanical properties.

### Factors (L12 Plackett-Burman, 11 factors)

| Factor | Unit | Low (-) | High (+) |
|--------|------|---------|----------|
| A: Laser power | W | 150 | 300 |
| B: Scan speed | mm/s | 600 | 1200 |
| C: Layer thickness | µm | 20 | 50 |
| D: Hatch spacing | µm | 80 | 150 |
| E: Scan strategy | — | Stripe | Chessboard |
| F: Scan rotation | ° | 0 | 67 |
| G: Laser spot size | µm | 50 | 100 |
| H: Preheat temperature | °C | 25 | 200 |
| I: Powder layer thickness | µm | 20 | 60 |
| J: Gas flow rate | m/s | 2 | 10 |
| K: Post-heat treatment | — | As-built | Stress relieved |

### Responses

| Response | Unit | Standard |
|----------|------|----------|
| Relative density | % | Archimedes (ASTM B311) |
| Surface roughness (Ra) | µm | Profilometer |
| Yield strength | MPa | ASTM E8 |
| Elongation | % | ASTM E8 |
| Microhardness | HV | ASTM E92 |

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

1. Calculate main effects for density, roughness, and strength
2. Pareto chart analysis to rank factor importance
3. Normal probability plot to identify statistically significant effects
4. Typically the strongest factors are laser power, scan speed, and hatch spacing
5. Follow up with RSM on the 3-4 most important parameters
6. Energy density (P/v·h·t) is a useful composite metric but hides individual effects

---

## Experiment Type 7: Alloy Composition Optimization (Mixture Design Template)

Optimize multi-component alloy composition using statistical mixture design.
Appropriate when alloying elements sum to 100% (balance element + additions).

### Components (4-component simplex centroid)

Example: High-entropy alloy or multi-component steel system

| Component | Range | Typical |
|-----------|-------|---------|
| x₁: Base metal (Fe/Ni/Cu) | 60 – 85% | ~75% |
| x₂: Alloying element A (Cr/Mn) | 5 – 20% | ~10% |
| x₃: Alloying element B (Co/Nb) | 3 – 15% | ~8% |
| x₄: Minor element (Mo/V/W/Ti) | 0.5 – 5% | ~2% |

**Constraint:** x₁ + x₂ + x₃ + x₄ = 100% (by atomic or weight percent)

Note: With constraints, use extreme vertices design rather than standard simplex.
Below is a standard simplex centroid for reference.

### Simplex Centroid Design (4 components, 15 runs)

| Run | x₁ Base | x₂ Element A | x₃ Element B | x₄ Minor | Description |
|-----|---------|-------------|-------------|----------|-------------|
| 1 | 100% | 0% | 0% | 0% | Pure base metal |
| 2 | 0% | 100% | 0% | 0% | Pure element A |
| 3 | 0% | 0% | 100% | 0% | Pure element B |
| 4 | 0% | 0% | 0% | 100% | Pure minor element |
| 5 | 50% | 50% | 0% | 0% | Binary 1-2 |
| 6 | 50% | 0% | 50% | 0% | Binary 1-3 |
| 7 | 50% | 0% | 0% | 50% | Binary 1-4 |
| 8 | 0% | 50% | 50% | 0% | Binary 2-3 |
| 9 | 0% | 50% | 0% | 50% | Binary 2-4 |
| 10 | 0% | 0% | 50% | 50% | Binary 3-4 |
| 11 | 33.3% | 33.3% | 33.3% | 0% | Ternary 1-2-3 |
| 12 | 33.3% | 33.3% | 0% | 33.3% | Ternary 1-2-4 |
| 13 | 33.3% | 0% | 33.3% | 33.3% | Ternary 1-3-4 |
| 14 | 0% | 33.3% | 33.3% | 33.3% | Ternary 2-3-4 |
| 15 | 25% | 25% | 25% | 25% | Overall centroid |

### Responses

| Response | Unit | Standard |
|----------|------|----------|
| Yield strength | MPa | ASTM E8 |
| UTS | MPa | ASTM E8 |
| Elongation | % | ASTM E8 |
| Hardness | HV | ASTM E92 |
| Charpy impact energy | J | ASTM E23 |
| Corrosion rate | mm/yr | ASTM G102 |

### Analysis Plan

1. Fit quadratic mixture model (special cubic if ternary points available)
2. ANOVA for significance of element effects and interactions
3. Ternary contour plots for key combinations
4. Multi-response optimization: strength-ductility balance, corrosion resistance
5. Desirability function optimization
6. Confirmation at optimal composition
