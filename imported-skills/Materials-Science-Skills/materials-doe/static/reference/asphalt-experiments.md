# Asphalt Experiment Reference

Common experiment types, typical factor-response pairs, and standard references for asphalt and asphalt mixture research.

## Experiment Type 1: Tack Coat Bond Strength

Evaluate the interlayer bond strength between asphalt layers under different tack coat materials and application rates.

### Factors and Responses

| Factor | Unit | Typical Range |
|--------|------|---------------|
| Tack coat type | — | CSS-1, CRS-1, SBS-modified emulsion |
| Application rate (L/m²) | L/m² | 0.2–0.8 |
| Curing time (min) | min | 15–120 |
| Temperature (°C) | °C | 15–35 |
| Surface condition | — | dry, damp, dusty |

| Response | Unit | Standard |
|----------|------|----------|
| Shear strength | kPa | ASTM D4867 |
| Tensile bond strength | kPa | EN 12697-48 |
| Failure mode | — | cohesive / adhesive |

### Standards

- ASTM D4867 — Pull-off test for tack coat bond
- AASHTO T 370 — Bond strength of tack coat
- EN 12697-48 — Interlayer bond strength

## Experiment Type 2: Modified Emulsified Asphalt Preparation

Optimize the formulation of polymer-modified emulsified asphalt for chip seal, micro-surface, or cold mix applications.

### Factors and Responses

| Factor | Unit | Typical Range |
|--------|------|---------------|
| Modifier type | — | SBR, SBS, EVA, waterborne epoxy |
| Modifier content (%) | % | 2–12 |
| Emulsifier type | — | cationic, anionic |
| Emulsifier dosage (%) | % | 0.5–3.0 |
| Mixing temperature (°C) | °C | 130–170 |
| Mixing speed (rpm) | rpm | 500–2500 |
| Mixing time (min) | min | 10–40 |

| Response | Unit | Standard |
|----------|------|----------|
| Storage stability (%) | % | ASTM D244 |
| Residue penetration | 0.1 mm | ASTM D5 |
| Residue softening point | °C | ASTM D36 |
| Residue ductility | cm | ASTM D113 |
| Elastic recovery (%) | % | ASTM D6084 |
| Adhesion grade | — | ASTM D2939 |

### Standards

- ASTM D244 — Emulsified asphalt testing
- ASTM D5 — Penetration of bituminous materials
- ASTM D36 — Softening point (ring and ball)
- JTG E20 — T 0651 (Chinese standard for emulsified asphalt)

## Experiment Type 3: Moisture Damage Resistance

Evaluate the moisture susceptibility of asphalt mixtures and the effectiveness of anti-stripping agents.

### Factors and Responses

| Factor | Unit | Typical Range |
|--------|------|---------------|
| Anti-stripping agent type | — | liquid amine, hydrated lime, polyamine |
| Anti-stripping agent dosage (%) | % | 0.1–2.0 |
| Aggregate type | — | limestone, basalt, granite |
| Asphalt content (%) | % | 4.0–6.5 |
| Conditioning method | — | freeze-thaw, moisture-induced stress |
| Freeze-thaw cycles | — | 1, 3, 5, 7 |

| Response | Unit | Standard |
|----------|------|----------|
| Tensile strength ratio (TSR) | % | AASHTO T 283 |
| Retained Marshall stability | % | ASTM D4867 |
| Dynamic stability ratio | % | JTG E20 T 0719 |
| Stripping inflection point | cycles | ASTM D4867 |

### Standards

- AASHTO T 283 — Moisture susceptibility of compacted asphalt mixtures
- ASTM D4867 — Effect of moisture on asphalt concrete
- JTG E20 T 0719 — Dynamic stability of asphalt mixture (Chinese)

## Typical Orthogonal Setup: Modified Emulsified Asphalt (L9)

4 factors, 3 levels each, 9 runs.

| Factor | Level 1 | Level 2 | Level 3 |
|--------|---------|---------|---------|
| Modifier content (%) | 4 | 6 | 8 |
| Emulsifier dosage (%) | 1.0 | 1.5 | 2.0 |
| Mixing temperature (°C) | 140 | 155 | 170 |
| Mixing time (min) | 15 | 25 | 35 |

| Run | Modifier (%) | Emulsifier (%) | Temp (°C) | Time (min) |
|-----|-------------|----------------|-----------|------------|
| 1 | 4 | 1.0 | 140 | 15 |
| 2 | 4 | 1.5 | 155 | 25 |
| 3 | 4 | 2.0 | 170 | 35 |
| 4 | 6 | 1.0 | 155 | 35 |
| 5 | 6 | 1.5 | 170 | 15 |
| 6 | 6 | 2.0 | 140 | 25 |
| 7 | 8 | 1.0 | 170 | 25 |
| 8 | 8 | 1.5 | 140 | 35 |
| 9 | 8 | 2.0 | 155 | 15 |

Responses: storage stability, residue softening point, elastic recovery.

---

## Experiment Type 4: WER-EA Formulation Optimization (RSM Template)

Optimize waterborne epoxy modified emulsified asphalt formulation using
response surface methodology. Use after initial screening has identified
key factors.

### Factors and Responses (Box-Behnken, 4 factors)

| Factor | Unit | Low (-1) | Center (0) | High (+1) |
|--------|------|----------|-----------|-----------|
| Waterborne epoxy content | % | 2 | 5 | 8 |
| Curing agent content | % | 0.5 | 1.5 | 2.5 |
| Emulsifier content | % | 1.0 | 1.5 | 2.0 |
| Shearing time | min | 10 | 20 | 30 |

| Response | Unit | Standard |
|----------|------|----------|
| Bond strength (shear) | kPa | EN 12697-48 |
| Storage stability (1d/5d) | % | ASTM D244 |
| Softening point | °C | ASTM D36 |
| Viscosity (Brookfield) | Pa·s | ASTM D4402 |

### Box-Behnken Design Matrix (27 runs)

Use the standard 4-factor BBD matrix in `static/core/response-surface.md` with:
A = waterborne epoxy content, B = curing agent content, C = emulsifier content,
D = shearing time. The design has 24 edge-midpoint runs plus 3 center points;
each non-center run varies exactly two factors at ±1 and holds the other two at 0.

### Analysis Plan

1. Fit quadratic model for each response
2. ANOVA for significance
3. Check model adequacy (R², adjusted R², lack-of-fit)
4. Generate response surface plots for key factor pairs
5. Multi-response optimization using desirability function
6. Confirmation runs at predicted optimum

---

## Experiment Type 5: Modified Emulsified Asphalt Factor Screening (Plackett-Burman Template)

Screen many candidate factors to identify the few that most strongly affect
modified emulsified asphalt properties. Use this BEFORE RSM when you have
many potential factors but limited experimental budget.

### Factors (L12 Plackett-Burman, 11 factors)

| Factor | Unit | Low (-) | High (+) |
|--------|------|---------|----------|
| A: Modifier type | — | SBR latex | SBS emulsion |
| B: Modifier content | % | 3 | 6 |
| C: Emulsifier type | — | Cationic | Anionic |
| D: Emulsifier content | % | 1.0 | 2.0 |
| E: Shearing temperature | °C | 50 | 70 |
| F: Shearing speed | rpm | 3000 | 8000 |
| G: Shearing time | min | 10 | 30 |
| H: pH value | — | 5 | 7 |
| I: Stabilizer content | % | 0 | 0.3 |
| J: Asphalt content | % | 55 | 65 |
| K: Soap solution temperature | °C | 50 | 70 |

### Responses

| Response | Unit | Standard |
|----------|------|----------|
| Storage stability (5d) | % | ASTM D244 |
| Residue softening point | °C | ASTM D36 |
| Viscosity (25°C) | Pa·s | ASTM D4402 |

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

1. Calculate main effects: (Avg at +) − (Avg at −) for each factor
2. Create Pareto chart of absolute effect magnitudes
3. Use normal probability plot or Lenth's method to identify active effects
4. Typically 2-4 factors emerge as important from a well-designed screen
5. Follow up with full factorial or RSM on the key factors only

### Example Follow-up Path

After L12 screening, suppose factors B (modifier content), D (emulsifier content),
and G (shearing time) are identified as most important:

→ Run full 2^3 factorial + center points (8+6=14 runs) to characterize interactions
→ If curvature significant → augment to CCD for optimization

---

## Experiment Type 6: Multi-Component Modifier Mixture Design (Simplex Template)

Optimize a multi-component modifier system for emulsified asphalt using
statistical mixture design. Appropriate when modifier components sum to
a fixed total modifier content.

### Components (3-component simplex centroid)

| Component | Range | Typical |
|-----------|-------|---------|
| x₁: Base asphalt | 80 – 92% | ~87% |
| x₂: SBR latex modifier | 3 – 10% | ~6% |
| x₃: Waterborne epoxy | 3 – 10% | ~7% |

**Constraint:** x₁ + x₂ + x₃ = 100% (by total binder mass)

Note: These are constrained components. For constrained mixture designs,
use extreme vertices design instead of standard simplex. Below is a
standard simplex centroid for reference — adjust constraints as needed.

### Simplex Centroid Design (7 runs)

| Run | x₁ Asphalt | x₂ SBR | x₃ Epoxy | Description |
|-----|-----------|--------|----------|-------------|
| 1 | 100% | 0% | 0% | Pure asphalt (baseline) |
| 2 | 0% | 100% | 0% | Pure SBR (reference) |
| 3 | 0% | 0% | 100% | Pure epoxy (reference) |
| 4 | 50% | 50% | 0% | Asphalt-SBR binary |
| 5 | 50% | 0% | 50% | Asphalt-epoxy binary |
| 6 | 0% | 50% | 50% | SBR-epoxy binary |
| 7 | 33.3% | 33.3% | 33.3% | Ternary blend |

### Constrained Version (Extreme Vertices Concept)

For the realistic constraints above (asphalt 80-92%, SBR 3-10%, epoxy 3-10%),
the feasible region is a polygon. Key points include:

| Run | x₁ Asphalt | x₂ SBR | x₃ Epoxy | Description |
|-----|-----------|--------|----------|-------------|
| 1 | 92% | 3% | 5% | Max asphalt, min SBR |
| 2 | 92% | 5% | 3% | Max asphalt, min epoxy |
| 3 | 87% | 3% | 10% | Min asphalt, max epoxy, min SBR |
| 4 | 87% | 10% | 3% | Min asphalt, max SBR, min epoxy |
| 5 | 87% | 6.5% | 6.5% | Center of feasible region |
| 6 | 89.5% | 6.5% | 4% | Interior check point |

Note: Confirm actual extreme vertices for your specific constraints.
This is a representative example — calculate exact vertices based on your bounds.

### Responses

| Response | Unit | Standard |
|----------|------|----------|
| Storage stability | % | ASTM D244 |
| Softening point | °C | ASTM D36 |
| Bond strength | kPa | EN 12697-48 |
| Ductility | cm | ASTM D113 |

### Analysis Plan

1. Fit quadratic mixture model (special cubic if center point available)
2. ANOVA for significance of blend components
3. Ternary contour plots for each response
4. Multi-response optimization (desirability function)
5. Confirmation at optimal blend

---

## Sequential Research Workflow Example

A complete WER-EA research program might follow this path:

### Phase 1: Screening (L12 Plackett-Burman)
- Goal: Identify the 2-3 most important factors from ~10 candidates
- Runs: 12
- Outcome: Factor ranking by effect magnitude
- Key factors identified: epoxy content, curing agent content, shearing time

### Phase 2: Characterization (Full factorial 2^3 + center points)
- Goal: Understand interactions between key factors
- Runs: 8 factorial + 4 center = 12 runs
- Outcome: Main effects, 2-factor interactions, curvature test
- If significant curvature → proceed to RSM

### Phase 3: Optimization (BBD or CCD)
- Goal: Find optimal formulation
- Runs: 15 (3-f BBD) or 20 (3-f CCD)
- Outcome: Quadratic model, response surfaces, optimal conditions

### Phase 4: Confirmation
- Goal: Verify predictions at optimal conditions
- Runs: 3-5 replicates at optimum
- Outcome: Confirmed optimal formulation with error bars

### Total runs: ~40-50
Compare to: A naive 4-factor × 3-level full factorial = 81 runs
(and still wouldn't give you a proper optimization model!)
