# Cement and Concrete Experiment Reference

Common experiment types, typical factor-response pairs, and standard references for cement, concrete, and supplementary cementitious materials (SCMs).

## Experiment Type 1: Mix Proportion Design

Optimize concrete mix proportions to achieve target strength, workability, and durability.

### Factors and Responses

| Factor | Unit | Typical Range |
|--------|------|---------------|
| Water-cement ratio | — | 0.30–0.60 |
| Cement content (kg/m³) | kg/m³ | 300–500 |
| Sand ratio (%) | % | 30–45 |
| Superplasticizer (%) | % | 0–2.0 |
| Coarse aggregate type | — | crushed stone, gravel, recycled |
| Maximum aggregate size (mm) | mm | 10, 16, 20, 25 |
| SCM type | — | fly ash, slag, silica fume |
| SCM replacement (%) | % | 0–40 |

| Response | Unit | Standard |
|----------|------|----------|
| 28-day compressive strength | MPa | ASTM C39 / GB/T 50081 |
| Slump | mm | ASTM C143 / GB/T 50080 |
| Air content (%) | % | ASTM C231 |
| Setting time | min | ASTM C191 / GB/T 1346 |
| Unit weight | kg/m³ | ASTM C138 |

### Standards

- ACI 211.1 — Standard practice for selecting proportions for normal concrete
- EN 206 — Concrete specification, performance, production and conformity
- GB/T 50080 — Standard for test method of performance on ordinary fresh concrete
- JGJ 55 — Specification for mix proportion design of ordinary concrete (Chinese)

## Experiment Type 2: Durability Testing

Evaluate concrete resistance to aggressive environments.

### Factors and Responses

| Factor | Unit | Typical Range |
|--------|------|---------------|
| w/c ratio | — | 0.35–0.55 |
| SCM type | — | fly ash, slag, silica fume, metakaolin |
| SCM replacement (%) | % | 0–40 |
| Curing condition | — | water, sealed, air, accelerated |
| Exposure type | — | chloride, sulfate, freeze-thaw, carbonation |
| Exposure duration | days | 28, 56, 90, 180, 365 |

| Response | Unit | Standard |
|----------|------|----------|
| Chloride migration coefficient | ×10⁻¹² m²/s | NT Build 492 / GB/T 50082 |
| Depth of carbonation | mm | GB/T 50082 |
| Mass loss after freeze-thaw | % | ASTM C666 / GB/T 50082 |
| Expansion after sulfate attack | % | ASTM C1012 |
| Compressive strength after exposure | MPa | ASTM C39 |
| Rapid chloride permeability | Coulombs | ASTM C1202 |

### Standards

- ASTM C666 — Resistance of concrete to rapid freezing and thawing
- ASTM C1012 — Length change of hydraulic-cement mortars exposed to sulfate solution
- ASTM C1202 — Electrical indication of concrete's ability to resist chloride penetration
- NT Build 492 — Chloride migration coefficient from non-steady-state migration
- GB/T 50082 — Standard for test methods of long-term performance and durability of ordinary concrete

## Experiment Type 3: Supplementary Cementitious Materials (SCMs)

Evaluate the effect of SCMs on fresh and hardened properties of concrete or mortar.

### Factors and Responses

| Factor | Unit | Typical Range |
|--------|------|---------------|
| SCM type | — | fly ash (Class F/C), slag, silica fume, metakaolin |
| Replacement level (%) | % | 5, 10, 15, 20, 30, 40 |
| Fineness (m²/kg) | m²/kg | 300–600 |
| w/b ratio | — | 0.35–0.50 |
| Curing temperature (°C) | °C | 20, 40, 60 |
| Curing age (days) | days | 3, 7, 28, 56, 90 |

| Response | Unit | Standard |
|----------|------|----------|
| Compressive strength | MPa | ASTM C39 |
| Activity index | % | ASTM C311 / GB/T 1596 |
| Water demand ratio | % | GB/T 1596 |
| Setting time | min | ASTM C191 |
| Heat of hydration | J/g | ASTM C1702 |
| Pozzolanic activity | — | EN 196-5 |

### Standards

- ASTM C618 — Fly ash and raw calcined natural pozzolan
- ASTM C989 — Ground granulated blast-furnace slag
- ASTM C1240 — Silica fume
- GB/T 1596 — Fly ash for cement and concrete (Chinese)
- GB/T 18046 — Ground granulated blast furnace slag used in cement and concrete (Chinese)

## Typical Orthogonal Setup: Concrete Durability (L9)

4 factors, 3 levels each, 9 runs.

| Factor | Level 1 | Level 2 | Level 3 |
|--------|---------|---------|---------|
| w/c ratio | 0.38 | 0.43 | 0.48 |
| Fly ash replacement (%) | 10 | 20 | 30 |
| Silica fume replacement (%) | 0 | 3 | 6 |
| Curing temperature (°C) | 20 | 35 | 50 |

| Run | w/c | Fly ash (%) | Silica fume (%) | Temp (°C) |
|-----|-----|------------|----------------|-----------|
| 1 | 0.38 | 10 | 0 | 20 |
| 2 | 0.38 | 20 | 3 | 35 |
| 3 | 0.38 | 30 | 6 | 50 |
| 4 | 0.43 | 10 | 3 | 50 |
| 5 | 0.43 | 20 | 6 | 20 |
| 6 | 0.43 | 30 | 0 | 35 |
| 7 | 0.48 | 10 | 6 | 35 |
| 8 | 0.48 | 20 | 0 | 50 |
| 9 | 0.48 | 30 | 3 | 20 |

Responses: 28-day compressive strength, chloride migration coefficient, water absorption.

---

## Experiment Type 4: UHPC Mix Optimization (RSM Template)

Optimize ultra-high performance concrete (UHPC) mix proportions using
response surface methodology.

### Factors and Responses (Central Composite, 4 factors)

| Factor | Unit | Low (-1) | Center (0) | High (+1) |
|--------|------|----------|-----------|-----------|
| Water-binder ratio | — | 0.16 | 0.20 | 0.24 |
| Silica fume content | % of binder | 15 | 20 | 25 |
| Steel fiber content | % by volume | 1.0 | 2.0 | 3.0 |
| Superplasticizer content | % of binder | 2.0 | 3.0 | 4.0 |

| Response | Unit | Standard |
|----------|------|----------|
| 28d compressive strength | MPa | ASTM C1856 / GB/T 50081 |
| 28d flexural strength | MPa | ASTM C1609 / GB/T 50081 |
| Flow (fresh) | mm | ASTM C1437 |
| Drying shrinkage (28d) | ×10⁻⁶ | ASTM C157 / GB/T 50082 |

### Central Composite Design (Face-Centered, α = 1)

Face-centered CCD is used here because extrapolation beyond the tested ranges
would be unreasonable (e.g., w/b < 0.16 may not be achievable).

Total runs: 16 factorial (2^4) + 8 axial + 6 center = **30 runs**

| Run | w/b (A) | SF (B) | Fiber (C) | SP (D) | Type |
|-----|---------|--------|-----------|--------|------|
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
| 17 | -1 | 0 | 0 | 0 | axial (face center) |
| 18 | +1 | 0 | 0 | 0 | axial (face center) |
| 19 | 0 | -1 | 0 | 0 | axial (face center) |
| 20 | 0 | +1 | 0 | 0 | axial (face center) |
| 21 | 0 | 0 | -1 | 0 | axial (face center) |
| 22 | 0 | 0 | +1 | 0 | axial (face center) |
| 23 | 0 | 0 | 0 | -1 | axial (face center) |
| 24 | 0 | 0 | 0 | +1 | axial (face center) |
| 25 | 0 | 0 | 0 | 0 | center |
| 26 | 0 | 0 | 0 | 0 | center |
| 27 | 0 | 0 | 0 | 0 | center |
| 28 | 0 | 0 | 0 | 0 | center |
| 29 | 0 | 0 | 0 | 0 | center |
| 30 | 0 | 0 | 0 | 0 | center |

**If 30 runs is too many**, consider Box-Behnken with 27 runs (but you lose
corner points — BBD doesn't test extreme combinations like w/b=0.16 + SF=25%).

### Analysis Plan

1. Fit full quadratic model for each response
2. ANOVA with backward elimination of non-significant terms
3. Check model diagnostics: R², adj-R², pred-R², lack-of-fit
4. Generate contour and surface plots for key factor pairs
5. Numerical optimization: maximize strength, minimize shrinkage
6. Multi-response desirability optimization
7. Confirmation at 2-3 optimal formulations

---

## Experiment Type 5: Durability Multi-Objective Optimization (RSM Template)

Optimize concrete mixture for multiple durability properties simultaneously
using response surface methodology with desirability function.

### Factors and Responses (Box-Behnken, 4 factors)

| Factor | Unit | Low (-1) | Center (0) | High (+1) |
|--------|------|----------|-----------|-----------|
| Water-binder ratio | — | 0.35 | 0.42 | 0.50 |
| Fly ash replacement | % of binder | 10 | 20 | 30 |
| GGBS replacement | % of binder | 0 | 20 | 40 |
| Curing age | days | 28 | 56 | 90 |

**Note:** Total SCM = fly ash + GGBS. If fly ash + GGBS should be ≤ 50%,
this becomes a constrained mixture problem. For initial screening, treat them
as independent factors and check the constraint post-hoc.

### Responses

| Response | Unit | Standard |
|----------|------|----------|
| Chloride migration coefficient | ×10⁻¹² m²/s | NT Build 492 |
| Compressive strength | MPa | ASTM C39 |
| Carbonation depth | mm | GB/T 50082 |
| Freeze-thaw mass loss | % | ASTM C666 |

### Box-Behnken Design (27 runs)

Use the standard 4-factor BBD matrix in `static/core/response-surface.md` with:
A = water-binder ratio, B = fly ash replacement, C = GGBS replacement,
D = curing age. The design has 24 edge-midpoint runs plus 3 center points;
each non-center run varies exactly two factors at ±1 and holds the other two at 0.

### Multi-Objective Optimization Strategy

Use desirability function approach:

1. **Individual desirability (d_i)** for each response:
   - Chloride migration: smaller-is-better → d₁
   - Compressive strength: larger-is-better → d₂
   - Carbonation depth: smaller-is-better → d₃
   - Freeze-thaw mass loss: smaller-is-better → d₄

2. **Overall desirability**: D = (d₁ × d₂ × d₃ × d₄)^(1/4)

3. **Weighted option**: If some responses matter more, apply weights:
   D = (d₁^w₁ × d₂^w₂ × d₃^w₃ × d₄^w₄)^(1/Σw_i)

4. Find factor settings that maximize D

5. **Generate trade-off curves**: e.g., how much strength must be sacrificed
   to reduce chloride migration by 20%?

---

## Experiment Type 6: SCM System Factor Screening (Plackett-Burman Template)

Screen multiple mixture and process factors to identify those most
affecting concrete properties with supplementary cementitious materials.

### Factors (L12 Plackett-Burman, 11 factors)

| Factor | Unit | Low (-) | High (+) |
|--------|------|---------|----------|
| A: Fly ash content | % of binder | 0 | 30 |
| B: GGBS content | % of binder | 0 | 40 |
| C: Silica fume content | % of binder | 0 | 8 |
| D: Water-binder ratio | — | 0.35 | 0.50 |
| E: Superplasticizer dosage | % of binder | 0.8 | 1.5 |
| F: Curing temperature | °C | 20 | 40 |
| G: Coarse aggregate type | — | Crushed | Gravel |
| H: Sand ratio | % | 33 | 40 |
| I: Air entrainer | % of binder | 0 | 0.03 |
| J: Fiber content | % by volume | 0 | 0.1 |
| K: Curing method | — | Standard | Steam |

### Responses

| Response | Unit | Standard |
|----------|------|----------|
| 28d compressive strength | MPa | ASTM C39 |
| Chloride migration coefficient | ×10⁻¹² m²/s | NT Build 492 |

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

1. Estimate main effects for strength and durability
2. Compare Pareto charts for both responses
3. Identify factors that affect both (high leverage) and factors that affect only one
4. Typically 3-5 factors emerge as active
5. Plan follow-up factorial or RSM on the key subset

### Typical Findings from SCM Screening

Usually the most important factors are:
- **w/b ratio** — strongly affects both strength and durability
- **SCM type/dosage** — especially for durability
- **Curing age/temperature** — affects strength gain rate

Factors that are often less important (in well-proportioned mixes):
- Sand ratio (within reasonable range)
- Coarse aggregate type (if same quality)
- Minor admixtures (if within recommended dosage)

Always verify with your specific materials — screening is for this reason!
