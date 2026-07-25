# Mixture Design

Statistical mixture designs for formulating materials where the sum of
component proportions equals 100%. Use for formulations, recipes,
and blend optimization.

## Overview

In mixture experiments, the response depends on the **proportions** of the
components, not on their absolute amounts. The key constraint is:

```
x₁ + x₂ + ... + x_q = 1.0 (or 100%)
```

where q = number of components.

### When to use mixture design

- You're formulating a blend (e.g., concrete mix, polymer blend, alloy)
- Changing one component's proportion forces changes in others
- You want to optimize a recipe for multiple properties
- You need a statistical model for prediction within the simplex

### When NOT to use mixture design

- Factors are independent (use factorial/RSM instead)
- You only need to adjust one additive (use single-factor or factorial)
- You're studying process parameters, not component proportions

### Mixture design vs Mix design (mix-design-guide)

| Aspect | Mixture Design (statistical) | Mix Design (engineering) |
|--------|-----------------------------|--------------------------|
| Approach | Statistical, model-based | Empirical, rule-based |
| Output | Regression model, optimal blend | Starting point recipe |
| Scope | Within tested range only | Broader guidance |
| Use when | You need optimization or predictive model | You need a first guess recipe |

**Recommended workflow:** Start with mix-design-guide for an initial recipe,
then use mixture design to fine-tune and optimize.

---

## Simplex Lattice Design {q, m}

### Principle

A {q, m} simplex lattice design places points at all combinations of
component proportions that are multiples of 1/m.

Notation:
- q = number of components
- m = degree of the lattice (number of levels per component minus 1)
- Total points = (q + m - 1)! / (q - 1)! / m!

### {3, 2} Simplex Lattice (3 components, 2nd degree)

Total points: 6 (no center) — or add center point for curvature check

| Run | x₁ | x₂ | x₃ | Description |
|-----|----|----|----|-------------|
| 1 | 1 | 0 | 0 | Pure component 1 |
| 2 | 0 | 1 | 0 | Pure component 2 |
| 3 | 0 | 0 | 1 | Pure component 3 |
| 4 | 0.5 | 0.5 | 0 | Binary blend (edge midpoint) |
| 5 | 0.5 | 0 | 0.5 | Binary blend (edge midpoint) |
| 6 | 0 | 0.5 | 0.5 | Binary blend (edge midpoint) |
| 7* | 0.333 | 0.333 | 0.333 | Center (centroid) - optional |

*Add center point to check for special cubic effects (ternary interaction).

### {3, 3} Simplex Lattice (3 components, 3rd degree)

Total points: 10

| Run | x₁ | x₂ | x₃ | Description |
|-----|----|----|----|-------------|
| 1 | 1 | 0 | 0 | Pure 1 |
| 2 | 0 | 1 | 0 | Pure 2 |
| 3 | 0 | 0 | 1 | Pure 3 |
| 4 | 2/3 | 1/3 | 0 | Edge (1:2 on 1-2 edge) |
| 5 | 1/3 | 2/3 | 0 | Edge (2:1 on 1-2 edge) |
| 6 | 2/3 | 0 | 1/3 | Edge (2:1 on 1-3 edge) |
| 7 | 1/3 | 0 | 2/3 | Edge (1:2 on 1-3 edge) |
| 8 | 0 | 2/3 | 1/3 | Edge (2:1 on 2-3 edge) |
| 9 | 0 | 1/3 | 2/3 | Edge (1:2 on 2-3 edge) |
| 10 | 1/3 | 1/3 | 1/3 | Center (centroid) |

### {4, 2} Simplex Lattice (4 components, 2nd degree)

Total points: 10

| Run | x₁ | x₂ | x₃ | x₄ | Description |
|-----|----|----|----|----|-------------|
| 1 | 1 | 0 | 0 | 0 | Pure 1 |
| 2 | 0 | 1 | 0 | 0 | Pure 2 |
| 3 | 0 | 0 | 1 | 0 | Pure 3 |
| 4 | 0 | 0 | 0 | 1 | Pure 4 |
| 5 | 0.5 | 0.5 | 0 | 0 | Edge midpoint 1-2 |
| 6 | 0.5 | 0 | 0.5 | 0 | Edge midpoint 1-3 |
| 7 | 0.5 | 0 | 0 | 0.5 | Edge midpoint 1-4 |
| 8 | 0 | 0.5 | 0.5 | 0 | Edge midpoint 2-3 |
| 9 | 0 | 0.5 | 0 | 0.5 | Edge midpoint 2-4 |
| 10 | 0 | 0 | 0.5 | 0.5 | Edge midpoint 3-4 |

Add overall center point (0.25, 0.25, 0.25, 0.25) if needed.

### Number of runs for simplex lattice

| Components (q) | m=2 | m=3 |
|---------------|-----|-----|
| 3 | 6 (+1 center) | 10 |
| 4 | 10 (+1 center) | 20 |
| 5 | 15 (+1 center) | 35 |
| 6 | 21 (+1 center) | 56 |

---

## Simplex Centroid Design

### Principle

A simplex centroid design includes:
- All pure components (vertices)
- All binary blends (edge midpoints)
- All ternary blends (face centroids)
- ... up to the overall centroid

For q components, there are 2^q − 1 points.

### 3-component Simplex Centroid

Total points: 7

| Run | x₁ | x₂ | x₃ | Description |
|-----|----|----|----|-------------|
| 1 | 1 | 0 | 0 | Pure 1 |
| 2 | 0 | 1 | 0 | Pure 2 |
| 3 | 0 | 0 | 1 | Pure 3 |
| 4 | 0.5 | 0.5 | 0 | Binary (1-2 edge midpoint) |
| 5 | 0.5 | 0 | 0.5 | Binary (1-3 edge midpoint) |
| 6 | 0 | 0.5 | 0.5 | Binary (2-3 edge midpoint) |
| 7 | 0.333 | 0.333 | 0.333 | Ternary (overall centroid) |

### 4-component Simplex Centroid

Total points: 15

| Run | x₁ | x₂ | x₃ | x₄ | Description |
|-----|----|----|----|----|-------------|
| 1 | 1 | 0 | 0 | 0 | Pure 1 |
| 2 | 0 | 1 | 0 | 0 | Pure 2 |
| 3 | 0 | 0 | 1 | 0 | Pure 3 |
| 4 | 0 | 0 | 0 | 1 | Pure 4 |
| 5 | 0.5 | 0.5 | 0 | 0 | Binary 1-2 |
| 6 | 0.5 | 0 | 0.5 | 0 | Binary 1-3 |
| 7 | 0.5 | 0 | 0 | 0.5 | Binary 1-4 |
| 8 | 0 | 0.5 | 0.5 | 0 | Binary 2-3 |
| 9 | 0 | 0.5 | 0 | 0.5 | Binary 2-4 |
| 10 | 0 | 0 | 0.5 | 0.5 | Binary 3-4 |
| 11 | 0.333 | 0.333 | 0.333 | 0 | Ternary 1-2-3 |
| 12 | 0.333 | 0.333 | 0 | 0.333 | Ternary 1-2-4 |
| 13 | 0.333 | 0 | 0.333 | 0.333 | Ternary 1-3-4 |
| 14 | 0 | 0.333 | 0.333 | 0.333 | Ternary 2-3-4 |
| 15 | 0.25 | 0.25 | 0.25 | 0.25 | Quaternary (overall centroid) |

### Number of runs for simplex centroid

| Components | Runs |
|-----------|------|
| 3 | 7 |
| 4 | 15 |
| 5 | 31 |
| 6 | 63 |

---

## Extreme Vertices Design

### Principle

When components have upper and lower bounds (constraints), the feasible region
is an irregular polygon inside the simplex. Extreme vertices designs sample
the vertices of this constrained region.

**When to use:**
- Each component has minimum and/or maximum constraints
- The feasible region is a subset of the full simplex
- Common in real formulations (e.g., cement must be at least X%, additive at most Y%)

### Example: Constrained 3-component blend

Constraints:
- x₁: 0.70 – 0.90
- x₂: 0.05 – 0.20
- x₃: 0.03 – 0.10
- x₁ + x₂ + x₃ = 1.0

The feasible region is a polygon inside the full simplex. The design points
are the vertices of this polygon (typically 2^q in number for q components
with both upper and lower bounds).

### Practical approach

For constrained mixture designs:
1. Define all constraints (lower and upper bounds for each component)
2. Check feasibility: do the constraints allow any valid blends?
3. Generate extreme vertices of the feasible region
4. Optionally add edge midpoints and overall centroid
5. Randomize run order

---

## Mixture Models

### Linear mixture model (first-order)

```
y = β₁x₁ + β₂x₂ + ... + β_qx_q
```

No intercept term (because of the sum-to-one constraint).
Can estimate main effects only — assumes straight-line blending.

Number of parameters: q

### Quadratic mixture model (second-order)

```
y = Σβ_i·x_i + ΣΣβ_ij·x_i·x_j   (i < j)
```

Adds binary interaction terms (non-linear blending).
Most commonly used model.

Number of parameters: q + q(q-1)/2 = q(q+1)/2

### Special cubic model

```
y = Σβ_i·x_i + ΣΣβ_ij·x_i·x_j + ΣΣΣβ_ijk·x_i·x_j·x_k   (i < j < k)
```

Adds ternary interaction terms. Use when you suspect three-component
synergies or antagonisms.

Number of parameters: q(q+1)(q+2)/6

### Full cubic model

Includes all terms up to third order, including terms like β_ij·x_i·x_j·(x_i−x_j).
Rarely needed in practice.

### Model selection guide

| Model | Parameters (q=3) | Min runs | Use when |
|-------|-----------------|----------|----------|
| Linear | 3 | 3 | Simple screening, linear blending assumed |
| Quadratic | 6 | 6 (or 7 with center) | Most common; captures curvature in binary blends |
| Special cubic | 7 | 7 | Ternary interactions suspected |
| Full cubic | 10 | 10 | Detailed characterization needed |

---

## Ternary (Triangular) Plot Interpretation

For 3-component mixtures, results are often shown on a triangular graph:

- **Vertices**: pure components (100% of one component)
- **Edges**: binary blends (two components only)
- **Interior**: all three components present
- **Contour lines**: constant response value

**Reading a ternary plot:**
- Each corner = 100% of that component
- Opposite edge = 0% of that component
- Parallel lines from edge to vertex = increasing proportion

---

## Multi-Response Optimization

### Desirability function approach

For multiple responses (e.g., strength + workability + cost):

1. For each response, define a desirability function d_i:
   - Larger is better: d = 0 at minimum, d = 1 at target
   - Smaller is better: d = 1 at minimum, d = 0 at target
   - Target is best: d = 1 at target, d = 0 at limits

2. Calculate overall desirability:
   ```
   D = (d₁ × d₂ × ... × d_m)^(1/m)
   ```

3. Find the blend that maximizes D

### Trade-off analysis

- Plot response surfaces for each property
- Identify regions where all properties meet specifications
- Choose optimum based on priorities

---

## Best Practices

1. **Start broad, then narrow**: begin with more components in a screening design, then reduce
2. **Check constraints first**: ensure your component bounds define a feasible region
3. **Randomize runs**: always randomize to protect against systematic errors
4. **Use replicates**: at least at the centroid, for pure error estimation
5. **Don't extrapolate**: mixture models are only valid inside the tested region
6. **Consider process factors too**: if both formulation and process matter,
   use a combined mixture-process design
7. **Validate with confirmation runs**: always test the predicted optimum experimentally
