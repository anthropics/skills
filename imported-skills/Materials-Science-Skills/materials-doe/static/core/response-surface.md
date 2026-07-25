# Response Surface Methodology (RSM)

Response surface methodology for modeling and optimizing materials experiments.
Use when you have 2-5 key factors and want to find optimal conditions or understand factor interactions.

## Overview

Response Surface Methodology (RSM) is a collection of statistical techniques for
developing, improving, and optimizing processes. It fits empirical models to
experimental data using designs that efficiently explore the factor space.

### When to use RSM

- You have already screened factors and know which 2-5 are most important
- You want to find optimal factor settings for one or more responses
- You suspect curvature in the response (linear model is not enough)
- You want to understand factor interactions in detail

### When NOT to use RSM

- You have more than 5 factors (screen first with Plackett-Burman)
- You are in early exploration and don't know which factors matter
- Each experiment is extremely expensive (use more efficient designs)

### Two most common RSM designs

| Design | Factors | Runs | Advantages | Disadvantages |
|--------|---------|------|------------|---------------|
| Central Composite (CCD) | 2-5 | 2^k + 2k + c | Rotatable, covers corners | Extreme axial points may be infeasible |
| Box-Behnken (BBD) | 3-5 | 2k(k-1) + c | No extreme points, spherical | Doesn't cover factor space corners |

c = center points (typically 3-6)

---

## Central Composite Design (CCD)

### Principle

A CCD consists of three parts:

1. **Factorial points** — a 2^k full factorial (coded levels: ±1)
2. **Axial (star) points** — points along each axis at distance α from center
3. **Center points** — several replicates at the center (0, 0, ..., 0)

### Choosing α

The value of α determines the design properties:

| α value | Property | Use case |
|---------|----------|----------|
| α = 1 | Face-centered (CCF) | Factor levels cannot go beyond the extremes |
| α = 2^(k/4) | Rotatable (CCD) | Prediction variance is the same at all points equidistant from center |
| α = sqrt(k) | Spherical | All points on a sphere of radius sqrt(k) |

### Standard CCD Designs

#### CCD for 2 factors (rotatable, α = 1.414)

Total runs: 4 factorial + 4 axial + 5 center = **13 runs**

| Run | A | B | Type |
|-----|---|---|------|
| 1 | -1 | -1 | factorial |
| 2 | +1 | -1 | factorial |
| 3 | -1 | +1 | factorial |
| 4 | +1 | +1 | factorial |
| 5 | -1.414 | 0 | axial |
| 6 | +1.414 | 0 | axial |
| 7 | 0 | -1.414 | axial |
| 8 | 0 | +1.414 | axial |
| 9 | 0 | 0 | center |
| 10 | 0 | 0 | center |
| 11 | 0 | 0 | center |
| 12 | 0 | 0 | center |
| 13 | 0 | 0 | center |

#### CCD for 3 factors (rotatable, α = 1.682)

Total runs: 8 factorial + 6 axial + 6 center = **20 runs**

| Run | A | B | C | Type |
|-----|---|---|---|------|
| 1 | -1 | -1 | -1 | factorial |
| 2 | +1 | -1 | -1 | factorial |
| 3 | -1 | +1 | -1 | factorial |
| 4 | +1 | +1 | -1 | factorial |
| 5 | -1 | -1 | +1 | factorial |
| 6 | +1 | -1 | +1 | factorial |
| 7 | -1 | +1 | +1 | factorial |
| 8 | +1 | +1 | +1 | factorial |
| 9 | -1.682 | 0 | 0 | axial |
| 10 | +1.682 | 0 | 0 | axial |
| 11 | 0 | -1.682 | 0 | axial |
| 12 | 0 | +1.682 | 0 | axial |
| 13 | 0 | 0 | -1.682 | axial |
| 14 | 0 | 0 | +1.682 | axial |
| 15 | 0 | 0 | 0 | center |
| 16 | 0 | 0 | 0 | center |
| 17 | 0 | 0 | 0 | center |
| 18 | 0 | 0 | 0 | center |
| 19 | 0 | 0 | 0 | center |
| 20 | 0 | 0 | 0 | center |

#### Face-Centered CCD for 3 factors (α = 1)

Total runs: 8 factorial + 6 axial + 6 center = **20 runs**
All factor levels are at -1, 0, or +1 (no extrapolation needed).

| Run | A | B | C | Type |
|-----|---|---|---|------|
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

---

## Box-Behnken Design (BBD)

### Principle

Box-Behnken designs are rotatable (or nearly rotatable) designs with:
- All points lie on a sphere of radius sqrt(2)
- No extreme corner points (all factors never at extremes simultaneously)
- Efficient for estimating quadratic models

### BBD for 3 factors

Total runs: 12 factorial + 3 center = **15 runs** (with 3 center points)

| Run | A | B | C |
|-----|---|---|---|
| 1 | -1 | -1 | 0 |
| 2 | +1 | -1 | 0 |
| 3 | -1 | +1 | 0 |
| 4 | +1 | +1 | 0 |
| 5 | -1 | 0 | -1 |
| 6 | +1 | 0 | -1 |
| 7 | -1 | 0 | +1 |
| 8 | +1 | 0 | +1 |
| 9 | 0 | -1 | -1 |
| 10 | 0 | +1 | -1 |
| 11 | 0 | -1 | +1 |
| 12 | 0 | +1 | +1 |
| 13 | 0 | 0 | 0 |
| 14 | 0 | 0 | 0 |
| 15 | 0 | 0 | 0 |

### BBD for 4 factors

Total runs: 24 factorial + 3 center = **27 runs** (with 3 center points)

| Run | A | B | C | D |
|-----|---|---|---|---|
| 1 | -1 | -1 | 0 | 0 |
| 2 | +1 | -1 | 0 | 0 |
| 3 | -1 | +1 | 0 | 0 |
| 4 | +1 | +1 | 0 | 0 |
| 5 | -1 | 0 | -1 | 0 |
| 6 | +1 | 0 | -1 | 0 |
| 7 | -1 | 0 | +1 | 0 |
| 8 | +1 | 0 | +1 | 0 |
| 9 | -1 | 0 | 0 | -1 |
| 10 | +1 | 0 | 0 | -1 |
| 11 | -1 | 0 | 0 | +1 |
| 12 | +1 | 0 | 0 | +1 |
| 13 | 0 | -1 | -1 | 0 |
| 14 | 0 | +1 | -1 | 0 |
| 15 | 0 | -1 | +1 | 0 |
| 16 | 0 | +1 | +1 | 0 |
| 17 | 0 | -1 | 0 | -1 |
| 18 | 0 | +1 | 0 | -1 |
| 19 | 0 | -1 | 0 | +1 |
| 20 | 0 | +1 | 0 | +1 |
| 21 | 0 | 0 | -1 | -1 |
| 22 | 0 | 0 | +1 | -1 |
| 23 | 0 | 0 | -1 | +1 |
| 24 | 0 | 0 | +1 | +1 |
| 25 | 0 | 0 | 0 | 0 |
| 26 | 0 | 0 | 0 | 0 |
| 27 | 0 | 0 | 0 | 0 |

Each non-center run varies exactly two factors at ±1 and holds the other two at 0.

### When to choose BBD vs CCD

| Criterion | CCD | BBD |
|-----------|-----|-----|
| Factor space coverage | Covers corners and beyond | Spherical, no corners |
| Extreme points | Yes (axial points beyond ±1) | No (all points at 0 or ±1) |
| Number of runs (3 factors) | 20 | 15 |
| Number of runs (4 factors) | 30+ | 27 |
| Predictions at corners | Good | Interpolation needed |
| Rotatable | Yes (with right α) | Yes |
| Factor feasibility | May need extrapolation | All within tested levels |

**Guidance:**
- Use CCD if you need predictions at extreme combinations, or if you started with a factorial design and are augmenting
- Use BBD if factor levels at extremes are expensive, dangerous, or infeasible simultaneously

---

## Analysis Workflow

### Step 1: First-order model (steepest ascent)

If you are far from the optimum, start with a first-order design:

```
y = β₀ + β₁x₁ + β₂x₂ + ... + β_kx_k
```

1. Fit first-order model
2. Check for lack-of-fit (center points provide curvature test)
3. If significant curvature → move to second-order (CCD/BBD)
4. If no curvature → follow path of steepest ascent
5. Stop when curvature detected or limits reached

### Step 2: Second-order model (quadratic)

For optimization, fit a full quadratic model:

```
y = β₀ + Σβ_i·x_i + ΣΣβ_ij·x_i·x_j + Σβ_ii·x_i²
```

Includes:
- Linear terms (β_i): main effects
- Interaction terms (β_ij): two-factor interactions
- Quadratic terms (β_ii): curvature

### Step 3: ANOVA table structure

| Source | DF |
|--------|----|
| Model | p-1 |
|   Linear | k |
|   Interaction | k(k-1)/2 |
|   Quadratic | k |
| Residual | n-p |
|   Lack-of-fit | n-p - n_c+1 |
|   Pure error | n_c-1 |
| Total | n-1 |

n = total runs, p = number of terms, k = number of factors, n_c = center points

### Step 4: Response surface visualization

- **2 factors**: 3D surface plot + contour plot
- **3 factors**: Contour plots for pairs of factors at fixed levels of the third
- **4+ factors**: Select the 2 most important factors for visualization

### Step 5: Optimization

**Single-response optimization:**
- Find factor settings that maximize/minimize the response
- Check if optimum is inside the design region or at boundary
- Run confirmation experiments at predicted optimum

**Multi-response optimization:**
- Desirability function approach:
  - For each response, compute desirability d_i (0 to 1)
  - Overall desirability D = (d₁·d₂·...·d_m)^(1/m)
  - Find factor settings that maximize D
- Pareto front approach for conflicting objectives

---

## Coded vs Actual Units

All designs above use coded units (-1, 0, +1). Convert to actual units:

```
Actual = Center + (Coded × Step)
```

where:
- Center = (High + Low) / 2
- Step = (High - Low) / 2

**Example:** Factor A with low=4%, high=8%
- Center = 6%
- Step = 2%
- Coded -1 → 4%
- Coded 0 → 6%
- Coded +1 → 8%
- Coded +1.414 (axial) → 6 + 1.414×2 = 8.83%

---

## Best Practices

1. **Randomize run order** to protect against time-related confounds
2. **Include center points** (3-6 replicates) for curvature detection and pure error
3. **Screen first** with PB or fractional factorial before RSM if you have many factors
4. **Check model assumptions**: normality, constant variance, outliers
5. **Run confirmation experiments** at predicted optimal conditions
6. **Don't extrapolate** beyond the design region — predictions are unreliable
