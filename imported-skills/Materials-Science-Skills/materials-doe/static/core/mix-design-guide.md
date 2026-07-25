# Mix Design Guide

Domain-specific mix design methods for concrete, mortar, polymer blends, ceramic slurries, and other proportioned material systems.

## When to Use Mix Design Mode

Use mix design mode when:

- The material system requires proportions that sum to a total (e.g., cement + sand + gravel + water = 1 m³ concrete).
- Factor levels are not independent — changing one proportion affects all others.
- The goal is to find a mix that meets target strength, workability, and durability requirements.

Do NOT use mix design mode for additive dosage studies, curing condition studies, or other factorial experiments where factors are independent.

## Method 1: Dense Packing (Furnas Model)

### Principle

Optimize particle packing density by combining aggregate fractions of different sizes so that smaller particles fill the voids between larger ones.

### Procedure

1. Determine the particle size distribution of each available aggregate fraction.
2. Calculate the packing density of each fraction individually.
3. Use the Furnas model to compute the optimal volume fraction for each size class:

$$V_{\text{fine}} = \frac{V_{\text{void,coarse}}}{V_{\text{void,coarse}} + V_{\text{void,fine}}}$$

4. Iterate for multiple size classes (coarse → medium → fine).
5. Verify with packing density measurement (ASTM C29 or equivalent).

### Output

| Fraction | Size Range (mm) | Volume Fraction (%) | Mass (kg/m³) |
|----------|----------------|--------------------:|-------------:|
| Coarse | 10–20 | — | — |
| Medium | 5–10 | — | — |
| Fine (sand) | 0.15–5 | — | — |
| Filler (<0.15) | <0.15 | — | — |

### Constraints

- Specify total volume (e.g., 1 m³).
- Specify minimum/maximum packing density target.
- Specify gradation requirements if applicable (e.g., Fuller curve).

## Method 2: Volume Method (ACI 211.1)

### Principle

Proportion concrete by absolute volume: the sum of volumes of cement, water, air, coarse aggregate, and fine aggregate equals 1 m³.

### Procedure

1. **Select target slump and w/c ratio** based on strength requirement.
2. **Estimate water content** from ACI 211.1 Table 6.3.3 based on slump and aggregate size.
3. **Calculate cement content** from water content and w/c ratio.
4. **Estimate coarse aggregate volume** from ACI 211.1 Table 6.3.6 based on fineness modulus.
5. **Calculate fine aggregate volume** by subtracting all other volumes from 1 m³.
6. **Adjust for air content** (entrained or non-entrained).

### Calculation template

| Component | Formula | Value | Unit |
|-----------|---------|-------|------|
| Water | Selected from table | — | kg/m³ |
| Cement | Water / w/c | — | kg/m³ |
| Coarse aggregate | Volume × bulk density | — | kg/m³ |
| Fine aggregate | 1 m³ − sum of other absolute volumes | — | kg/m³ |
| Air content | From exposure condition table | — | % |

### Absolute volume formula

$$V_i = \frac{m_i}{\rho_i \times 1000}$$

where $m_i$ is mass (kg/m³) and $\rho_i$ is specific gravity of component $i$.

### Constraints

- Target compressive strength (MPa) at 28 days.
- Target slump (mm).
- Maximum w/c ratio (from durability exposure class).
- Minimum cement content (from exposure class).
- Air content requirement (if freeze-thaw exposure).
- Aggregate specific gravity and absorption.

## Method 3: Empirical Formula Method

### Principle

Use regression formulas derived from experimental data to predict mix proportions from target properties.

### Common formulas

**Abrams' law** (strength vs. w/c):

$$f_c = \frac{A}{B^{w/c}}$$

where $A$ and $B$ are material-dependent constants (typically $A \approx 140$, $B \approx 4.5$ for OPC concrete in MPa).

**Bolomey's formula**:

$$f_c = A \cdot (c/w - B)$$

where $A$ and $B$ are constants depending on cement type and aggregate.

### Procedure

1. Collect calibration data from prior experiments or literature.
2. Fit regression model (linear, power, or exponential).
3. Use the fitted model to predict proportions for the target property.
4. Validate with at least 3 confirmation trials.

### Constraints

- Minimum data points for regression: 10 (ideally 20+).
- Report R² and prediction interval.
- Do not extrapolate beyond the calibration range.

## Mix Design Output Template

After completing any mix design method, produce the following output table:

| Property | Target | Achieved | Method |
|----------|--------|----------|--------|
| 28-day compressive strength (MPa) | — | — | — |
| Slump (mm) | — | — | — |
| w/c ratio | — | — | — |
| Air content (%) | — | — | — |
| Cement content (kg/m³) | — | — | — |
| Water content (kg/m³) | — | — | — |
| Coarse aggregate (kg/m³) | — | — | — |
| Fine aggregate (kg/m³) | — | — | — |

## Constraints to Specify

Before starting any mix design, confirm these constraints with the user:

1. **Target strength** — compressive strength at 28 days (MPa).
2. **Workability** — slump (mm) or flow (%) requirement.
3. **Durability exposure class** — determines maximum w/c, minimum cement, air content.
4. **Available materials** — cement type, aggregate sizes and properties, admixtures.
5. **Standard** — ACI 211.1, EN 206, GB/T 50080, or project-specific specification.
6. **Special requirements** — self-compacting, high-performance, lightweight, fiber-reinforced.
