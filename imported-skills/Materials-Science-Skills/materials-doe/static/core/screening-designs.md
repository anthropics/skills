# Screening Designs

Factor screening designs for identifying important factors from many candidates.
Use when you have 5+ factors and want to efficiently find the few that matter most.

## Overview

Screening designs are used in early experimentation to separate the "vital few"
factors from the "trivial many". They trade off the ability to estimate
interactions for efficiency in estimating main effects.

### When to use screening designs

- You have many candidate factors (typically 5-20+)
- You're not sure which factors actually affect the response
- You want to reduce the factor space before more detailed study
- Experiment budget is limited

### When NOT to use screening designs

- You already know which factors are important (use factorial or RSM instead)
- You need to estimate interaction effects precisely
- You have very few factors (≤4)

### Screening strategy

```
Many factors → Screening (PB/2^(k-p)) → Few key factors → Full factorial/RSM → Optimization
```

---

## Plackett-Burman Designs

### Principle

Plackett-Burman (PB) designs are two-level screening designs with:
- N runs (N is a multiple of 4: 12, 20, 24, 28, ...)
- Can estimate up to N-1 factor main effects
- Main effects are confounded with two-factor interactions
- Very efficient for factor screening

### Key properties

- All main effects are uncorrelated with each other (orthogonal)
- Main effects are partially confounded with two-factor interactions
- Use when interactions are believed to be small relative to main effects
- "Effect sparsity" principle: only a few factors are active

### L12 Plackett-Burman (up to 11 factors)

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

Note: Run 12 is all minus (baseline). Some versions use all plus as the last run,
or alternate. This version is the standard Hadamard-matrix construction.

### L20 Plackett-Burman (up to 19 factors)

| Run | A | B | C | D | E | F | G | H | I | J | K | L | M | N | O | P | Q | R | S |
|-----|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | + | + | - | - | + | + | + | + | - | + | - | + | - | + | + | - | - | - | + |
| 2 | + | + | + | - | - | + | + | + | + | - | + | - | + | - | + | + | - | - | - |
| 3 | - | + | + | + | - | - | + | + | + | + | - | + | - | + | - | + | + | - | - |
| 4 | - | - | + | + | + | - | - | + | + | + | + | - | + | - | + | - | + | + | - |
| 5 | + | - | - | + | + | + | - | - | + | + | + | + | - | + | - | + | - | + | + |
| 6 | + | + | - | - | + | + | + | - | - | + | + | + | + | - | + | - | + | - | + |
| 7 | + | + | + | - | - | + | + | + | - | - | + | + | + | + | - | + | - | + | - |
| 8 | - | + | + | + | - | - | + | + | + | - | - | + | + | + | + | - | + | - | + |
| 9 | + | - | + | + | + | - | - | + | + | + | - | - | + | + | + | + | - | + | - |
| 10 | - | + | - | + | + | + | - | - | + | + | + | - | - | + | + | + | + | - | + |
| 11 | + | - | + | - | + | + | + | - | - | + | + | + | - | - | + | + | + | + | - |
| 12 | - | + | - | + | - | + | + | + | - | - | + | + | + | - | - | + | + | + | + |
| 13 | + | - | + | - | + | - | + | + | + | - | - | + | + | + | - | - | + | + | + |
| 14 | + | + | - | + | - | + | - | + | + | + | - | - | + | + | + | - | - | + | + |
| 15 | + | + | + | - | + | - | + | - | + | + | + | - | - | + | + | + | - | - | + |
| 16 | + | + | + | + | - | + | - | + | - | + | + | + | - | - | + | + | + | - | - |
| 17 | - | + | + | + | + | - | + | - | + | - | + | + | + | - | - | + | + | + | - |
| 18 | - | - | + | + | + | + | - | + | - | + | - | + | + | + | - | - | + | + | + |
| 19 | + | - | - | + | + | + | + | - | + | - | + | - | + | + | + | - | - | + | + |
| 20 | - | - | - | - | - | - | - | - | - | - | - | - | - | - | - | - | - | - | - |

### Choosing the right PB design

| Design | Max factors | Runs |
|--------|------------|------|
| L8 | 7 | 8 |
| L12 | 11 | 12 |
| L16 | 15 | 16 |
| L20 | 19 | 20 |
| L24 | 23 | 24 |

**Recommendation:** Use the smallest design that accommodates your factors.
L12 is the most commonly used (good balance of runs and factor capacity).

### Analysis methods for PB designs

1. **Main effect estimate**: (Avg response at + level) − (Avg response at − level)

2. **Pareto chart**: Bar chart of effect magnitudes, sorted from largest to smallest.
   Helps visually identify which factors are most important.

3. **Normal probability plot**: Plot effects on normal probability paper.
   Unimportant effects fall on a straight line; important effects stand out.

4. **Half-normal plot**: Absolute effect values on probability paper.
   Similar to normal plot but all on one side.

5. **Lenth's method**: Statistical test for active effects without replication.
   Uses a pseudo-standard-error from the smallest effects.

### Practical guidance

- Start with the smallest design that fits your factors
- Usually 2-4 factors emerge as "active" from a PB study
- Follow up with a full factorial or RSM on the key factors
- Be aware that a "significant" factor might actually be an interaction
  that is aliased with that factor's main effect

---

## Fractional Factorial Designs (2^(k-p))

### Principle

A fractional factorial design uses a subset (fraction) of the full 2^k factorial runs.
The fraction is 1/2^p of the full factorial.

Notation: 2^(k-p)
- k = number of factors
- p = fraction exponent (1 = 1/2 fraction, 2 = 1/4 fraction, etc.)
- Total runs = 2^(k-p)

### Resolution

The resolution describes how effects are confounded:

| Resolution | Meaning | Example |
|------------|---------|---------|
| **III** | Main effects confounded with 2FI | 2^(3-1) (R=III if I=ABC) |
| **IV** | Main effects clear of 2FI; 2FI confounded with other 2FI | 2^(4-1) (R=IV) |
| **V** | Main effects and 2FI clear of each other; 2FI confounded with 3FI | 2^(5-1) (R=V) |

**Higher resolution is better but requires more runs.**

### 2^(3-1) Design (Resolution III, 4 runs)

Generator: C = AB (or I = ABC)

| Run | A | B | C = AB |
|-----|---|---|--------|
| 1 | - | - | + |
| 2 | + | - | - |
| 3 | - | + | - |
| 4 | + | + | + |

Alias structure:
- A = BC
- B = AC
- C = AB

### 2^(4-1) Design (Resolution IV, 8 runs)

Generator: D = ABC (or I = ABCD)

| Run | A | B | C | D = ABC |
|-----|---|---|---|---------|
| 1 | - | - | - | - |
| 2 | + | - | - | + |
| 3 | - | + | - | + |
| 4 | + | + | - | - |
| 5 | - | - | + | + |
| 6 | + | - | + | - |
| 7 | - | + | + | - |
| 8 | + | + | + | + |

Alias structure:
- All main effects are clear of 2FIs
- 2FIs are confounded with each other:
  - AB = CD, AC = BD, AD = BC

### 2^(5-1) Design (Resolution V, 16 runs)

Generator: E = ABCD (or I = ABCDE)

| Run | A | B | C | D | E = ABCD |
|-----|---|---|---|---|----------|
| 1 | - | - | - | - | + |
| 2 | + | - | - | - | - |
| 3 | - | + | - | - | - |
| 4 | + | + | - | - | + |
| 5 | - | - | + | - | - |
| 6 | + | - | + | - | + |
| 7 | - | + | + | - | + |
| 8 | + | + | + | - | - |
| 9 | - | - | - | + | - |
| 10 | + | - | - | + | + |
| 11 | - | + | - | + | + |
| 12 | + | + | - | + | - |
| 13 | - | - | + | + | + |
| 14 | + | - | + | + | - |
| 15 | - | + | + | + | - |
| 16 | + | + | + | + | + |

Alias structure:
- All main effects and 2FIs are estimable
- 2FIs are confounded with 3FIs (which are usually small)

### 2^(5-2) Design (Resolution III, 8 runs)

Generators: D = AB, E = AC (or I = ABD = ACE = BCDE)

| Run | A | B | C | D = AB | E = AC |
|-----|---|---|---|--------|--------|
| 1 | - | - | - | + | + |
| 2 | + | - | - | - | - |
| 3 | - | + | - | - | + |
| 4 | + | + | - | + | - |
| 5 | - | - | + | + | - |
| 6 | + | - | + | - | + |
| 7 | - | + | + | - | - |
| 8 | + | + | + | + | + |

### When to use fractional factorial vs Plackett-Burman

| Criterion | Fractional Factorial | Plackett-Burman |
|-----------|---------------------|-----------------|
| Factor count | 2-10 | 7-23 |
| Runs | 2^(k-p) (power of 2) | Multiple of 4 |
| Resolution | Known and controlled | Complex aliasing |
| Alias structure | Simple, systematic | Partial confounding |
| Follow-up | Easy to augment to full factorial | Need completely new design |
| Best for | Small-moderate factor count | Large factor count, initial screen |

---

## Fold-Over Designs

### Principle

Fold-over is a technique to de-alias (separate) confounded effects by adding
a second fraction with signs reversed on one or more factors.

### Full fold-over (reverse all signs)

- Doubles the number of runs
- Separates main effects from two-factor interactions
- Example: 2^(3-1) full fold-over → becomes 2^3 full factorial

### Single-factor fold-over

- Reverse signs of ONE factor only
- De-aliases that factor's main effect and all its interactions
- Useful when only one factor is suspected of having large interactions

---

## Sequential Screening Strategy

**Recommended workflow:**

1. **Phase 1: PB screening** (many factors → few key factors)
   - Run L12 or L20 PB design
   - Identify 2-4 most important factors
   - Drop the rest

2. **Phase 2: Full factorial or fractional factorial** (characterize key factors)
   - Run full 2^k factorial on the key factors (k = 2-4)
   - Estimate all main effects and 2FIs
   - Check for curvature via center points

3. **Phase 3: RSM** (optimize)
   - If curvature is significant → augment to CCD or run BBD
   - Fit quadratic model
   - Find optimal conditions

4. **Phase 4: Confirmation**
   - Run 3-5 replicates at predicted optimum
   - Verify predictions

---

## Best Practices

1. **Use screening liberally** — it's almost always cheaper than over-testing unimportant factors
2. **Don't skip screening** when you have 5+ factors — the probability of picking the right factors by intuition is low
3. **Randomize** run order
4. **Include center points** if budget allows (for curvature check)
5. **Don't overinterpret** screening results — follow up with more detailed designs
6. **Use effect sparsity** principle: expect only ~20% of factors to be important
7. **Be aware of aliasing** — a "significant factor" might be masking an interaction
