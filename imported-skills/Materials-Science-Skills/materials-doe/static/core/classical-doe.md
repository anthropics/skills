# Classical DOE Procedures

Standard design-of-experiments procedures for materials science and engineering research when orthogonal arrays are not appropriate.

## Single-Factor Design

Use when studying the effect of one factor (e.g., curing temperature, additive dosage, water-cement ratio) on a response.

### Procedure

1. **Define the factor** — name, unit, and range of interest.
2. **Select levels** — choose 3–5 evenly spaced levels spanning the range, plus a control (baseline) level.
3. **Define the response** — compressive strength, slump, setting time, etc.
4. **Determine replications** — minimum 3 replicates per level for error estimation.
5. **Randomize run order** — to minimize systematic bias from batch effects or environmental drift.
6. **Conduct experiments** — record all responses.
7. **Analyze** — one-way ANOVA, post-hoc tests (Tukey HSD or Duncan) if F is significant.

### Design table template

| Run | Factor Level | Replicate | Response |
|-----|-------------|-----------|----------|
| 1 | Control | 1 | — |
| 2 | Control | 2 | — |
| 3 | Control | 3 | — |
| 4 | Level 1 | 1 | — |
| ... | ... | ... | ... |

### Analysis

- One-way ANOVA to test $H_0$: all level means are equal.
- If rejected, post-hoc pairwise comparison to identify which levels differ.
- Report: F-statistic, p-value, means ± standard deviation per level.

## Multi-Factor Design (One-Factor-at-a-Time, OFAT)

Use when studying 2–3 factors independently, one at a time. Simpler than full factorial but cannot detect interactions.

### Procedure

1. **Fix all factors at baseline levels.**
2. **Vary factor A** across its levels while holding B and C at baseline. Record responses.
3. **Set A at its best level.** Vary factor B across its levels while holding C at baseline.
4. **Set B at its best level.** Vary factor C across its levels.
5. **The combined best levels form the recommended combination.** Note: this is NOT guaranteed to be the true optimum because interactions are ignored.

### Example (3 factors, 3 levels each)

| Phase | A | B | C | Runs |
|-------|---|---|---|------|
| Phase 1 | 1, 2, 3 | Baseline | Baseline | 3 × replications |
| Phase 2 | Best | 1, 2, 3 | Baseline | 3 × replications |
| Phase 3 | Best | Best | 1, 2, 3 | 3 × replications |

Total: 9 × replications (vs. 27 for full factorial, or 9 for L9 orthogonal with no replication).

### Limitations

- Cannot detect factor interactions.
- Order of factor testing can influence the final recommendation.
- Not guaranteed to find the global optimum.
- More runs than an equivalent orthogonal design for the same number of factors.

## When to Use Classical vs Orthogonal

| Criterion | Classical (Single/OFAT) | Orthogonal (L-array) |
|-----------|------------------------|---------------------|
| Number of factors | 1–2 | 3–6 |
| Interaction suspected | Yes (full factorial) or No (OFAT) | No (assumed negligible) |
| Goal | Detailed characterization of one factor | Screening: identify important factors efficiently |
| Replication | Required (≥3 per level for ANOVA) | Recommended (≥1 per run) |
| Run budget | Flexible | Fixed by array size (9, 16, 25) |
| Analysis | ANOVA + post-hoc | Range analysis (R), optionally ANOVA |
| Control group | Explicit baseline required | Implicit (all levels compared) |

## Full Factorial (when interactions matter)

For 2–3 factors with suspected interactions, use a full factorial design:

- 2 factors × 3 levels = 9 treatment combinations
- 3 factors × 2 levels = 8 treatment combinations
- 3 factors × 3 levels = 27 treatment combinations

Full factorial allows estimation of all main effects and all interaction terms. Use when:

- Interaction between factors is physically plausible (e.g., water-cement ratio × superplasticizer dosage).
- The number of treatment combinations is manageable (≤27 with replication).
- The research question requires understanding how factors jointly affect the response.

### Analysis for full factorial

- Two-way or three-way ANOVA with interaction terms.
- Interaction plots to visualize factor dependencies.
- If interaction is significant, main effects alone are misleading — report interaction effects prominently.
