# Method selection — decision trees

**Load when:** the question does not map cleanly to the SKILL.md router, or you must justify a choice
between two candidate methods.

---

## 1. Comparing central tendency

```
How many groups?
├─ 1 group vs a fixed target value
│    numeric, ~normal ...... one-sample t-test
│    numeric, skewed/small . Wilcoxon signed-rank (vs hypothesised median)
├─ 2 groups
│    independent units
│      ~normal ............. Welch's t-test   (default; do NOT assume equal variance)
│      skewed / ordinal .... Mann-Whitney U
│    same units, two times (paired)
│      ~normal differences . paired t-test
│      skewed differences .. Wilcoxon signed-rank
└─ 3+ groups
     independent, ~normal ... one-way ANOVA → if significant, Tukey HSD (all pairs)
     independent, skewed .... Kruskal-Wallis → if significant, Dunn's test (BH-adjusted)
     repeated measures ...... repeated-measures ANOVA / Friedman (non-parametric)
```
**Default to Welch, not Student.** Equal-variance t-tests inflate error under heteroskedasticity for
no benefit; Welch reduces to Student when variances are equal.

## 2. Measuring association

```
Both variables numeric?
├─ yes, linear & ~bivariate-normal .... Pearson r      (report r, p, 95% CI, R²=r²)
├─ yes, monotonic but non-linear ....... Spearman ρ    (rank correlation)
├─ one numeric, one ordinal ............ Spearman ρ / Kendall τ (small n, many ties → τ)
└─ both categorical .................... chi-square + Cramér's V ; Fisher's exact if any expected cell <5
```
Correlation is symmetric and unit-free; it is **not** a controlled effect. If a third variable could
drive both, escalate to regression with that variable included.

## 3. Explaining / predicting an outcome

```
Outcome type?
├─ continuous ............... OLS (multiple regression); report robust (HC3) SE by default
│     panel data (entity×time) → FIXED-EFFECTS regression: entity dummies absorb all
│                                time-invariant differences between units → isolates the
│                                within-unit driver. Cluster SE by entity.
│     strong non-linearity ... transform (log/Box-Cox) or add polynomial/spline terms
├─ binary (0/1) ............. logistic regression; report odds ratios + 95% CI, not raw β
├─ count ................... Poisson / negative-binomial (if over-dispersed)
└─ time-to-event ........... survival (Cox) — out of scope here; flag for specialist tooling
```
**When to reach for fixed effects (the report's workhorse):** whenever the objection is "the units
aren't comparable" or "it's really just differences between states/farms/zones." Fixed effects hold
the unit constant and answer the objection structurally, not rhetorically.

## 4. Trend over time

```
Is the series roughly linear?
├─ yes ..... OLS slope (β per period) + Mann-Kendall as a distribution-free confirmation
└─ no/unsure Mann-Kendall τ (monotonic trend, no linearity or normality assumption)
Growth of a total over a span .... CAGR = (end/begin)^(1/periods) − 1
Index series with different scales to a common base year before comparing trends.
```

## 5. Concentration, inequality, diversity

| Question | Measure | Range / reading |
|---|---|---|
| How unequally is a total shared across units? | **Gini** | 0 = perfectly equal, →1 = one unit holds all |
| Market/production concentration | **HHI** = Σ(share%)² | <1500 low, 1500–2500 moderate, >2500 high |
| How diverse / even are category counts? | **Shannon-Wiener** H = −Σ pᵢ ln pᵢ | 0 = one category; ln(S) = perfectly even |
| Evenness (diversity vs the max possible) | H / ln(S) | 0–1; 1 = all categories equal |

## 6. Parametric vs non-parametric — the honest test

Use a **parametric** test (t, ANOVA, Pearson, OLS) when: the numeric outcome is roughly normal *or*
n is large enough for the CLT (rule of thumb n ≥ 30 per group for means), variances are examined, and
observations are independent. Use a **non-parametric** test when: the sample is small and skewed, the
data are ordinal, or outliers dominate. Non-parametric tests trade a little power for robustness —
that trade is correct precisely when the parametric assumptions are shaky.

## 7. One-tailed vs two-tailed

Default to **two-tailed.** Use one-tailed only when a directional hypothesis was fixed *before* seeing
the data and a result in the opposite direction would be treated as no effect. Switching to one-tailed
after seeing the data to cross α is p-hacking.

## 8. Sample size / power (do this before, not after)

- Under-powered studies do not "fail to find" an effect — they cannot see one. A non-significant
  result from a tiny sample is uninformative, not evidence of no effect.
- Rough guides: detecting a **medium** effect (d ≈ 0.5) at α = 0.05, power 0.80 needs ~64/group for a
  two-sample t-test; a **large** effect (d ≈ 0.8) needs ~26/group. Correlations need ~85 (r = 0.3) or
  ~30 (r = 0.5) observations.
- When n is fixed and small, say so in the limitation and prefer estimation (CI) over a yes/no test.

## 9. Multiplicity — the silent inflator

Running k independent tests at α = 0.05 makes the chance of ≥1 false positive ≈ 1 − 0.95ᵏ (5 tests →
23%; 20 tests → 64%). Whenever several tests support one conclusion, or you scan many comparisons:
- **BH-FDR** (Benjamini-Hochberg) by default — controls the expected false-discovery proportion,
  retains power for exploratory work.
- **Bonferroni** when a single false positive is costly (few, confirmatory, high-stakes tests).
State which correction was applied and over how many tests.
