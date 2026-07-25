# Methods catalog — purpose · assumptions · computation · report format · pitfalls

**Load when:** a method has been selected. Each entry gives the exact assumptions to check (details in
`assumptions-diagnostics.md`), how to compute it (functions in `scripts/stats_toolkit.py`), the
**report-ready output**, and the pitfall that most often invalidates it.

Report every result as a complete tuple. Skeleton: `statistic(df) = value, p = value, effect = value,
95% CI [lo, hi]`.

---

## Descriptive statistics & dispersion
- **Use for:** characterising one variable before any test.
- **Report:** `n`, mean (SD) *or* median [IQR] if skewed, min–max, **CV = SD/mean** for comparing
  variability across series on different scales.
- **Pitfall:** reporting a mean for a skewed or bimodal distribution. Check skew; if |skew| > 1, lead
  with the median. The CV is meaningless for data that can be zero or negative.

## Confidence intervals
- **Use for:** the uncertainty of any estimate — always, not optionally.
- **Compute:** t-based CI for a mean of ~normal data; **bootstrap CI** (10,000 resamples, percentile
  or BCa) for medians, ratios, Gini, or any statistic without a clean formula.
- **Report:** `estimate, 95% CI [lo, hi]`. A CI that excludes the null value implies significance at
  that α; a CI that contains it does not.
- **Pitfall:** interpreting "95% CI" as "95% probability the parameter is inside." It is a coverage
  statement about the procedure. Report it; don't over-narrate it.

## t-tests (one-sample, independent Welch, paired)
- **Assumptions:** approximately normal (or large n); independent observations; for paired, the
  *differences* are what must be ~normal.
- **Compute:** `t_onesample`, `t_independent` (Welch by default), `t_paired`.
- **Report:** `t(df) = 2.61, p = 0.013, d = 0.83, 95% CI of the difference [0.19, 1.46]`. Cohen's d:
  0.2 small, 0.5 medium, 0.8 large. Use **Hedges' g** for n < 20.
- **Pitfall:** using an independent-samples test on paired data (before/after the same farms) throws
  away the pairing and loses power; using Student's t under unequal variance inflates error.

## One-way ANOVA (+ post-hoc)
- **Assumptions:** normal residuals; homogeneous variances (Levene); independence.
- **Compute:** `one_way_anova` → F, p, **η²** and **ω²** (less biased). Follow a significant F with
  **Tukey HSD** for all pairwise comparisons (already multiplicity-controlled).
- **Report:** `F(2, 87) = 22.94, p < 0.0001, ω² = 0.33`, then the Tukey table of which pairs differ.
- **Pitfall:** running many pairwise t-tests instead of ANOVA+Tukey (multiplicity), or reading a
  significant F as "all groups differ" — it says *at least one* pair differs; Tukey says which.

## Non-parametric comparisons
- **Mann-Whitney U** (two independent), **Wilcoxon signed-rank** (paired), **Kruskal-Wallis** (k
  groups) → **Dunn's test** (BH-adjusted) post-hoc.
- **Report:** `U = 512, p = 0.008, rank-biserial r = 0.41` (or Kruskal `H(2) = 11.3, p = 0.004`).
- **Pitfall:** claiming these "compare medians" unconditionally — they compare distributions/stochastic
  dominance; equal shapes are needed to read them purely as a median difference.

## Correlation
- **Pearson r** (linear, numeric), **Spearman ρ** / **Kendall τ** (monotonic/ordinal).
- **Report:** `r = +0.924, p = 0.025, 95% CI [0.31, 0.99], R² = 0.854`. Sign explicit.
- **Pitfall:** correlation ≠ causation, and r captures only *linear* structure — always eyeball the
  scatter first (a curve or a single leverage point can manufacture or hide r).

## Chi-square / Fisher (categorical association)
- **Assumptions:** independent observations; expected count ≥ 5 in ~all cells (else **Fisher's exact**).
- **Report:** `χ²(df) = 9.4, p = 0.009, Cramér's V = 0.21`.
- **Pitfall:** using chi-square on small or sparse tables; using it on paired categorical data (use
  **McNemar** for before/after on the same units).

## OLS / multiple regression
- **Assumptions:** linearity, independent errors, homoskedasticity, ~normal residuals, no severe
  multicollinearity (VIF < 5–10). See `assumptions-diagnostics.md`.
- **Compute:** `ols_fit` with **HC3 robust SE by default**; check VIF, Breusch-Pagan, Durbin-Watson,
  Cook's distance.
- **Report per coefficient:** `β = 3.21, SE = 0.74, t = 4.34, p < 0.001, 95% CI [1.75, 4.67]`; model:
  `R² = 0.998, adj-R² = 0.996, F(3, 46) = 812, p < 0.0001, n = 50`. Prefer **adjusted R²** when
  comparing models with different predictor counts.
- **Pitfall:** reading β as causal without design/controls; chasing R² by adding predictors
  (overfitting) — adjusted R² and out-of-sample check guard against it.

## Fixed-effects regression (the report's workhorse for "hold the unit constant")
- **Use for:** panel data (entity × time) when the objection is that units are not comparable. Entity
  dummies absorb every time-invariant difference between units, so β reflects the **within-unit**
  relationship.
- **Compute:** `fixed_effects(df, y, x, entity=...)` — OLS with `C(entity)` and cluster-robust SE by
  entity.
- **Report:** the coefficient(s) of interest, note "entity fixed effects included; SE clustered by
  entity," within-R², and n (obs) with the number of entities and periods.
- **Pitfall:** including a variable that never varies within a unit (it is collinear with the fixed
  effect and drops out); too few periods per entity to identify the effect.

## Logistic regression (binary outcome)
- **Report odds ratios,** not raw log-odds: `OR = 2.4, 95% CI [1.3, 4.5], p = 0.006`. Report model fit
  (pseudo-R², AUC) and n with the event count.
- **Pitfall:** rare events (need ≥ ~10 events per predictor); reporting β instead of the interpretable OR.

## Inequality & diversity indices
- **Gini** (0 equal → 1 concentrated): concentration of a total across units. Pair with a **bootstrap
  CI** since its sampling distribution has no simple closed form.
- **HHI** = Σ(share in %)²: <1500 low, 1500–2500 moderate, >2500 high concentration.
- **Shannon-Wiener** H = −Σ pᵢ ln pᵢ with **evenness** = H / ln(S): diversity of category counts.
- **Report:** `Gini = 0.42, 95% CI [0.35, 0.49]`; `H = 1.567 (evenness 0.680, S = 10)`.
- **Pitfall:** comparing Shannon H across datasets with different category counts S without reporting
  evenness; computing Gini on data containing negative values.

## Trend
- **Linear slope:** `β per period, p, 95% CI` from OLS on time. **Mann-Kendall:** `τ, S, p` — monotonic
  trend with no linearity/normality assumption; robust to outliers. **CAGR** for compound growth of a total.
- **Pitfall:** fitting a line to a series with a structural break or seasonality; extrapolating beyond
  the observed window without labelling it a projection and stating the basis.

## Outlier detection
- **IQR fence:** outside `Q1 − 1.5·IQR, Q3 + 1.5·IQR`. **Modified z-score** (median/MAD based, robust):
  |Mᵢ| > 3.5. Prefer the modified z-score; the plain z-score is itself distorted by the outliers it
  hunts.
- **Pitfall:** deleting outliers reflexively. Investigate first — an outlier may be the finding (a
  failing PPIT, a data-entry error, a genuine extreme). Report what was excluded and why.
