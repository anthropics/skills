# Assumptions & diagnostics — check before reporting, remedy on violation

**Load when:** any inferential result is about to be reported. A violated assumption changes the
method, not the conclusion. For each assumption: how to test it, how to read the test, and what to do
when it fails.

---

## For t-tests and ANOVA

| Assumption | Diagnostic | Read | On violation |
|---|---|---|---|
| Normality (of values, or of paired differences) | Shapiro-Wilk `W, p`; Q-Q plot | p < 0.05 → non-normal (but with large n, mild non-normality is fine — CLT) | switch to Mann-Whitney / Wilcoxon / Kruskal-Wallis, **or** rely on CLT if n large |
| Homogeneity of variance | Levene's test `W, p` | p < 0.05 → variances differ | use **Welch's** t/ANOVA (does not assume equal variance) |
| Independence | design knowledge | clustered/repeated sampling breaks it | mixed model / clustered SE / paired test |

**Note:** normality tests are themselves powered by n — with large samples they flag trivial
departures; with tiny samples they miss real ones. Read Shapiro *alongside* a Q-Q plot and the
histogram, never alone.

## For correlation and OLS regression

| Assumption | Diagnostic | Read | On violation |
|---|---|---|---|
| Linearity | residuals-vs-fitted plot; component-plus-residual | curvature in residuals | transform (log/Box-Cox), add polynomial/spline, or use a non-linear model |
| Independent errors (no autocorrelation) | **Durbin-Watson** | ≈2 good; <1.5 or >2.5 → autocorrelation | time-series model, Newey-West SE, add lag |
| Homoskedasticity (constant error variance) | **Breusch-Pagan** `LM, p`; residual fan-shape | p < 0.05 → heteroskedastic | **HC3 robust SE** (default here), or transform outcome |
| Normality of residuals | Shapiro on residuals; Q-Q | matters mainly for small-n inference | large n → CLT; else bootstrap or transform |
| No multicollinearity | **VIF** per predictor | VIF > 5 caution, > 10 serious | drop/combine collinear predictors; centre interaction terms |
| No overly influential points | **Cook's distance** | Dᵢ > 4/n flags influence | inspect the point; report fit with and without it |

**Default posture:** report **HC3 robust standard errors** for OLS unless you have verified
homoskedasticity. Robust SE cost almost nothing when errors are well-behaved and protect the p-values
when they are not.

## For chi-square

- Expected count ≥ 5 in essentially all cells (compute the expected table, not just the observed).
  Any expected cell < 5 → **Fisher's exact test**.
- Observations independent; each unit counted once. Paired/repeated categorical data → **McNemar**.

## For fixed-effects / panel models

- Enough within-unit variation and periods to identify the effect; a predictor constant within a unit
  is collinear with the fixed effect and cannot be estimated.
- Cluster standard errors by the entity to allow within-unit correlation over time.

## The general discipline

1. **Profile first.** Histogram, box plot, and summary before any test — most assumption failures are
   visible before they are tested.
2. **Test the assumption that matters for *this* method** — do not run every diagnostic reflexively.
3. **On violation, switch method openly** — never report a test whose assumption you know is broken,
   and never present the assumption check as a formality that "passed" without showing the number.
4. **Record the check in the limitation**, e.g. "residuals were heteroskedastic (Breusch-Pagan
   p = 0.01); HC3 robust standard errors are reported."
