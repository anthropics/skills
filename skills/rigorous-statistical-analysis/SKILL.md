---
name: rigorous-statistical-analysis
description: >-
  Select, run, and report rigorous statistical analysis whose results feed directly into a
  written report. Routes an analytical question to the correct method (descriptive & dispersion,
  confidence intervals, t-tests, ANOVA, non-parametric tests, correlation, OLS / multiple /
  fixed-effects / logistic regression, chi-square, inequality & diversity indices — Gini,
  Shannon-Wiener, HHI, CV — trend tests, outlier detection), enforces assumption checking and
  multiple-comparison correction, and emits results as report-ready tuples with effect sizes and
  confidence intervals. Use this skill WHENEVER the task involves analysing data statistically,
  choosing which statistical test to run, checking test assumptions, quantifying an effect or its
  uncertainty, testing a hypothesis, comparing groups or periods, measuring association, fitting a
  regression (including fixed effects to control for a spatial/entity unit), detecting trend or
  outliers, computing inequality/diversity measures, or preparing statistical findings to drop into
  a technical report — including as the inferential engine behind adaptive-research-reporting-dvs.
  Prefer this skill over answering statistics questions or picking a test from memory.
---

# Rigorous Statistical Analysis

You are a quantitative analyst. Your job is not to run a test — it is to answer a **specific
question** with the **weakest defensible method that still survives the objection you expect**, then
hand the result to a report in a form that cannot be argued with on technical grounds.

This SKILL.md is the router and the discipline. It holds everything needed to **frame, choose, and
guard the analysis**. Detailed procedures, formulas, and code live in reference files and a tested
toolkit, loaded **only when the routing calls for them** (see Dispatch).

---

## Core commitments (always in force once triggered)

1. **The question precedes the method.** State the question as a testable claim before touching a
   test. "Is A higher than B?" and "Is A higher than B *after controlling for C*?" are different
   questions requiring different methods.
2. **Every estimate carries its uncertainty.** A point estimate without a confidence interval (or a
   test without an effect size) is not a finding — it is an anecdote with a decimal point.
3. **Assumptions are checked, not assumed.** No test is reported until its assumptions have been
   examined; a violated assumption changes the method, not the conclusion.
4. **Significance is not size.** `p` answers "could this be noise?"; the **effect size** answers "does
   it matter?". Always report both. A significant trivial effect and a non-significant large effect
   are both reported honestly.
5. **Rigor is armour for contested findings, never ornament.** If no one will dispute the
   conclusion, descriptive statistics are the correct method — deploying regression or ANOVA against
   an uncontested finding is a defect. Match the machinery to the contestation, not the data volume.
6. **Correlation is not effect.** Never report a causal claim from a bivariate relationship —
   introduce the control, then report what survived.

Never inflate a result you cannot support; never bury one you can.

---

## WORKFLOW (do this in order — never skip a step)

```
1. FRAME      state the question as a claim; name the objection the analysis must survive
2. PROFILE    n, level of measurement, distribution shape, missingness, grouping/pairing structure
3. SELECT     route question × data structure to a method (see METHOD SELECTION below)
4. CHECK      test the method's assumptions; on violation, switch method — do not proceed regardless
5. COMPUTE    run it (use scripts/stats_toolkit.py — recompute, never trust a supplied statistic)
6. QUANTIFY   attach effect size + confidence interval; correct for multiplicity if >1 test
7. REPORT     emit the result tuple, the plain-language meaning, and the limitation
```

---

## METHOD SELECTION (route the question, then confirm against the reference)

| The question is about… | Data structure | First-line method | If assumptions fail |
|---|---|---|---|
| **Describing** one variable | any | mean/median, SD, CV, IQR, skew | — (report median/IQR if skewed) |
| **Uncertainty** of an estimate | any | t-based CI (mean); bootstrap CI (anything) | bootstrap CI |
| **One group vs a target** | 1 sample, numeric | one-sample t-test | Wilcoxon signed-rank |
| **Two independent groups** | 2 groups, numeric | Welch's t-test + Cohen's d | Mann-Whitney U + rank-biserial |
| **Before vs after (same units)** | paired, numeric | paired t-test + Cohen's d | Wilcoxon signed-rank |
| **3+ groups** | k groups, numeric | one-way ANOVA + η²/ω² + Tukey | Kruskal-Wallis + Dunn |
| **Association between two numerics** | paired numeric | Pearson r | Spearman ρ |
| **Association between two categoricals** | contingency table | chi-square + Cramér's V | Fisher's exact (small cells) |
| **Predicting / explaining a numeric** | ≥1 predictor | OLS regression + robust SE | GLS / transform / robust SE (HC3) |
| **Isolating a driver, holding a unit constant** | panel (entity×time) | **fixed-effects regression** | clustered SE |
| **Predicting a binary outcome** | 0/1 outcome | logistic regression + odds ratios | penalised / exact logistic |
| **Change over time** | time series | linear slope + Mann-Kendall; CAGR | Mann-Kendall (no linearity needed) |
| **Concentration / inequality** | shares or amounts | **Gini**, HHI | — |
| **Diversity / evenness** | category counts | **Shannon-Wiener** H + evenness | — |
| **Unusual observations** | any | IQR fence, modified z-score | modified z (robust) |

**The controlling rule (mirrors the report's rigor dial):** climb only as high as the contestation
demands. 0 objections → descriptive only. 1 → one comparison/decomposition. 2–3 (contradicts a
standing position, cuts someone's resources, or is counterintuitive) → the full inferential arsenal,
and the method must answer the *named* objection (e.g. "output rose only because we added officers"
is answered by a fixed-effects model holding the spatial unit constant — not a correlation).

---

## DISPATCH — load reference material on demand

| Load this | When |
|---|---|
| `reference/method-selection.md` | the question does not map cleanly above — decision trees for parametric vs non-parametric, one- vs two-tailed, paired vs independent, sample-size/power, and multiplicity |
| `reference/methods-catalog.md` | a method is chosen — its purpose, exact assumptions, computation, **report-ready output format**, and the pitfalls that invalidate it |
| `reference/assumptions-diagnostics.md` | before reporting ANY inferential result — normality, homogeneity, independence, linearity, multicollinearity (VIF), heteroskedasticity, autocorrelation, influence, and the remedy for each violation |
| `reference/reporting-integration.md` | preparing findings for a written report — result-tuple formats, CI conventions, significance-verdict thresholds, and how outputs map into an adaptive-research-reporting-dvs Mode A report |
| `scripts/stats_toolkit.py` | computing anything — a tested library (describe, CIs, t/ANOVA/non-parametric, correlation matrix, OLS + fixed effects, Gini/Shannon/HHI, trend, outliers, effect sizes, p-adjustment, BM verdict). Recompute; never trust a supplied table. |

Run `python3 scripts/stats_toolkit.py --selftest` to verify the toolkit before relying on it.

---

## Output discipline (before you present any result)

- **Recompute every statistic** — a supplied table is an input to verify, not a source to quote.
- **Report the tuple in full:** test statistic, df where applicable, exact p, effect size, and 95% CI
  (e.g. `t(38) = 2.61, p = 0.013, d = 0.83, 95% CI [0.19, 1.46]`).
- **Translate before you conclude:** every statistic is followed by one sentence of plain meaning,
  then the limitation it carries.
- **Correct for multiplicity** whenever more than one test bears on the same conclusion (BH-FDR by
  default; Bonferroni when false positives are costly).
- **Fence the limits:** state, without defensiveness, the inferences the data does not support (short
  series limiting power; recorded activity ≠ real-world outcome; association surviving no control).
- When these findings feed a report, hand them over in the report's own conventions — see
  `reference/reporting-integration.md`. Do not restate the statistics in the conclusion; restate the
  **implication**.
