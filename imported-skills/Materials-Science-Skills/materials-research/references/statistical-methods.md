# Statistical Methods for Materials Science

Use this reference when a manuscript claim depends on numerical comparison, dosage optimization, durability retention, or multi-factor test results.

## Minimum Reporting Contract

Every quantitative claim should state:

- sample size or replicate count per group.
- mean plus uncertainty type, such as SD, SE, 95% CI, or IQR.
- test standard and specimen condition.
- statistical method and significance threshold if significance is claimed.
- exact p value when available, not only `p < 0.05`.

Do not write `significantly improved` unless a statistical test or pre-registered engineering threshold supports the word `significantly`.

## Method Selection

Decision tree:

1. Is the result only a single group or a single formulation? Use descriptive statistics only.
2. Are there two independent groups, such as control vs modified? Use Welch t-test by default unless equal variance is justified.
3. Are the same specimens measured before and after aging? Use paired t-test for normal paired differences; otherwise use Wilcoxon signed-rank.
4. Are there three or more dosage groups? Use one-way ANOVA plus Tukey HSD if assumptions are acceptable; otherwise Kruskal-Wallis plus Dunn-style post-hoc comparison.
5. Are there two factors, such as epoxy content and curing time? Use two-way ANOVA and report interaction effects.
6. Is the goal correlation between continuous variables, such as viscosity and bond strength? Use Pearson for approximately normal linear relationships and Spearman for monotonic or non-normal relationships.
7. Is the goal dosage-response modelling? Fit the simplest justified model; avoid claiming an optimum unless the curve includes enough points around the peak.

| Situation | Preferred method | Reviewer-safe wording |
|---|---|---|
| Two independent groups | Welch t-test if variance may differ; Student t-test only if assumptions are justified | `The modified group showed a higher mean value; statistical significance was assessed using ...` |
| More than two dosages or mixtures | One-way ANOVA plus Tukey HSD | `Differences among dosage groups were screened by ANOVA and separated by Tukey HSD.` |
| Two factors, such as dosage and curing time | Two-way ANOVA | `The effects of dosage, curing time, and their interaction were evaluated.` |
| Non-normal or very small samples | Mann-Whitney U; Kruskal-Wallis + Dunn post-hoc test with Bonferroni correction; or descriptive statistics with caution | `The trend is reported descriptively unless a valid non-parametric post-hoc comparison is reported.` |
| Before/after aging retention | Paired test if same specimens; independent test if different specimens | `Retention was calculated as aged/unaged performance and tested according to specimen pairing.` |
| Repeated temperature/frequency rheology | Repeated-measures model or separate curves with cautious interpretation | `Curve-level behavior is shown; pointwise comparisons should not be overinterpreted.` |
| Correlation between continuous variables | Pearson or Spearman | `The association was evaluated using [Pearson/Spearman] correlation; correlation is not treated as causation.` |
| Dosage-response curve | Linear, polynomial, segmented, or nonlinear regression only if data density supports it | `The fitted curve is used to describe the tested dosage range, not to predict untested formulations.` |

## Small-Sample Guidance

Civil materials experiments often use `n = 3`. Treat this as a minimum engineering replicate count, not strong statistical evidence.

- Prefer plotting all data points plus mean and SD when `n <= 5`.
- Minimum: `n = 3` independent specimens per group for common materials testing.
- Recommended: `n = 5` when adhesion, pull-off, fracture, or heterogeneous specimens create high scatter.
- If the coefficient of variation is expected to exceed 15-20%, increase replicate count or avoid strong significance claims.
- Avoid overfitting regression models to fewer than 5 dosage levels.
- Report effect size or percentage change, but mark it as descriptive if no valid test is possible.
- If variability is high, discuss mixture heterogeneity, specimen preparation, curing condition, and instrument error before claiming a mechanism.

## Assumption and Outlier Checks

- Normality: use Shapiro-Wilk for small datasets, but do not overinterpret it when `n = 3`.
- Variance: use Levene or Brown-Forsythe before assuming equal variance.
- Outliers: apply a pre-defined rule such as instrument failure, visible specimen defect, 3 SD screening, or Grubbs test. Do not remove outliers only because they weaken the conclusion.
- Report exclusions transparently: `One specimen was excluded because the dolly detached from the adhesive layer before loading, which invalidated the pull-off measurement.`

## Writing Templates

Short method statement:

```text
The results are expressed as mean +/- SD (n = 3). Differences between groups
were considered statistically significant at p < 0.05.
```

ANOVA plus post-hoc statement:

```text
One-way ANOVA indicated that epoxy content significantly affected pull-off
strength (F(4, 10) = 23.5, p < 0.01). Tukey HSD tests showed that the 15%
epoxy group differed from the control (p < 0.01) and from the 20% group
(p < 0.05), supporting a dosage-dependent optimum within the tested range.
```

Non-significant result statement:

```text
Although the 15% epoxy group showed a higher mean value than the 10% group,
the difference was not statistically significant (p = 0.12). The result is
therefore discussed as a descriptive trend rather than definitive evidence
for an optimum dosage.
```

Correlation statement:

```text
The relationship between viscosity and pull-off strength was evaluated using
Spearman correlation because the dosage-response trend was monotonic but not
strictly linear. The correlation is used to describe association, not causality.
```

Post-hoc Dunn statement:

```text
Kruskal-Wallis + Dunn analysis indicated a statistically significant
difference in [property] across [X] groups (H([df]) = [value], p < 0.05).
Post-hoc Dunn tests with Bonferroni correction revealed that the [A]% group
differed significantly from the [B]% group (p < 0.01) and the [C]% group
(p < 0.05).
```

## Waterborne Epoxy Emulsified Asphalt Notes

- Bond strength: report pull-off or shear test standard, curing time, test temperature, substrate condition, and failure mode.
- Storage stability: report storage temperature, duration, settlement/separation index, and whether the epoxy system changes demulsification behavior.
- Viscosity/rheology: report shear rate, temperature, spindle/geometry, equilibration time, and whether the emulsion is still stable during testing.
- Moisture/aging: separate immediate bonding performance from retained performance after water immersion, freeze-thaw, UV, or thermal aging.

## Reviewer Risk Checks

- If a paragraph says `optimal dosage`, verify that the dosage range is dense enough and the criterion is defined.
- If a paragraph says `mechanism`, verify that statistics alone are not being used as mechanism evidence.
- If a figure uses error bars, define SD/SE/CI in the caption.
- If only one batch was tested, avoid generalizing to all emulsified asphalt systems.
