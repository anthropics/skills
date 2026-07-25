# Statistical Interpretation Guide

Full protocol for validate mode's statistical interpretation and fallacy scan.

## Part 1: Statistical Interpretation

### Step 1: Detect Statistical Content

Scan user-provided output for these patterns:
- p-values: `p = 0.023`, `p < .001`, `p > .05`
- Confidence intervals: `95% CI [0.12, 0.45]`, `CI: 0.12-0.45`
- Effect sizes: `d = 0.47`, `eta-squared = .036`, `r = .31`, `OR = 2.4`
- Test statistics: `t(98) = 2.34`, `F(2, 97) = 1.82`, `chi2(4) = 12.3`
- Coefficients: `beta = 0.23`, `B = 1.45`, `SE = 0.12`

If structured format (CSV/JSON): auto-extract column names matching these patterns.
If unstructured: ask user to highlight key numbers.

### Step 2: Interpret Each Finding

For each statistical result, assess:

**Significance:**
- Report exact p-value (not just "significant" or "not significant")
- Flag if p is borderline (.04-.05): "marginal significance — interpret with caution"
- Flag if many tests run without correction: "N tests without multiple comparison correction"

**Effect Size:**

| Measure | Small | Medium | Large |
|---------|-------|--------|-------|
| Cohen's d | 0.2 | 0.5 | 0.8 |
| eta-squared | .01 | .06 | .14 |
| r (correlation) | .10 | .30 | .50 |
| Odds Ratio | 1.5 | 2.5 | 4.3 |

- Always report: "statistically significant with [small/medium/large] effect"
- Warn if significant but small effect: "statistically significant but practically small — consider whether this difference matters in context"

**Confidence Interval:**
- Does CI include 0 (or 1 for OR)? → result is not significant regardless of p-value
- Width: narrow CI = precise estimate; wide CI = uncertain estimate
- Asymmetric CI around point estimate → possible skewness

**Assumption Checks:**

| Test | Assumption | Red Flag |
|------|-----------|----------|
| t-test | Normality | n < 30 per group and no normality test reported |
| t-test | Equal variance | No Levene's test and group sizes differ > 2:1 |
| ANOVA | Normality + homogeneity | Same as t-test; additionally check sphericity for RM |
| Chi-squared | Expected frequencies >= 5 | Any cell < 5 → for 2x2 tables use Fisher's exact; for larger tables use an exact/Monte Carlo approach or collapse categories with justification |
| Regression | Linearity, normality of residuals, homoscedasticity | No diagnostic plots reported |
| Correlation | Both variables continuous, linearity | Pearson used on ordinal data |

**Multiple Comparisons:**
- Count total number of statistical tests in the analysis
- If > 3 tests and no correction reported:
  - Suggest Bonferroni (conservative): adjusted alpha = .05 / N
  - Suggest Benjamini-Hochberg FDR (less conservative): for exploratory analyses
  - Report: which results survive correction, which don't

### Step 3: Assign Confidence Level

| Level | Criteria |
|-------|---------|
| `SOLID` | Significant with medium+ effect size, assumptions met, no fallacies detected |
| `CAUTION` | One or more: borderline p, small effect, unchecked assumptions, uncorrected comparisons |
| `RED_FLAG` | Multiple issues: non-significant reframed as trend, violated assumptions, detected fallacy |

---

## Part 2: Fallacy Scan (11 Types)

Check ALL 11 types for every validation. Report coverage in output ("11/11 checked").

### Structural Fallacies (Data Level)

**1. Simpson's Paradox**
- **What**: Overall trend reverses when data is split by a grouping variable
- **Detection**: If analysis has grouping variables (gender, department, site), compare aggregated result direction vs per-group direction
- **When to suspect**: Aggregate shows negative relationship but subgroups are all positive (or vice versa)
- **Severity if found**: RED_FLAG
- **Reporting note**: describe what numbers say (overall vs per-group), do NOT recommend which to report — that is an editorial decision for the reviewer

**2. Ecological Fallacy**
- **What**: Inferring individual-level relationships from group-level data
- **Detection**: Unit of analysis (e.g., schools, countries) differs from unit of inference (e.g., students, citizens)
- **When to suspect**: Regression on aggregated data used to make claims about individuals
- **Severity if found**: RED_FLAG

**3. Berkson's Paradox**
- **What**: Selection/sampling bias creates spurious negative correlation
- **Detection**: Sample drawn from a filtered population (only hospitalized patients, only admitted students, only published papers)
- **When to suspect**: Two seemingly unrelated variables show unexpected negative correlation in a selected sample
- **Severity if found**: CAUTION

**4. Collider Bias**
- **What**: Controlling for a variable that is a common effect of both IV and DV creates spurious association
- **Detection**: Check if any control variable could be caused by both IV and DV
- **When to suspect**: Adding a control variable changes the sign or significance of the main effect
- **Severity if found**: CAUTION

### Inferential Fallacies (Interpretation Level)

**5. Base Rate Neglect**
- **What**: Reporting sensitivity/specificity without considering prevalence
- **Detection**: Results present conditional probabilities (PPV, NPV, sensitivity, specificity) without base rate
- **When to suspect**: Screening or diagnostic accuracy studies
- **Severity if found**: CAUTION

**6. Regression to the Mean**
- **What**: Extreme values naturally move toward the mean on re-measurement
- **Detection**: Pre-post design where groups were selected based on extreme scores (lowest performers, highest risk)
- **When to suspect**: "Improvement" in the worst-performing group without a control group
- **Severity if found**: RED_FLAG if no control group; CAUTION if control group exists but not compared

**7. Survivorship Bias**
- **What**: Analyzing only "survivors" (those who completed, stayed, succeeded)
- **Detection**: Dropout/attrition rate > 15%; no intention-to-treat analysis; no dropout comparison
- **When to suspect**: Longitudinal studies, intervention studies, cohort studies
- **Severity if found**: CAUTION if dropout documented; RED_FLAG if dropout not reported

**8. Look-Elsewhere Effect**
- **What**: Testing many variables and reporting only the significant ones
- **Detection**: Ratio of (reported significant results) to (total tests run) is suspiciously high
- **When to suspect**: Exploratory analysis with many DVs; "we also found..." language
- **Severity if found**: CAUTION

**9. Garden of Forking Paths**
- **What**: Many researcher degrees of freedom (outlier removal criteria, variable transformations, model specifications) but only one path reported
- **Detection**: No pre-registration; analysis described only in final form; no robustness checks
- **When to suspect**: Complex analyses with many decision points
- **Severity if found**: NOTE if exploratory; CAUTION if presented as confirmatory

### Causal Fallacies (Claim Level)

**10. Correlation != Causation**
- **What**: Observational study uses causal language
- **Detection**: Study design is cross-sectional, correlational, or observational, but language includes "caused", "led to", "resulted in", "improved", "reduced"
- **When to suspect**: Always check in non-experimental designs
- **Severity if found**: CAUTION
- **Reporting note**: flag the specific causal language and note that the study design does not support causal inference. Example associational alternatives exist ("was associated with", "correlated with") but choosing phrasing is an editorial decision for the reviewer.

**11. Reverse Causality**
- **What**: The assumed direction of causation may be backwards
- **Detection**: Cross-sectional data with directional claims; no temporal precedence established
- **When to suspect**: "X predicts Y" in cross-sectional design (maybe Y causes X)
- **Severity if found**: CAUTION

---

## Relationship to ARS Logical Fallacies Catalog

ARS `deep-research/references/logical_fallacies.md` contains a broader 32-type catalog covering formal, informal, and rhetorical fallacies. This guide's 11-type list focuses specifically on **statistical and methodological** fallacies relevant to experiment validation. 7 types overlap (Simpson's Paradox, Ecological Fallacy, Survivorship Bias, Base Rate Neglect, Regression to Mean, Correlation != Causation, Reverse Causality). When both skills are loaded, this guide takes precedence for experiment result validation; ARS's catalog applies to broader argument evaluation in paper review.

**Severity mapping to ARS terminology**: experiment-agent's `RED_FLAG` corresponds to issues ARS would classify as requiring mandatory revision. `CAUTION` corresponds to issues ARS would flag for author attention. `NOTE` corresponds to optional commentary.

---

## Output Template

See `templates/output_formats.md` "Validation Report" section for the Markdown template.
