# Statistical Reporting Standards — Statistical Reporting Standards & APA 7.0 Format Quick Reference

This document defines the complete review standards for statistical reporting in quantitative research. `methodology_reviewer_agent` uses this document as the primary reference in Step 4a (Statistical Reporting Adequacy).

---

## 1. Universal Statistical Reporting Checklist

All quantitative research papers **must** report the following items. Check each item during review:

### 1.1 Descriptive Statistics

| Item | Standard | Common Omission |
|------|----------|----------------|
| Mean (*M*) | Must be reported for all continuous variables | Only overall reported, not by group |
| Standard deviation (*SD*) | Must appear paired with the mean | Standard error (*SE*) used incorrectly in place of SD |
| Sample size (*N* / *n*) | Both total and group sample sizes must be reported | Sample attrition during analysis unexplained |
| Range | Report Min-Max or interquartile range | Completely absent, unable to judge distribution characteristics |
| Categorical variable distribution | Report frequency (*f*) and percentage (%) | Only percentage reported, missing raw frequency |

### 1.2 Effect Size

| Item | Standard | Common Omission |
|------|----------|----------------|
| Reporting obligation | **All statistical tests must be accompanied by effect sizes** — APA 7.0 mandatory requirement | Only *p*-value reported, no effect size |
| Select appropriate metric | Choose effect size metric corresponding to the analysis method (see Section 2) | Inappropriate effect size metric used |
| Interpretation | Must provide Cohen's conventional benchmarks or field-specific benchmarks | Numbers reported but magnitude not interpreted |

**Common Effect Size Metrics Quick Reference:**

| Analysis Method | Effect Size Metric | Small/Medium/Large (Cohen's Convention) |
|----------------|-------------------|----------------------------------------|
| *t*-test | Cohen's *d* | 0.2 / 0.5 / 0.8 |
| ANOVA | *eta*-squared | .01 / .06 / .14 |
| ANOVA (partial) | partial *eta*-squared | .01 / .06 / .14 |
| Correlation | *r* | .10 / .30 / .50 |
| Regression | *R*-squared, *f*-squared | *f*-squared: .02 / .15 / .35 |
| Chi-square | Cramer's *V*, *phi* | *V*: .10 / .30 / .50 (*df*=1) |
| Odds Ratio | OR | 1.5 / 2.5 / 4.3 (Rosenthal) |

### 1.3 Confidence Intervals

| Item | Standard | Common Omission |
|------|----------|----------------|
| CI reporting | All effect sizes and key estimates **should** report 95% CI | CI completely absent |
| Format | 95% CI [lower bound, upper bound] | Inconsistent format or using parentheses instead of brackets |
| Interpretation | Describe the substantive meaning of the CI, not just statistical meaning | Only checking whether CI includes zero, not interpreting width |

### 1.4 Statistical Significance

| Item | Standard | Common Omission |
|------|----------|----------------|
| *p*-value format | Report exact *p* value (e.g., *p* = .032) | Only reporting *p* < .05 or *p* > .05 |
| *p* < .001 | Can report *p* < .001 when *p* is very small | Reporting *p* = .000 (raw statistical software output) |
| Alpha level | Declare alpha level a priori | Failure to state whether alpha = .05 or another value |
| Multiple comparisons | Use Bonferroni, Holm, FDR correction | Multiple comparisons without any correction |
| Non-significant results | Must be fully reported; cannot be hidden | Selectively reporting only significant results |

### 1.5 Statistical Power

| Item | Standard | Common Omission |
|------|----------|----------------|
| A priori power analysis | State target power (typically >= .80), assumed effect size, alpha, required sample size | Power analysis completely absent |
| Effect size source | Based on prior research, pilot study, or theoretical expectation | Using Cohen's convention without explanation |
| Tool | Use G*Power, pwr package, etc. | Tool not specified |
| Post-hoc power | Report observed power for non-significant results | Type II error risk not discussed for non-significant results |
| Sensitivity analysis | Report the minimum detectable effect size given *N* | Sensitivity analysis not conducted |

### 1.6 Missing Data Handling

| Item | Standard | Common Omission |
|------|----------|----------------|
| Missing data reporting | Report missing data amount and proportion for each variable | Missing data situation not reported |
| Missing mechanism | Discuss MCAR / MAR / MNAR | MCAR assumed without testing |
| Handling method | State the method used: listwise deletion / pairwise deletion / MI / FIML | Not stated or only using listwise deletion |
| Sensitivity analysis | Compare result robustness across different missing data handling methods | Only one method used, sensitivity not tested |

### 1.7 Assumption Testing

| Assumption | Applicable Analysis | Testing Method | Common Omission |
|-----------|-------------------|---------------|----------------|
| Normality | *t*-test, ANOVA, regression | Shapiro-Wilk / K-S / Q-Q plot / skewness & kurtosis | Completely untested or only invoking CLT |
| Homogeneity of variance | Independent *t*-test, ANOVA | Levene's test | Not reported or alternative method not used when violated |
| Linearity | Regression, correlation | Residual plot / scatter plot | Linearity assumed without testing |
| Independence | Most parametric tests | Durbin-Watson / research design explanation | Nested data not handled |
| Multicollinearity | Multiple regression | VIF, tolerance, correlation matrix | VIF not reported or reported but not addressed |
| Residual normality / homoscedasticity | Regression | Residual plot, Breusch-Pagan | Residuals not checked after model fitting |

---

## 2. Method-Specific Checklists

### 2.1 *t*-test (Independent / Paired Samples)

| Check Item | Description |
|-----------|-------------|
| Report *t* statistic | *t*(df) = X.XX, *p* = .XXX |
| Independent vs paired | Correct selection? Paired designs need to report pairing logic |
| Effect size | Cohen's *d* (independent) or *d*_z (paired) |
| Assumption testing | Normality (important for small samples), homogeneity of variance (independent *t*-test) |
| Welch's *t*-test | Is Welch correction used when variances are unequal? |
| Directionality | Is one-tailed vs two-tailed supported by a priori theoretical basis? |

### 2.2 ANOVA (One-Way / Factorial / Repeated Measures)

| Check Item | Description |
|-----------|-------------|
| Report *F* statistic | *F*(df1, df2) = X.XX, *p* = .XXX |
| Effect size | *eta*-squared, partial *eta*-squared, or *omega*-squared |
| Post-hoc comparisons | When main effect is significant, are post-hoc tests done (Tukey / Bonferroni / Games-Howell)? |
| Interaction effects | In factorial designs, are interactions interpreted? Are simple effects tested? |
| Sphericity assumption | For repeated measures, is Mauchly's test reported + Greenhouse-Geisser / Huynh-Feldt correction? |
| Assumption testing | Normality, homogeneity of variance (Levene's), independence of between-group observations |
| Unequal group sizes | When group sizes differ substantially, is Type III SS used? |

### 2.3 Regression Analysis (Linear / Logistic)

#### Linear Regression

| Check Item | Description |
|-----------|-------------|
| Model summary | *R*-squared, adjusted *R*-squared, *F* test for model |
| Coefficient table | *B*, *SE*, *beta*, *t*, *p*, 95% CI for *B* |
| Multicollinearity | VIF (< 5 or < 10 depending on field convention), tolerance |
| Residual diagnostics | Normality, homoscedasticity, linearity, outliers (Cook's *D*) |
| Variable selection | Rationale for enter vs stepwise method |
| Effect size | *R*-squared, *f*-squared, Cohen's *f*-squared |

#### Logistic Regression

| Check Item | Description |
|-----------|-------------|
| Model fit | Hosmer-Lemeshow / chi-squared / -2LL / Nagelkerke *R*-squared |
| Coefficient reporting | *B*, *SE*, Wald, OR, 95% CI for OR |
| Classification accuracy | Classification table, sensitivity, specificity, AUC/ROC |
| Assumptions | Independence of observations, linearity in the logit (linear relationship between continuous predictors and logit) |
| Sample size | At least 10-20 events per predictor variable (EPV rule) |

### 2.4 Structural Equation Modeling (SEM)

| Check Item | Standard |
|-----------|----------|
| Sample size | Typically >= 200; or 5-10 times the number of estimated parameters |
| Model fit indices | **Must report multiple indices simultaneously** (at least 4) |
| CFI / TLI | >= .95 (good); >= .90 (acceptable) |
| RMSEA | <= .06 (good); <= .08 (acceptable); must report 90% CI |
| SRMR | <= .08 |
| chi-squared/df | <= 3 (some scholars suggest <= 2) |
| Factor loadings | Standardized >= .50 (ideal >= .70) |
| Measurement model | CFA before SEM (two-step approach) — Anderson & Gerbing (1988) |
| Reliability and validity | CR >= .70, AVE >= .50, discriminant validity (Fornell-Larcker / HTMT) |
| Modification indices | When using modification indices, must have theoretical support |
| Normality | Multivariate normality (Mardia's coefficient); when violated, use robust ML or bootstrapping |

### 2.5 Hierarchical Linear Modeling (HLM / MLM)

| Check Item | Standard |
|-----------|----------|
| Nested structure | Clearly explain each level (e.g., students -> classes -> schools) |
| ICC | Report Intraclass Correlation Coefficient; ICC > .05 supports using MLM |
| Random effects | Report random intercept and (if applicable) random slope variances |
| Fixed effects | Report coefficients, *SE*, *t* / *z*, *p*, CI |
| Between-group sample size | Level-2 unit count (typically recommended >= 30) |
| Centering | Explain whether grand-mean centering or group-mean centering is used and why |
| Model comparison | Use deviance (-2LL), AIC, BIC to compare nested models |
| Effect size | Pseudo *R*-squared (e.g., Snijders & Bosker's *R*-squared) |

### 2.6 Chi-Square Test

| Check Item | Description |
|-----------|-------------|
| Reporting format | chi-squared(df, *N* = XX) = X.XX, *p* = .XXX |
| Effect size | Cramer's *V* (larger than 2x2) or *phi* (2x2) |
| Expected frequencies | All cells expected frequency >= 5; if any cell < 5, use Fisher's exact test |
| Independence | Are observations truly independent? (Repeated measures are not suitable for ordinary chi-square) |
| Residual analysis | When significant, check standardized residuals to determine which cells contribute to significance |

### 2.7 Non-Parametric Tests

| Check Item | Description |
|-----------|-------------|
| Justification for use | Clearly explain why parametric tests are not used (e.g., normality violation, ordinal scale) |
| Method selection | Mann-Whitney *U* / Wilcoxon / Kruskal-Wallis / Friedman — is the correct test matched |
| Effect size | *r* = *Z* / sqrt(*N*) (Mann-Whitney); *W* (Kendall's) |
| Reporting format | Report test statistic, *p*-value, effect size |
| Post-hoc comparisons | After significant Kruskal-Wallis, pairwise comparisons + correction needed |

---

## 3. APA 7th Edition Statistical Format Quick Reference

### 3.1 Number Formatting

| Rule | Correct | Incorrect |
|------|---------|-----------|
| *p*-value no leading zero | *p* = .032 | *p* = 0.032 |
| Statistics that can exceed 1.0 have leading zero | *M* = 0.75 | *M* = .75 |
| Statistics that cannot exceed 1.0 have no leading zero | *r* = .45 | *r* = 0.45 |
| Generally 2 decimal places | *M* = 3.45 | *M* = 3.4 |
| *p*-value 2-3 decimal places | *p* = .03 or *p* = .032 | *p* = .0321 |
| Percentages 0-1 decimal places | 45.2% | 45.2381% |

**Statistics that cannot exceed 1.0** (no leading zero): correlation coefficients (*r*, *R*), proportions (*p*-value), Cramer's *V*, *phi*, *eta*-squared, *R*-squared, *beta* (standardized regression coefficient)

**Statistics that can exceed 1.0** (leading zero): *M*, *SD*, *B* (unstandardized regression coefficient), Cohen's *d*, *t*, *F*, chi-squared

### 3.2 Statistical Symbol Italicization Rules

| Italic | Non-italic |
|--------|-----------|
| *M*, *SD*, *SE* | df |
| *N* (total sample), *n* (subsample) | SS, MS |
| *t*, *F*, *p*, *r*, *R*, *z* | OR, CI, VIF |
| *d*, *f*-squared, *eta*-squared, *omega*-squared | AIC, BIC, CFI, TLI |
| *B*, *beta* | RMSEA, SRMR |
| *chi*-squared | ICC |
| *U*, *W* (non-parametric statistics) | ANOVA, SEM, HLM |

### 3.3 Statistical Results Reporting Format Examples

| Analysis Method | APA Format Example |
|----------------|-------------------|
| Independent samples *t*-test | *t*(58) = 2.45, *p* = .017, *d* = 0.63, 95% CI [0.12, 1.14] |
| Paired samples *t*-test | *t*(29) = -3.12, *p* = .004, *d*_z = 0.57 |
| One-way ANOVA | *F*(2, 87) = 4.56, *p* = .013, partial *eta*-squared = .09 |
| Linear regression | *B* = 0.34, *SE* = 0.12, *beta* = .28, *t*(95) = 2.83, *p* = .006, 95% CI [0.10, 0.58] |
| Logistic regression | *B* = 1.24, *SE* = 0.45, Wald = 7.59, *p* = .006, OR = 3.46, 95% CI [1.43, 8.37] |
| Chi-square | chi-squared(2, *N* = 150) = 8.34, *p* = .015, *V* = .24 |
| Mann-Whitney | *U* = 245.00, *z* = -2.31, *p* = .021, *r* = .29 |
| SEM fit | chi-squared(52) = 78.34, *p* = .011, CFI = .97, TLI = .96, RMSEA = .045 [.018, .068], SRMR = .038 |
| HLM fixed effects | *gamma*_10 = 0.45, *SE* = 0.15, *t*(28) = 3.00, *p* = .006 |

### 3.4 Table Format Standards

| Rule | Description |
|------|-------------|
| Three-line table | APA tables have only three horizontal lines (above header, below header, bottom of table), no vertical lines |
| Table numbering | Table 1, Table 2... (bold), title on the line below the number (italic) |
| Note levels | General note (Note.) -> Specific note (superscript a, b) -> Significance (*p* < .05, **p* < .01) |
| Asterisks | \**p* < .05. \*\**p* < .01. \*\*\**p* < .001. |
| Alignment | Numbers right-aligned, decimal points aligned |

---

## 4. Statistical Red Flags

The following patterns during review should raise red flags, requiring further investigation or author clarification:

### 4.1 P-hacking Indicators

| Red Flag | Description | Severity |
|----------|-------------|----------|
| Many *p* near .05 | Multiple results with *p* concentrated in the .04-.05 range | HIGH |
| Selective reporting | Only significant results reported, non-significant ones disappeared | HIGH |
| Vague analysis strategy | Analysis strategy not stated a priori, appears exploratory in hindsight | MEDIUM |
| Unexpected subgroups | Post-hoc subgroup decomposition to find significant results | MEDIUM |
| Flexible sample size | No pre-defined stopping rule (sequential testing without correction) | HIGH |
| "Excluding outliers" | Large number of outliers excluded with unclear criteria | MEDIUM |

### 4.2 HARKing (Hypothesizing After Results are Known)

| Red Flag | Description | Severity |
|----------|-------------|----------|
| Perfect hypothesis-result match | All hypotheses supported without exception | MEDIUM |
| Exploratory analysis packaged as confirmatory | Literature review clearly constructed post-hoc | HIGH |
| Hypothesis directionality change | Originally predicted positive but result was negative, yet claimed "as expected" | HIGH |
| No pre-registration | No OSF / AsPredicted pre-registration link provided (not mandatory but recommended) | LOW |

### 4.3 Missing Effect Sizes and Confidence Intervals

| Red Flag | Description | Severity |
|----------|-------------|----------|
| No effect sizes reported at all | Conclusions based solely on *p*-values | HIGH |
| CI completely absent | Cannot judge estimation precision | MEDIUM |
| Extremely wide CI | CI spans from small to large effect sizes, imprecise estimation | MEDIUM |
| Inconsistent effect sizes | Reported effect sizes inconsistent with calculations from raw data | HIGH |

### 4.4 Sample Size Issues

| Red Flag | Description | Severity |
|----------|-------------|----------|
| No power analysis | Sample size lacks a priori calculation basis | MEDIUM |
| Sample too small | In regression analysis, *N* < 10 x number of predictors | HIGH |
| Unexplained sample attrition | Large gap between starting *N* and final *N* without explanation | MEDIUM |
| SEM small sample | *N* < 200 without small sample correction | MEDIUM |
| HLM Level-2 insufficient | Level-2 units < 30 | MEDIUM |

### 4.5 Uncorrected Multiple Comparisons

| Red Flag | Description | Severity |
|----------|-------------|----------|
| Multiple *t*-tests instead of ANOVA | 3+ group comparisons using multiple *t*-tests | HIGH |
| No post-hoc after ANOVA | Main effect significant but claiming group differences without post-hoc tests | MEDIUM |
| Multiple DVs uncorrected | Multiple dependent variables tested separately on the same dataset without Bonferroni or FDR | MEDIUM |
| Multiple model comparisons | Trying multiple models but only reporting "the best one" | HIGH |

### 4.6 Assumption Violation

| Red Flag | Description | Severity |
|----------|-------------|----------|
| Assumption testing completely absent | Skipping normality/homogeneity/linearity tests | MEDIUM |
| Violations not addressed | Violations reported but original analysis still used | HIGH |
| CLT as excuse | "Because *N* > 30, normality can be ignored" without actual testing | LOW |
| Excessive VIF | VIF > 10 but no action taken | HIGH |

### 4.7 Other Red Flags

| Red Flag | Description | Severity |
|----------|-------------|----------|
| *p* = .000 | Raw statistical software output, should be *p* < .001 | LOW |
| df inconsistent with *N* | *N* derived from degrees of freedom doesn't match reported *N* | HIGH |
| Inconsistent table numbers | Text narrative contradicts table values | HIGH |
| Statistical software not stated | Not reporting SPSS / R / Stata / Mplus and version | LOW |
| Causal language | Non-experimental designs (correlational/survey) using causal inference language | MEDIUM |

---

## 5. Common Statistical Methods in Higher Education Research

Higher education research papers frequently involve the following topics and corresponding analysis methods. This table can be referenced during review to judge whether method selection is appropriate.

### 5.1 Recommended Methods by Research Question Type

| Research Question Type | Recommended Method | Description |
|-----------------------|-------------------|-------------|
| Two-group comparison (e.g., experimental vs control) | Independent samples *t*-test / Mann-Whitney | Depending on data normality |
| Multi-group comparison (e.g., different institution types) | ANOVA / Kruskal-Wallis | Mean comparison for 3+ groups |
| Pre-post comparison | Paired *t*-test / Wilcoxon | Change within the same group |
| Predictive analysis (continuous DV) | Multiple regression | Multiple predictors' effects on continuous outcome |
| Predictive analysis (binary DV) | Logistic regression | E.g., graduation/dropout, pass/fail |
| Nested data (students -> schools) | HLM / MLM | Higher education data naturally has nested structure |
| Latent constructs and path analysis | SEM / CFA | Measuring unobservable constructs (e.g., teaching quality) |
| Scale reliability and validity | EFA -> CFA | Scale development or validation |
| Categorical variable association | Chi-square / Fisher's exact | Cross-tabulation analysis |
| Longitudinal data | Growth curve models / Latent growth models | Tracking student trajectories over multiple years |
| Large-scale datasets | Weighted analysis / sampling design correction | Accounting for sampling design when using national survey data |

### 5.2 Special Considerations for Higher Education Research

| Consideration | Description |
|--------------|-------------|
| **Nested structure** | Higher education data almost always has nesting (students -> departments -> institutions); ignoring it underestimates standard errors and inflates Type I error |
| **Sampling design** | When using national databases (e.g., MOE statistics, public higher education data), must account for sampling weights and clustering |
| **Selection bias** | Students self-select into departments/institutions, not randomly assigned; consider propensity score matching or Heckman correction |
| **Ceiling effects** | Satisfaction surveys often show extreme skewness; need to check and consider Tobit model or non-parametric methods |
| **Small population** | Taiwan has a limited number of universities (~150); census surveys are not appropriate for inferential statistics (census, not sample) |
| **Time series** | Analyzing multi-year enrollment trends requires considering autocorrelation |
| **Multiple roles** | Same faculty completing multiple surveys (e.g., teaching evaluations) -> observations not independent |

---

## 6. Statistical Reporting Completeness Scoring Standards

`methodology_reviewer_agent` uses the following standards to assess statistical reporting completeness:

### Scoring Dimensions and Weights

| Dimension | Weight | Full Score Criteria |
|-----------|--------|-------------------|
| A. Descriptive statistics completeness | 15% | M, SD, N, Range all present |
| B. Effect size reporting | 20% | All tests accompanied by effect sizes |
| C. Confidence interval reporting | 15% | Key estimates include CI |
| D. Assumption testing reporting | 15% | All statistical assumptions tested |
| E. Statistical power | 10% | Complete a priori power analysis |
| F. Missing data handling | 10% | Missing data amounts + handling method reported |
| G. APA format correctness | 10% | Symbols, decimals, tables compliant |
| H. No red flag indicators | 5% | No red flags from Section 4 detected |

### Scoring Levels

| Level | Score | Description |
|-------|-------|-------------|
| Exemplary | 90-100 | Statistical reporting is exemplary, all items complete and correctly formatted |
| Adequate | 70-89 | Major items complete, minor omissions that don't affect conclusion credibility |
| Needs Improvement | 50-69 | Significant omissions (e.g., missing effect sizes or assumption testing), supplementation needed |
| Inadequate | 30-49 | Multiple items missing, statistical reporting insufficient to support conclusions |
| Unacceptable | 0-29 | Severely insufficient statistical reporting, major rewrite needed |

---

## 7. Quick Reference: Recommended Review Sequence

Methodology reviewer should follow this sequence when reviewing statistical reporting:

```
Step 1: Confirm research question -> analysis method correspondence is reasonable (Section 5)
Step 2: Check whether assumption testing is reported (Section 1.7)
Step 3: Check universal checklist item by item (Sections 1.1-1.6)
Step 4: Consult method-specific checklist (Section 2)
Step 5: Scan red flag list (Section 4)
Step 6: Verify APA formatting (Section 3)
Step 7: Produce completeness score (Section 6)
```
