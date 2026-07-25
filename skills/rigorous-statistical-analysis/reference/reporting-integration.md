# Reporting & integration — turning results into report-ready findings

**Load when:** statistical results are being prepared for a written report. This file gives the
result-tuple formats, the significance-verdict thresholds, and the exact mapping into an
**adaptive-research-reporting-dvs** Mode A report.

---

## 1. Result-tuple formats (use verbatim)

| Analysis | Report as |
|---|---|
| Mean comparison (2 groups) | `t(38) = 2.61, p = 0.013, d = 0.83, 95% CI [0.19, 1.46]` |
| ANOVA | `F(2, 87) = 22.94, p < 0.0001, ω² = 0.33` + Tukey pairs |
| Correlation | `r = +0.924, p = 0.025, 95% CI [0.31, 0.99], R² = 0.854` |
| Regression coefficient | `β = 3.21, SE = 0.74, t = 4.34, p < 0.001, 95% CI [1.75, 4.67]` |
| Regression model | `R² = 0.998, adj-R² = 0.996, F(3, 46) = 812, p < 0.0001, n = 50` |
| Logistic | `OR = 2.4, 95% CI [1.3, 4.5], p = 0.006` |
| Non-parametric | `U = 512, p = 0.008, rank-biserial r = 0.41` |
| Inequality | `Gini = 0.42, 95% CI [0.35, 0.49]` |
| Diversity | `H = 1.567 (evenness 0.680, S = 10)` |
| Trend | `β = +142.3 unit/tahun, p = 0.004`; `Mann-Kendall τ = 0.78, p = 0.002`; `CAGR = 6.4%` |

Rules: exact p (or `p < 0.001` below that), explicit sign on every coefficient and delta, effect size
**always** beside the p-value, 95% CI wherever a formula or bootstrap allows it, and full source
precision retained in the underlying tables.

## 2. Significance verdict — the reporting convention

State α once in the methodology section, then apply consistently:

| p-value | English verdict | BM verdict (for a DVS report) |
|---|---|---|
| `p < 0.05` | significant | **Signifikan** |
| `0.05 ≤ p < 0.10` | a tendency / marginal | **Kecenderungan** |
| `p ≥ 0.10` | not significant | **Tidak signifikan** |

A "Tidak signifikan" result on an adequately powered test is a finding — report it plainly. A
non-significant result on an under-powered test is uninformative — say so in the limitation, do not
present it as evidence of no effect. `toolkit.verdict(p)` returns the BM verdict.

## 3. Effect-size reference (so "does it matter?" is answered)

| Measure | Small | Medium | Large |
|---|---|---|---|
| Cohen's d / Hedges' g | 0.20 | 0.50 | 0.80 |
| Pearson r (and √R²) | 0.10 | 0.30 | 0.50 |
| η² / ω² (ANOVA) | 0.01 | 0.06 | 0.14 |
| Cramér's V (df=1) | 0.10 | 0.30 | 0.50 |
| Odds ratio | ~1.5 | ~2.5 | ~4.0 |

Report the size and then say, in words, whether it is material to the decision at hand.

## 4. Mapping into an adaptive-research-reporting-dvs Mode A report

The two skills are designed to interlock. The statistics you produce here drop into the report's
numbered skeleton like this:

| Report section (Mode A) | What this skill supplies |
|---|---|
| `Ringkasan Eksekutif` | the headline effect with its magnitude, effect size, and verdict — the counterintuitive finding stated first |
| `1 Data dan Metodologi` | n, unit of observation, the tests deployed **named**, and α; declare definitional boundaries of the data |
| `2 Trend Parameter Utama` | slopes, indexed trends, CAGR, CV across the series |
| `4 Analisis Statistik Inferensi` *(rigor TINGGI only)* | the t/ANOVA/correlation tuples, each answering a named objection |
| `5 Analisis Mengikut [unit ruang]` | disaggregated comparisons; Gini/Shannon across the spatial units |
| `6 Analisis Regresi / Dekomposisi` *(TINGGI only)* | the fixed-effects model that holds the spatial unit constant + diagnostics (robust SE, VIF, Breusch-Pagan) |
| `7 Limitasi Dapatan` | every assumption check and power caveat recorded here, without defensiveness |
| `8 Kesimpulan` | restate the **implication**, not the statistics |
| `Nota` | any reconciliation of conflicting figures and the basis adopted |

**The rigor dial is shared.** Only populate sections 4 and 6 when the finding is contested (it
contradicts a standing position, cuts resources, or is counterintuitive). Against an uncontested
finding, descriptive statistics in sections 2–3 are the correct and complete analysis — deploying
regression there is a defect under both skills' anti-decoration rule.

## 5. The honesty rules that both skills enforce

- **Never a bare mean, never a bare p.** Magnitude + uncertainty, or it is not reported.
- **Never causal from bivariate.** The controlled estimate is the claim; the correlation is a prompt
  to run it.
- **Never inferential machinery on an uncontested point.** Strip it.
- **Never a hedge as an ending.** A gap in evidence becomes a *commissioned study* (question, method,
  data source, owner, deadline), not "further investigation is needed."
- **Recompute everything.** A supplied statistic is verified, never quoted.
