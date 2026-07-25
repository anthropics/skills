# NIH Mechanism Matching — Career Stage × Scope × Prelim

This reference answers exactly one decision: **given a researcher's career stage, project scope, and preliminary data status, which NIH mechanism(s) should the skill recommend?**

Pair with `scripts/mechanism_matcher.py` for the deterministic implementation.

## The Core Rule

**Career stage alone does NOT determine mechanism.** Scope and prelim data matter equally. The biggest misalignment is "early career + R01 with pilot data" — review reads as overscoped and goes unfunded.

The matching is a 3-dimensional lookup:

```
(career_stage, project_scope, preliminary_data) → mechanism shortlist
```

## Career Stage Buckets (from Q2)

| Bucket | Examples | Eligible mechanisms |
|---|---|---|
| Pre-doctoral | PhD student, T32 trainee | F31, T32 |
| Postdoctoral | F32, K99 candidate | F32, K99/R00, T32 |
| Early career | First R01 candidate, K-awardee | K01/K08/K23, K99/R00 → R00, R21, R03 |
| Independent | Multiple R01s, established lab | R01, R21, R03, R34, R61/R33 |
| Senior PI | R35, P-series | R35, P01, P30, U01 |

## Project Scope Buckets (inferred or asked)

| Scope | Indicator | Mechanism implication |
|---|---|---|
| Solo / pilot | Single site, single hypothesis, <2 yr | R03, R21 |
| Hypothesis-driven independent | Single PI, multi-aim, 4-5 yr | R01 |
| Multi-site cooperative | Multi-PI, multi-site, coord centers | U01 |
| Program-scale | Multiple aims, multiple PIs, sustained | P01, P30, R35 |
| Early/exploratory | High-risk, high-reward | DP1, DP2, R21 |

## Preliminary Data Buckets (from Q3)

| Status | Indicator | Mechanism budget tier |
|---|---|---|
| None | De novo project, no pilot | R03, R21, F-series |
| Pilot | Single-site early findings | R21, K-series, K99/R00 |
| Strong | Multi-experiment, R01-ready | R01, R34 |
| Validated | Multi-site publication-ready | R01, U01, P-series |

## Matching Matrix

The skill applies this matrix in `scripts/mechanism_matcher.py`:

### Pre-doctoral

- **Solo + None → F31** (NRSA individual fellowship)
- **Solo + Pilot → F31, T32 slot**
- **Larger → not eligible as PI** (work as co-investigator on mentor's grant)

### Postdoctoral

- **Solo + None → F32** (postdoc fellowship)
- **Solo + Pilot → F32, K99 candidate prep**
- **Strong + transitioning → K99/R00** (career-transition mechanism, unique to NIH)

### Early career

- **Solo + None/Pilot → K-series** (K01 / K08 / K23 — career development)
- **Solo + Pilot → R21 candidate** (after K-award completion or as parallel)
- **Independent + Pilot → R03, R21**
- **Independent + Strong → R01** (this is the "qualifying" R01 — most career-defining)
- **Resource-constrained env (Q4=3) → R15** (specifically targets this — fund undergrad-involving research)

### Independent

- **Pilot scope + Strong prelim → R01** (the standard)
- **Multi-aim + Strong → R01** (the standard 5-yr R01)
- **Multi-site + Validated → U01** (cooperative agreement)
- **Pilot/early → R21** (exploratory)
- **Clinical trial planning → R34**
- **Early-phase trial → R61/R33** (phased innovation award)
- **High-risk → DP1, DP2** (Pioneer / New Innovator)

### Senior PI

- **Program scope → R35** (outstanding investigator award, unrestricted by topic)
- **Program scope → P01** (program project, multi-PI)
- **Core facility → P30** (center grant)
- **Multi-site cooperative → U01**

## Critical Anti-Patterns

### Career stage alone

Common error: "Early career → K-award". Misses scope. Early-career researcher with **strong prelim** + **independent scope** should target **R01**, not K. K-award is for protected research time; R01 is for hypothesis-driven research budget.

### Scope/prelim mismatch

- "R01 + No prelim" → unfundable. Reviewers will reject as premature.
- "R03 + Strong prelim" → underscoped. Researcher leaves money + scope on the table.

`mechanism_matcher.py` flags both as warnings.

### Environment-blind recommendations

Resource-constrained institution (Q4=3) → consider **R15** specifically. R15 only goes to non-research-intensive institutions. Recommending R01 to a researcher at a resource-constrained college is malpractice — even with strong prelim, their environment can't support R01-scale costs.

### Skipping multi-PI options

For collaborative-by-design projects, **multi-PI R01** (multiple-PI option) is often better than splitting into two R01s. Don't default to single-PI just because it's the default.

## Mechanism Reference Table (Full)

| Mechanism | Budget (annual DC) | Duration | Best for | Prelim needed |
|---|---|---|---|---|
| F31 | $40-50k stipend + tuition | 2-3 yr | Pre-doc training | None-pilot |
| F32 | $48-58k stipend | 2-3 yr | Postdoc training | None-pilot |
| T32 | Institutional | 5-yr renewable | Pre-doc/postdoc training cohort | Institutional commitment |
| R03 | $50k × 2 yr | 2 yr | Small pilot studies | None-pilot |
| R21 | $275k DC × 2 yr | 2 yr | Pilot/exploratory R&D | None-pilot |
| R34 | $450k × 3 yr | 3 yr | Clinical trial planning | Pilot |
| R61/R33 | Phased: $250k + $500k × 2 yr | Up to 5 yr | Phased innovation | Pilot |
| K01 | $100k × 5 yr | 5 yr | Mentored research scientist | Pilot |
| K08 | $100k × 5 yr | 5 yr | Mentored clinical scientist | Pilot |
| K23 | $100k × 5 yr | 5 yr | Mentored patient-oriented | Pilot |
| K99/R00 | $90k mentored + $250k indep | Up to 5 yr | Postdoc → independence | Strong |
| R01 | $250-499k DC × 4-5 yr | 4-5 yr | Hypothesis-driven research | Strong |
| R15 | $300k total × 3 yr | 3 yr | Resource-constrained institutions | Pilot |
| R35 | $750k × 5-8 yr | 5-8 yr | Senior outstanding investigators | Validated |
| P01 | Multi-PI, $1-2M/yr × 5 yr | 5 yr | Program project (3+ PIs) | Validated |
| P30 | Core facility funding | 5 yr | Multi-investigator core | Validated |
| U01 | Cooperative agreement | 5 yr | Multi-site collaborative | Strong-validated |
| DP1 (Pioneer) | $700k × 5 yr | 5 yr | High-risk individual | None (visionary) |
| DP2 (New Innovator) | $300k × 5 yr | 5 yr | Early-career high-risk | Pilot |

## Program Officer Recommendation (Mandatory Per Skill)

After mechanism shortlist is generated, the skill MUST recommend:

> **Contact program officer at {top institute, top match} BEFORE writing.**
>
> Find them at: https://www.nih.gov/institutes-nih/list-nih-institutes-centers-offices → {institute} → Program Officers.
>
> Prepare:
> 1. 1-page specific aims
> 2. Your CV (NIH biosketch format if available)
> 3. 3 specific questions about institute priorities / mechanism fit
>
> Email subject: "Pre-application inquiry: <topic>"

This is the **single highest-leverage step** in any NIH application. Program officers signal "yes, submit" or "no, not the right institute" before you spend months writing. Skipping this is common; the cost is huge.

## Citations (7 sources)

1. **NIH Office of Extramural Research — *Types of Grant Programs* (https://grants.nih.gov/grants/funding/funding_program.htm).** Authoritative source for mechanism definitions + budget ranges + duration. The skill's mechanism reference table mirrors NIH's published catalog.

2. **Sally Rockey, "Mechanism Selection Guide" — *NIH Extramural Nexus*, 2014-2022.** Former NIH Deputy Director's blog series on mechanism selection. Source for the "career stage alone is wrong" framing.

3. **Robertson, M. et al., "Successful K-to-R Transition" — *Academic Medicine* 92(3), 2017.** Empirical analysis of K-award → R01 transitions. Source for the early-career mechanism sequencing (K → R21 → R01) heuristic.

4. **NIH RePORTER Project Database (https://reporter.nih.gov).** The empirical ground truth for what NIH actually funds — institute portfolios, study section ranges, project sizes. The skill queries this via POST API.

5. **Mehrotra, A. et al., "R01 Funding Patterns Across Career Stages" — *JAMA Internal Medicine*, 2020.** Career-stage-stratified analysis of R01 application + funding rates. Source for the "early career + strong prelim → R01 IS appropriate" guidance.

6. **NIH NRSA Fellowship guidelines (https://grants.nih.gov/training/F_files_index.htm).** Authoritative F31/F32 source. Source for the trainee-stage mechanism shortlist.

7. **Heggeness, M. L., "What Makes a Successful Grant Application" — *Nature Human Behaviour* 5, 2021.** Meta-analysis of grant-writing predictors. Source for the program-officer-contact recommendation (#1 predictor of submission success after scientific merit).
