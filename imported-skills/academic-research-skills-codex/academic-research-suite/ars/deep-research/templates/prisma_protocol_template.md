# PRISMA-P 2015 — Systematic Review Protocol Template

## Purpose

Template for writing a systematic review protocol following PRISMA-P 2015 (Preferred Reporting Items for Systematic Review and Meta-Analysis Protocols). Complete this template before starting the literature search and register it on PROSPERO or OSF.

**Reference**: Shamseer et al. (2015). BMJ, 349, g7647. https://doi.org/10.1136/bmj.g7647

---

## ADMINISTRATIVE INFORMATION

### Title

**[Provide a descriptive title that identifies the report as a protocol for a systematic review. Include "systematic review" and "meta-analysis" if applicable.]**

Registration: [PROSPERO / OSF ID, or "To be registered"]

### Authors

| # | Name | Affiliation | Role | Contact |
|---|------|-------------|------|---------|
| 1 | [Name] | [Institution] | Guarantor / Lead | [email] |
| 2 | [Name] | [Institution] | Co-reviewer | [email] |

### Amendments

| Date | Section Changed | Description of Change | Rationale |
|------|----------------|----------------------|-----------|
| [date] | [section] | [change] | [why] |

### Support

**Sources**: [Funding source(s) or "No external funding"]
**Role of funder**: [Describe any role of funders in the review, or "None"]

---

## INTRODUCTION

### Rationale

**[Describe the rationale for the review in the context of what is already known. Explain why this review is needed.]**

Key points to address:
- What is the health/education/social problem?
- What is the current state of the evidence?
- Why is a systematic review needed now? (e.g., existing reviews are outdated, conflicting evidence, no previous review exists)

### Objectives

**[Provide an explicit statement of the question(s) the review will address. Use the PICOS framework.]**

- **P** (Population): [Define the target population]
- **I** (Intervention/Exposure): [Define the intervention or exposure of interest]
- **C** (Comparator): [Define the comparison group]
- **O** (Outcomes): [Define primary and secondary outcomes]
- **S** (Study design): [Specify eligible study designs]

Research Question: [State the review question in a single sentence]

---

## METHODS

### Eligibility Criteria

#### Study Characteristics

| Criterion | Include | Exclude |
|-----------|---------|---------|
| **Study design** | [e.g., RCTs, quasi-experimental, cohort] | [e.g., case reports, editorials, commentaries] |
| **Publication date** | [e.g., 2010-present] | [Before cutoff, with justification] |
| **Language** | [e.g., English and Chinese] | [Other languages, with justification] |
| **Publication status** | [e.g., published and preprints] | [e.g., conference abstracts only] |
| **Setting** | [e.g., higher education institutions] | [e.g., K-12, non-formal education] |

#### Participants

[Describe the target population in detail. Include age, gender, condition, or other relevant characteristics.]

#### Interventions/Exposures

[Describe the intervention(s) or exposure(s) of interest. Include dosage, frequency, duration if applicable.]

#### Comparators

[Describe the comparator(s). This may include no intervention, usual care, placebo, or alternative interventions.]

#### Outcomes

**Primary outcome(s)**:
1. [Outcome 1] — measured by [instrument/method], at [time point(s)]
2. [Outcome 2] — measured by [instrument/method], at [time point(s)]

**Secondary outcome(s)**:
1. [Outcome 3] — measured by [instrument/method], at [time point(s)]
2. [Outcome 4] — measured by [instrument/method], at [time point(s)]

#### Timing

[Specify any minimum follow-up duration or time constraints]

### Information Sources

| Database/Source | URL | Coverage | Justification |
|----------------|-----|----------|---------------|
| [e.g., PubMed/MEDLINE] | pubmed.ncbi.nlm.nih.gov | Biomedical | Core database for health research |
| [e.g., Web of Science] | webofscience.com | Multidisciplinary | Citation indexing, broad coverage |
| [e.g., Scopus] | scopus.com | Multidisciplinary | Large abstract database |
| [e.g., ERIC] | eric.ed.gov | Education | Core database for education research |
| [e.g., PsycINFO] | apa.org/pubs/databases/psycinfo | Psychology | Behavioral science coverage |
| [Grey literature] | [specify sources] | — | Reduce publication bias |
| [Trial registries] | clinicaltrials.gov, WHO ICTRP | — | Identify unpublished studies |

Additional sources:
- Reference lists of included studies (backward citation)
- Citation tracking of key studies (forward citation)
- Contact with experts in the field (if applicable)

### Search Strategy

**[Present the draft search strategy for at least one database. The strategy should be peer-reviewed using the PRESS checklist.]**

Example structure for [primary database]:
```
Search Block 1 (Population):
  "higher education" OR "university" OR "college" OR "postsecondary"

Search Block 2 (Intervention/Exposure):
  "quality assurance" OR "accreditation" OR "program review"

Search Block 3 (Outcome):
  "student outcomes" OR "learning outcomes" OR "graduation rate"

Combined: Block 1 AND Block 2 AND Block 3
Filters: [date range], [language], [document type]
```

### Study Records

#### Data Management

[Describe the software/tools to be used for managing records. E.g., Covidence, Rayyan, Excel, Zotero]

#### Selection Process

1. **Deduplication**: [Method for removing duplicates, e.g., automatic in Covidence + manual check]
2. **Title/Abstract screening**: [Number of reviewers, independence, process for resolving disagreements]
3. **Full-text screening**: [Number of reviewers, independence, process for resolving disagreements]
4. **Documentation**: [How excluded studies and reasons will be recorded]

Pilot: [Describe pilot testing of screening criteria, e.g., "Two reviewers will independently screen 50 records to calibrate criteria before full screening"]

#### Data Collection Process

1. **Data extraction form**: [Describe or attach the form. Pilot test with 3-5 studies]
2. **Extractors**: [Number, independence, process for resolving discrepancies]
3. **Missing data**: [How missing or unclear data will be handled, e.g., contact authors]

### Data Items

| Category | Variables to Extract |
|----------|---------------------|
| **Study metadata** | Authors, year, country, journal, study design |
| **Participants** | Sample size, demographics, setting, inclusion criteria |
| **Intervention/Exposure** | Description, duration, frequency, comparison group |
| **Outcomes** | Primary and secondary outcomes, measurement tools, time points |
| **Results** | Effect sizes, CIs, p-values, means, SDs, counts |
| **Quality** | Funding, COI declarations, registration status |

### Risk of Bias Assessment

**Tool**: [Specify the tool]
- RCTs: RoB 2 (Sterne et al., 2019)
- Non-randomized studies: ROBINS-I (Sterne et al., 2016)
- Qualitative studies: [e.g., CASP qualitative checklist]

**Process**: [Number of assessors, independence, consensus process]

**Use in synthesis**: [How risk of bias results will inform the synthesis, e.g., sensitivity analysis excluding high-risk studies]

### Data Synthesis

#### Quantitative Synthesis (Meta-Analysis)

**Conditions for meta-analysis**: [Describe when studies will be pooled, e.g., "When ≥ 3 studies report sufficiently similar outcomes measured in comparable populations"]

**Effect measure**: [Specify, e.g., SMD for continuous outcomes, RR for binary outcomes]

**Model**: [Fixed-effect / Random-effects, with justification]

**Heterogeneity assessment**:
- Q-test (significance at p < 0.10)
- I² statistic with 95% CI
- tau² (between-study variance)
- Prediction interval

**Subgroup analyses** (pre-specified):
1. [Subgroup variable 1] — Rationale: [why]
2. [Subgroup variable 2] — Rationale: [why]

**Sensitivity analyses**:
1. Leave-one-out analysis
2. Exclude high risk of bias studies
3. [Other planned sensitivity analyses]

**Software**: [Specify, e.g., R metafor package, RevMan]

#### Narrative Synthesis

**When meta-analysis is not feasible**: [Describe the narrative synthesis approach, e.g., SWiM reporting guideline, vote counting, effect direction plot]

### Meta-Bias Assessment

**Publication bias**: [Methods to assess, e.g., funnel plot + Egger's test if ≥ 10 studies]

**Selective reporting**: [How to detect, e.g., compare protocol to published report, search trial registries]

### Confidence in Cumulative Evidence

**Framework**: GRADE (Grading of Recommendations, Assessment, Development and Evaluations)

[Describe how GRADE will be applied to assess certainty for each outcome]

---

## APPENDICES

### Appendix A: Draft Search Strategy

[Complete search strategy for the primary database]

### Appendix B: Data Extraction Form

[Include or reference the data extraction form]

### Appendix C: PRISMA-P Checklist

[Mark each PRISMA-P item as addressed with the relevant page/section number]

---

## Revision Log

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | [date] | [name] | Initial protocol |
