# Systematic Review Toolkit — Reference Guide

## Purpose

Comprehensive reference for conducting systematic reviews and meta-analyses. Covers Cochrane methodology, PRISMA 2020 reporting, risk of bias instruments, heterogeneity interpretation, GRADE certainty framework, and protocol registration. Used by `risk_of_bias_agent`, `meta_analysis_agent`, `bibliography_agent`, and `report_compiler_agent`.

---

## 1. Cochrane Handbook v6.4 — Key Principles

The Cochrane Handbook for Systematic Reviews of Interventions (v6.4, 2023) is the gold standard reference for systematic review methodology.

### Core Methodology Stages

| Stage | Cochrane Chapter | Key Requirements |
|-------|-----------------|-----------------|
| Planning | Ch 1-3 | Protocol registration, clear objectives, PICOS |
| Searching | Ch 4 | Comprehensive search (≥ 2 databases), documented strategy |
| Selecting | Ch 4 | Independent dual screening, predefined criteria |
| Data extraction | Ch 5 | Standardized forms, pilot testing, dual extraction |
| Risk of bias | Ch 8 (RoB 2), Ch 25 (ROBINS-I) | Domain-based assessment, signaling questions |
| Synthesis | Ch 10-12 | Appropriate statistical methods, heterogeneity assessment |
| GRADE | Ch 14 | Certainty of evidence for each outcome |
| Reporting | Ch 15 | PRISMA 2020 compliance |

### Fundamental Principles

1. **A priori protocol**: Register the protocol before conducting the review (PROSPERO, OSF)
2. **Comprehensive searching**: Search multiple databases; do not rely on a single source
3. **Dual independent processes**: Two reviewers for screening, extraction, and risk of bias (at minimum for a subset)
4. **Pre-specified methods**: Analysis plan defined before seeing results
5. **Transparent reporting**: Document everything; another team should be able to replicate the review

---

## 2. PRISMA 2020 — Full 27-Item Checklist

**Full Name**: Preferred Reporting Items for Systematic Reviews and Meta-Analyses
**Reference**: Page et al. (2021). BMJ, 372, n71. https://doi.org/10.1136/bmj.n71

### Title and Abstract

| # | Item | Guidance |
|---|------|---------|
| 1 | **Title** | Identify the report as a systematic review, meta-analysis, or both |
| 2 | **Abstract** | Structured summary: background, objectives, data sources, study eligibility criteria, participants, interventions, study appraisal/synthesis methods, results, limitations, conclusions, registration number |

### Introduction

| # | Item | Guidance |
|---|------|---------|
| 3 | **Rationale** | Describe the rationale for the review in the context of existing knowledge |
| 4 | **Objectives** | Provide an explicit statement of the questions being addressed with reference to PICOS |

### Methods

| # | Item | Guidance |
|---|------|---------|
| 5 | **Eligibility criteria** | Specify inclusion and exclusion criteria (PICOS components, date range, language, publication status) |
| 6 | **Information sources** | Describe all information sources searched (databases, registers, websites, organizations, reference lists) with dates |
| 7 | **Search strategy** | Present the complete search strategy for at least one database, including any filters and limits |
| 8 | **Selection process** | State methods for deciding which studies met eligibility criteria (number of reviewers, consensus process) |
| 9 | **Data collection process** | Describe methods for extracting data (number of reviewers, whether independently, any processes for obtaining/confirming data from investigators) |
| 10 | **Data items** | List and define all outcome variables and other variables extracted |
| 11 | **Study risk of bias assessment** | Describe methods for assessing risk of bias in included studies, including tools used and how results were used in synthesis |
| 12 | **Effect measures** | Specify for each outcome the effect measure(s) used (e.g., RR, MD, SMD) |
| 13a | **Synthesis methods** | Describe the processes used to decide which studies were eligible for each synthesis |
| 13b | | Describe any methods required to prepare the data for synthesis (e.g., handling multi-arm studies) |
| 13c | | Describe any methods used to tabulate or visually display results of individual studies and syntheses |
| 13d | | Describe any methods used to synthesize results and rationale (meta-analysis: model, software; narrative: SWiM) |
| 13e | | Describe any methods used to explore possible causes of heterogeneity (subgroup, meta-regression) |
| 13f | | Describe any sensitivity analyses conducted |
| 14 | **Reporting bias assessment** | Describe any methods used to assess risk of bias due to missing results (publication bias) |
| 15 | **Certainty assessment** | Describe any methods used to assess certainty in the body of evidence (e.g., GRADE) |

### Results

| # | Item | Guidance |
|---|------|---------|
| 16a | **Study selection** | Describe results of the search and selection process, ideally using a PRISMA flow diagram |
| 16b | | Cite studies that appeared to meet inclusion criteria but were excluded, and explain why |
| 17 | **Study characteristics** | For each included study cite it and present its characteristics |
| 18 | **Risk of bias in studies** | Present assessments of risk of bias for each included study |
| 19 | **Results of individual studies** | For all outcomes, present for each study: summary data, effect estimates and CIs, results of syntheses |
| 20a | **Results of syntheses** | For each synthesis, briefly summarize the characteristics and risk of bias among contributing studies |
| 20b | | Present results of all statistical syntheses conducted, including CIs and measures of heterogeneity |
| 20c | | Present results of all investigations of possible causes of heterogeneity |
| 20d | | Present results of all sensitivity analyses |
| 21 | **Reporting biases** | Present assessments of risk of bias due to missing results |
| 22 | **Certainty of evidence** | Present assessments of certainty of evidence for each outcome assessed |

### Discussion

| # | Item | Guidance |
|---|------|---------|
| 23 | **Discussion** | Provide a general interpretation of results in the context of other evidence, discuss limitations of the evidence and of the review process, implications |
| 24 | **Registration and protocol** | Provide registration information including register name and registration number, and a link to the protocol |
| 25 | **Support** | Describe sources of financial or non-financial support and the role of funders |
| 26 | **Competing interests** | Declare any competing interests of review authors |
| 27 | **Availability of data, code, and other materials** | Report which of the following are publicly available: template data collection forms, data extracted from included studies, analysis code, any other materials |

### PRISMA 2020 Flow Diagram

```
 ┌─────────────────────────────────────────────────────┐
 │                 IDENTIFICATION                      │
 ├─────────────────────────────────────────────────────┤
 │ Records identified from databases (n = )            │
 │ Records identified from other sources (n = )        │
 └──────────────────────┬──────────────────────────────┘
                        │
 ┌──────────────────────▼──────────────────────────────┐
 │ Records removed before screening:                   │
 │   Duplicate records (n = )                          │
 │   Records marked as ineligible by automation (n = ) │
 │   Records removed for other reasons (n = )          │
 └──────────────────────┬──────────────────────────────┘
                        │
 ┌──────────────────────▼──────────────────────────────┐
 │                  SCREENING                          │
 ├─────────────────────────────────────────────────────┤
 │ Records screened (n = )                             │
 │ Records excluded (n = )                             │
 └──────────────────────┬──────────────────────────────┘
                        │
 ┌──────────────────────▼──────────────────────────────┐
 │ Reports sought for retrieval (n = )                 │
 │ Reports not retrieved (n = )                        │
 └──────────────────────┬──────────────────────────────┘
                        │
 ┌──────────────────────▼──────────────────────────────┐
 │ Reports assessed for eligibility (n = )             │
 │ Reports excluded, with reasons (n = )               │
 │   Reason 1 (n = )                                   │
 │   Reason 2 (n = )                                   │
 │   Reason 3 (n = )                                   │
 └──────────────────────┬──────────────────────────────┘
                        │
 ┌──────────────────────▼──────────────────────────────┐
 │                  INCLUDED                           │
 ├─────────────────────────────────────────────────────┤
 │ Studies included in review (n = )                   │
 │ Reports of included studies (n = )                  │
 │                                                     │
 │ Studies included in quantitative synthesis (n = )   │
 └─────────────────────────────────────────────────────┘
```

---

## 3. RoB 2 Instrument Summary

**Full Name**: Risk of Bias tool for randomized trials (version 2)
**Reference**: Sterne et al. (2019). BMJ, 366, l4898. https://doi.org/10.1136/bmj.l4898

### Domains

| Domain | Abbreviation | Focus |
|--------|-------------|-------|
| Bias arising from the randomization process | D1 | Sequence generation, allocation concealment, baseline balance |
| Bias due to deviations from intended interventions | D2 | Blinding, protocol adherence, ITT analysis |
| Bias due to missing outcome data | D3 | Completeness, differential dropout, handling of missing data |
| Bias in measurement of the outcome | D4 | Outcome assessment method, blinding of assessors |
| Bias in selection of the reported result | D5 | Pre-registration, selective reporting |

### Judgment Scale

- **Low risk of bias**: The study is judged to be at low risk of bias for this domain
- **Some concerns**: The study raises some concerns about bias for this domain
- **High risk of bias**: The study is judged to be at high risk of bias for this domain

### Overall Judgment Algorithm

- All domains Low → Overall **Low**
- Some Concerns in ≥ 1 domain, no High → Overall **Some Concerns**
- High in ≥ 1 domain → Overall **High**

---

## 4. ROBINS-I Summary

**Full Name**: Risk Of Bias In Non-randomized Studies of Interventions
**Reference**: Sterne et al. (2016). BMJ, 355, i4919. https://doi.org/10.1136/bmj.i4919

### Domains (7 domains spanning 3 time points)

**Pre-intervention**:
- D1: Bias due to confounding
- D2: Bias in selection of participants into the study

**At intervention**:
- D3: Bias in classification of interventions

**Post-intervention**:
- D4: Bias due to deviations from intended interventions
- D5: Bias due to missing data
- D6: Bias in measurement of outcomes
- D7: Bias in selection of the reported result

### Judgment Scale

- **Low risk**: Comparable to a well-performed RCT
- **Moderate risk**: Sound for a non-randomized study but cannot be considered comparable to a well-performed RCT
- **Serious risk**: Some important problems
- **Critical risk**: Study is too problematic to provide useful evidence
- **No information**: Insufficient reporting

---

## 5. I² Interpretation Guide

| I² Range | Label | What It Means | Action |
|----------|-------|---------------|--------|
| 0-40% | Low | Heterogeneity might not be important | Proceed with pooling; report I² |
| 30-60% | Moderate | May represent moderate heterogeneity | Proceed with pooling; investigate sources |
| 50-90% | Substantial | Substantial heterogeneity | Investigate sources; consider subgroup analyses; report prediction interval |
| 75-100% | Considerable | Considerable heterogeneity | Question whether pooling is meaningful; consider narrative synthesis |

**Important caveats**:
- Ranges overlap intentionally (per Cochrane Handbook 10.10.2)
- I² significance depends on: magnitude of effects, p-value from Q-test, and visual inspection of forest plot
- A high I² with all effects in the same direction is less concerning than moderate I² with effects crossing zero
- I² is influenced by precision of studies — many precise studies can yield high I² even with small absolute differences
- Always report the 95% CI for I² (which can be very wide with few studies)

---

## 6. GRADE Certainty of Evidence Framework

**Full Name**: Grading of Recommendations, Assessment, Development and Evaluations
**Reference**: Guyatt et al. (2008). BMJ, 336, 924-926.

### Starting Points

| Study Design | Starting Certainty |
|-------------|-------------------|
| Randomized trials | HIGH (⊕⊕⊕⊕) |
| Non-randomized studies | LOW (⊕⊕◯◯) |

### Factors That Lower Certainty (Rate Down)

| Factor | Rate Down | When to Apply |
|--------|-----------|---------------|
| Risk of bias | -1 or -2 | Serious or very serious limitations in study design/execution |
| Inconsistency | -1 or -2 | Unexplained heterogeneity (I² > 50%, different directions of effect) |
| Indirectness | -1 or -2 | Evidence does not directly address the PICOS of the review question |
| Imprecision | -1 or -2 | Wide CIs, small sample sizes, CIs cross clinical decision threshold |
| Publication bias | -1 | Funnel plot asymmetry, small study effects, known unpublished trials |

### Factors That Raise Certainty (Rate Up — Observational Studies Only)

| Factor | Rate Up | When to Apply |
|--------|---------|---------------|
| Large effect | +1 or +2 | RR > 2 or < 0.5 (large), RR > 5 or < 0.2 (very large), without confounders |
| Dose-response gradient | +1 | Clear dose-response relationship observed |
| Plausible confounding | +1 | All plausible confounders would reduce the observed effect |

### Certainty Levels

| Level | Symbol | Meaning |
|-------|--------|---------|
| High | ⊕⊕⊕⊕ | Very confident the true effect lies close to the estimate |
| Moderate | ⊕⊕⊕◯ | Moderately confident; the true effect is likely close but may be substantially different |
| Low | ⊕⊕◯◯ | Limited confidence; the true effect may be substantially different |
| Very Low | ⊕◯◯◯ | Very little confidence; the true effect is likely substantially different |

---

## 7. Protocol Registration Guidance

### When to Register

- **Always** for systematic reviews intended for publication
- **Before** starting the literature search
- Registration prevents outcome reporting bias and demonstrates a priori planning

### Where to Register

| Platform | Focus | Cost | URL |
|----------|-------|------|-----|
| **PROSPERO** | Health-related systematic reviews | Free | crd.york.ac.uk/prospero |
| **OSF Registries** | Any discipline | Free | osf.io/registries |
| **INPLASY** | Any discipline | ~$40 | inplasy.com |
| **Research Registry** | Any discipline | Free for systematic reviews | researchregistry.com |

### Protocol Content (PRISMA-P 2015)

See `templates/prisma_protocol_template.md` for the complete protocol template.

Key sections:
1. Title, registration, authors, amendments
2. Rationale, objectives, PICOS eligibility criteria
3. Information sources, search strategy, study records management
4. Data extraction, risk of bias assessment, data synthesis plan
5. Meta-bias assessment, confidence in cumulative evidence

---

## 8. Software and Tools

### Statistical Software for Meta-Analysis

| Tool | Language | Best For | Key References |
|------|----------|----------|---------------|
| **metafor** (R) | R | Comprehensive meta-analysis (all models, diagnostics) | Viechtbauer (2010) |
| **meta** (R) | R | User-friendly standard meta-analyses | Balduzzi et al. (2019) |
| **dmetar** (R) | R | Companion to "Doing Meta-Analysis in R" textbook | Harrer et al. (2021) |
| **RevMan** | Standalone | Cochrane reviews (required for Cochrane) | Cochrane Collaboration |
| **robvis** (R) | R | Risk of bias visualization (traffic-light plots) | McGuinness & Higgins (2020) |
| **GRADE pro GDT** | Web-based | GRADE Summary of Findings tables | McMaster University |

### Screening and Management Tools

| Tool | Purpose | Cost |
|------|---------|------|
| **Covidence** | Study screening, data extraction, RoB | Paid (free Cochrane license) |
| **Rayyan** | Abstract screening (AI-assisted) | Free |
| **EPPI-Reviewer** | Full review management | Paid |
| **ASReview** | AI-assisted screening | Free (open source) |
| **Zotero/Mendeley** | Reference management | Free |

---

## Quick Decision Guide

```
Starting a systematic review?
│
├── 1. Register your protocol
│   └── PROSPERO (health) or OSF (any field)
│
├── 2. Write your protocol
│   └── Use PRISMA-P template → templates/prisma_protocol_template.md
│
├── 3. Search systematically
│   └── ≥ 2 databases, document everything, PRISMA flow
│
├── 4. Screen and select
│   └── Dual screening, predefined criteria
│
├── 5. Assess risk of bias
│   └── RCTs → RoB 2 | Non-randomized → ROBINS-I
│
├── 6. Synthesize evidence
│   ├── Quantitative data + comparable studies → Meta-analysis
│   └── Otherwise → Narrative synthesis (SWiM)
│
├── 7. Assess certainty
│   └── GRADE for each outcome
│
└── 8. Report
    └── PRISMA 2020 checklist → templates/prisma_report_template.md
```
