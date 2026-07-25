# PRISMA 2020 — Systematic Review Report Template

## Purpose

Template for writing a systematic review report following PRISMA 2020 (Page et al., 2021). All 27 PRISMA items are mapped to their corresponding sections. Use alongside `references/systematic_review_toolkit.md` for detailed guidance.

**Reference**: Page et al. (2021). The PRISMA 2020 statement: an updated guideline for reporting systematic reviews. BMJ, 372, n71. https://doi.org/10.1136/bmj.n71

---

## Title [PRISMA Item 1]

**[Full title identifying the report as a systematic review, meta-analysis, or both]**

Example: "The Effect of [Intervention] on [Outcome] in [Population]: A Systematic Review and Meta-Analysis"

---

## Abstract [PRISMA Item 2]

### Background
[1-2 sentences on context and why the review was done]

### Objectives
[Research question(s), ideally structured as PICOS]

### Data Sources
[Databases searched and dates of last search]

### Study Selection
[Eligibility criteria in brief]

### Data Extraction and Synthesis
[Methods used for data extraction, risk of bias, and synthesis]

### Results
[Number of studies included, key findings, effect estimates with CIs, certainty of evidence]

### Limitations
[Key limitations of the evidence and/or the review process]

### Conclusions
[General interpretation and implications]

### Registration
[Protocol registration number and repository]

**Keywords**: [3-5 keywords]

---

## 1. Introduction

### 1.1 Rationale [PRISMA Item 3]

[Describe the rationale for the review in the context of existing knowledge. Address:]
- What is the problem or question?
- What is already known (with references to existing reviews)?
- Why is this review needed (e.g., no existing review, existing review outdated, conflicting evidence)?

### 1.2 Objectives [PRISMA Item 4]

[Provide an explicit statement of the question(s) using PICOS:]

- **Population**: [target population]
- **Intervention/Exposure**: [intervention or exposure of interest]
- **Comparator**: [comparison group]
- **Outcome(s)**: [primary and secondary outcomes]
- **Study Design**: [eligible study designs]

---

## 2. Methods

### 2.1 Eligibility Criteria [PRISMA Item 5]

| Criterion | Include | Exclude |
|-----------|---------|---------|
| Study design | [e.g., RCTs, quasi-experimental] | [e.g., case reports, editorials] |
| Population | [describe] | [describe] |
| Intervention | [describe] | [describe] |
| Comparator | [describe] | [describe] |
| Outcome | [describe] | [describe] |
| Time frame | [e.g., published 2014-2024] | [before cutoff] |
| Language | [e.g., English] | [other] |
| Setting | [describe] | [describe] |

### 2.2 Information Sources [PRISMA Item 6]

[List all databases and other sources searched, with dates of coverage and last search date:]

| Source | Date Range | Last Searched |
|--------|-----------|---------------|
| [Database 1] | [start]-[end] | [date] |
| [Database 2] | [start]-[end] | [date] |
| [Other sources: reference lists, expert contact, grey literature] | — | [date] |

### 2.3 Search Strategy [PRISMA Item 7]

[Present the complete search strategy for at least one database. Include all search terms, Boolean operators, and any filters applied.]

**[Database Name] Search Strategy**:
```
#1 [search block 1 - Population terms]
#2 [search block 2 - Intervention terms]
#3 [search block 3 - Outcome terms]
#4 #1 AND #2 AND #3
#5 #4 with filters: [date, language, document type]
```

[Search strategies for other databases are available in Appendix A.]

### 2.4 Selection Process [PRISMA Item 8]

[Describe the study selection process:]
- Number of reviewers at each stage
- How independence was maintained
- How disagreements were resolved
- Software used (e.g., Covidence, Rayyan)
- Pilot testing of screening criteria

### 2.5 Data Collection Process [PRISMA Item 9]

[Describe methods for extracting data from reports:]
- Data extraction form (developed, piloted)
- Number of extractors and independence
- Process for resolving discrepancies
- How missing data were handled (e.g., contacted authors)

### 2.6 Data Items [PRISMA Item 10]

[List all variables for which data were sought:]

| Category | Variables |
|----------|----------|
| Study-level | Authors, year, country, design, setting, funding |
| Participants | N, age, gender, diagnosis/condition, attrition |
| Intervention | Type, duration, frequency, fidelity |
| Outcomes | Definition, measurement tool, time points |
| Results | Effect sizes, CIs, p-values, raw data |

### 2.7 Study Risk of Bias Assessment [PRISMA Item 11]

[Describe the risk of bias assessment:]
- Tool(s) used: [RoB 2 for RCTs / ROBINS-I for non-randomized / other]
- Domains assessed
- Number of assessors and independence
- How results were used in the synthesis

### 2.8 Effect Measures [PRISMA Item 12]

[Specify the effect measure(s) for each outcome:]

| Outcome | Type | Effect Measure | Justification |
|---------|------|---------------|---------------|
| [Outcome 1] | Continuous | SMD (Hedges' g) | Different scales across studies |
| [Outcome 2] | Binary | RR | Incidence data |

### 2.9 Synthesis Methods [PRISMA Items 13a-13f]

**13a. Eligibility for synthesis**: [Criteria for grouping studies into each synthesis]

**13b. Data preparation**: [Methods to prepare data, e.g., converting SE to SD, handling multi-arm studies]

**13c. Tabulation/visualization**: [Methods for displaying individual study and synthesis results, e.g., forest plots, summary tables]

**13d. Synthesis approach**: [Statistical model and software]
- Model: [Fixed-effect / Random-effects (DerSimonian-Laird / REML)]
- Software: [R metafor / RevMan / Stata]
- OR if narrative: [SWiM approach, vote counting, effect direction plot]

**13e. Heterogeneity exploration**: [Methods used]
- Subgroup analyses: [pre-specified subgroups and rationale]
- Meta-regression: [covariates tested, if applicable]

**13f. Sensitivity analyses**: [Planned sensitivity analyses]
1. Leave-one-out analysis
2. Excluding high risk of bias studies
3. Fixed-effect vs. random-effects comparison
4. [Other analyses]

### 2.10 Reporting Bias Assessment [PRISMA Item 14]

[Methods to assess publication bias:]
- Funnel plot (visual inspection)
- Statistical test: [Egger's / Peter's / trim-and-fill]
- Comparison of protocol to published reports

### 2.11 Certainty Assessment [PRISMA Item 15]

[Framework used to assess certainty of evidence:]
- GRADE approach
- Factors assessed: risk of bias, inconsistency, indirectness, imprecision, publication bias
- Rating up factors (for observational studies): large effect, dose-response, plausible confounding

---

## 3. Results

### 3.1 Study Selection [PRISMA Item 16a, 16b]

#### PRISMA Flow Diagram

```
 ┌─────────────────────────────────────────────────────┐
 │                 IDENTIFICATION                      │
 ├─────────────────────────────────────────────────────┤
 │ Records identified from databases (n = )            │
 │   Database 1 (n = )                                 │
 │   Database 2 (n = )                                 │
 │   Database 3 (n = )                                 │
 │ Records identified from other sources (n = )        │
 │   Reference lists (n = )                            │
 │   Expert recommendations (n = )                     │
 └──────────────────────┬──────────────────────────────┘
                        │
 ┌──────────────────────▼──────────────────────────────┐
 │ Records removed before screening:                   │
 │   Duplicate records (n = )                          │
 │   Records marked ineligible by automation (n = )    │
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
 │ Studies in quantitative synthesis (n = )             │
 └─────────────────────────────────────────────────────┘
```

[PRISMA Item 16b: Cite studies that appeared to meet inclusion criteria but were excluded, with reasons.]

### 3.2 Study Characteristics [PRISMA Item 17]

**Table: Characteristics of Included Studies**

| Study | Country | Design | Population (N) | Intervention | Comparator | Outcome(s) | Follow-up | Funding |
|-------|---------|--------|----------------|-------------|-----------|------------|-----------|---------|
| Author1 (Year) | [country] | [design] | [N] | [intervention] | [comparator] | [outcomes] | [duration] | [source] |
| Author2 (Year) | ... | ... | ... | ... | ... | ... | ... | ... |

### 3.3 Risk of Bias in Studies [PRISMA Item 18]

**Table: Risk of Bias Summary (Traffic-Light)**

| Study | D1 | D2 | D3 | D4 | D5 | Overall |
|-------|----|----|----|----|----|---------|
| Author1 (Year) | [L/S/H] | [L/S/H] | [L/S/H] | [L/S/H] | [L/S/H] | [L/S/H] |
| Author2 (Year) | ... | ... | ... | ... | ... | ... |

L = Low risk, S = Some concerns, H = High risk

[Narrative summary of risk of bias findings across studies]

### 3.4 Results of Individual Studies [PRISMA Item 19]

**Table: Individual Study Results**

| Study | Outcome | Effect Estimate | 95% CI | p-value | Weight |
|-------|---------|----------------|--------|---------|--------|
| Author1 (Year) | [outcome] | [estimate] | [lower, upper] | [p] | [%] |
| Author2 (Year) | ... | ... | ... | ... | ... |

### 3.5 Results of Syntheses [PRISMA Items 20a-20d]

#### Primary Outcome: [Name]

**20a. Study characteristics**: [Brief summary of contributing studies' characteristics and risk of bias]

**20b. Pooled result**:
- Pooled effect: [estimate] (95% CI: [lower, upper])
- Statistical significance: Z = [value], p = [value]
- Heterogeneity: I² = [value]% (95% CI: [lower, upper]), Q = [value] (df = [n], p = [value]), tau² = [value]
- Prediction interval: [lower, upper]

**Forest Plot**: [Insert or reference forest plot]

**20c. Heterogeneity investigation**:
- Subgroup analyses: [results]
- Meta-regression: [results, if conducted]

**20d. Sensitivity analyses**:
1. Leave-one-out: [results — did any single study substantially change the estimate?]
2. Excluding high-risk studies: [revised estimate]
3. Fixed vs. random effects: [comparison]

#### Secondary Outcome(s): [Name]

[Repeat structure above for each secondary outcome]

### 3.6 Reporting Biases [PRISMA Item 21]

[Report assessments of publication bias:]
- Funnel plot: [description of symmetry/asymmetry]
- Statistical test: [result]
- Trim-and-fill: [adjusted estimate, if applicable]
- Other assessments: [protocol-outcome comparison]

### 3.7 Certainty of Evidence [PRISMA Item 22]

**GRADE Summary of Findings Table**

| Outcome | Studies (n) | Participants (N) | Effect (95% CI) | Certainty | Rationale |
|---------|------------|-------------------|-----------------|-----------|-----------|
| [Outcome 1] | [n] | [N] | [estimate (CI)] | [High/Moderate/Low/Very Low] | [Reasons for up/downgrading] |
| [Outcome 2] | [n] | [N] | [estimate (CI)] | [level] | [reasons] |

---

## 4. Discussion [PRISMA Item 23]

### 4.1 Summary of Evidence

[Provide a general interpretation of the results in the context of other evidence. Address:]
- Main findings for each outcome
- How findings compare to previous reviews
- Consistency of findings across studies

### 4.2 Limitations

**Limitations of the evidence**:
- [e.g., risk of bias across studies, inconsistency, indirectness, imprecision]

**Limitations of the review process**:
- [e.g., language restrictions, database coverage, inability to contact authors]

### 4.3 Implications

**For practice**:
- [What practitioners should do based on these findings]

**For research**:
- [Gaps identified, recommended future study designs]

**For policy**:
- [Policy implications, if applicable]

---

## 5. Other Information

### 5.1 Registration and Protocol [PRISMA Item 24]

[Provide registration information and link to protocol:]
- Registry: [e.g., PROSPERO]
- Registration number: [number]
- Protocol URL: [link]
- Deviations from protocol: [describe any deviations and rationale]

### 5.2 Support [PRISMA Item 25]

[Describe sources of support:]
- Financial: [funding sources and grant numbers]
- Non-financial: [e.g., institutional support, access to databases]
- Role of funder: [describe any role of funders in the review]

### 5.3 Competing Interests [PRISMA Item 26]

[Declare competing interests of all authors]

### 5.4 Availability of Data and Materials [PRISMA Item 27]

[Report availability of:]
- [ ] Data extraction forms
- [ ] Extracted data from included studies
- [ ] Analysis code
- [ ] List of excluded studies with reasons
- [ ] PRISMA checklist (completed)

---

## Appendices

### Appendix A: Full Search Strategies

[Complete search strategies for all databases]

### Appendix B: Excluded Studies with Reasons

| Study | Reason for Exclusion |
|-------|---------------------|
| [citation] | [reason] |

### Appendix C: PRISMA 2020 Checklist

[Completed PRISMA 2020 checklist with page/section numbers for each item]

| Item # | Checklist Item | Reported on Page/Section |
|--------|---------------|-------------------------|
| 1 | Title | [page] |
| 2 | Abstract | [page] |
| ... | ... | ... |
| 27 | Availability | [page] |
