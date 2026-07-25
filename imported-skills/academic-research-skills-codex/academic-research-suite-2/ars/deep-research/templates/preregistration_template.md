# Preregistration Template — OSF Standard 21-Item Preregistration Template

## Purpose
A fill-in template based on the OSF Standard Pre-Data Collection Registration format. Researchers complete this template before data collection and upload it to a preregistration platform (e.g., OSF Registries).

---

## Instructions

1. Complete this template **before** data collection
2. Items marked `[Required]` are mandatory; `[Optional]` are recommended but not required
3. If an item is not applicable, write "Not applicable" and briefly explain why
4. After completion, go to [OSF Registries](https://osf.io/registries) to create a preregistration
5. Once submitted, preregistrations cannot be modified (an embargo period can be set)

---

## A. Study Information

### 1. Title [Required]
> Study Title

```
[Enter descriptive study title]
```

### 2. Authors [Required]
> Research Team

| Name | Institution | Role | ORCID |
|------|-------------|------|-------|
| [Name] | [Institution] | [PI / Co-PI / RA] | [ORCID] |
| [Name] | [Institution] | [Role] | [ORCID] |

### 3. Research Questions [Required]
> Main Research Questions

```
RQ1: [Enter main research question]
RQ2: [Enter secondary research question, if any]
```

### 4. Hypotheses [Required]
> Pre-specified Hypotheses
> Please state directional predictions clearly

```
H1: [Enter hypothesis 1, including expected direction]
    Example: Students receiving treatment X will score significantly higher
    on test Y than the control group

H2: [Enter hypothesis 2, if any]

H3: [Enter hypothesis 3, if any]
```

---

## B. Design Plan

### 5. Study Type [Required]
> Study Design

- [ ] Experiment
  - [ ] Between-subjects
  - [ ] Within-subjects
  - [ ] Mixed design
  - [ ] Factorial design: ___ x ___
- [ ] Observational study
  - [ ] Cross-sectional
  - [ ] Longitudinal / Cohort
  - [ ] Case-control
- [ ] Survey
- [ ] Other: [Describe]

```
[Describe study design in detail]
```

### 6. Randomization [Optional]
> Randomization Procedure

```
Randomization method: [Simple random / Stratified random / Cluster random / Block random / Not applicable]
Randomization unit: [Individual / Class / School / Not applicable]
Randomization tool: [Random number table / Computer program / Lottery / Not applicable]
Allocation ratio: [1:1 / 2:1 / Other]
```

### 7. Blinding [Optional]
> Blinding / Masking

```
Blinding level: [No blinding / Single-blind / Double-blind / Triple-blind]
Blinded parties: [Participants / Researchers / Assessors / Not applicable]
Blinding maintenance: [Describe how blinding is maintained]
Unblinding timing: [Describe when unblinding occurs]
```

### 8. Study Design / Conditions [Required]
> Specific description of each group/condition

```
Experimental group/Condition 1: [Describe intervention content, duration, frequency in detail]
Experimental group/Condition 2: [If any]
Control group: [Describe control condition in detail]
```

---

## C. Sampling Plan

### 9. Existing Data [Required]
> Existing Data Declaration

- [ ] No data have been collected yet (Registration prior to creation of data)
- [ ] Data exist but have not been examined (Registration prior to any human observation of the data)
- [ ] Some data have been examined (Registration prior to accessing the data)
- [ ] Data have been used for preliminary analysis (Registration following analysis of the data)

```
[Describe data status and your level of familiarity with the data]
```

### 10. Data Collection Procedures [Required]
> Data Collection Procedures

```
Collection method: [Online survey / Paper survey / Interview / Experiment / Archival data / Other]
Collection instruments: [Questionnaire name / Scale name / Experimental software]
Collection location: [Online / Classroom / Laboratory / Other]
Collection timeline: [Start and end dates]
Data collectors: [Who is responsible for collection]
```

### 11. Sample Size [Required]
> Planned sample size

```
Target sample size: [N = ]
Sample size per group: [Experimental group n = , Control group n = ]
```

### 12. Sample Size Rationale [Required]
> Basis for sample size determination

```
Method: [Power analysis / Prior research conventions / Feasibility constraints / Other]

Power analysis parameters (if applicable):
- Effect size: [d = / f = / r = ]
- Effect size source: [Prior study / Meta-analysis / Pilot study]
- Significance level (alpha): [.05 / .01]
- Statistical power: [.80 / .90]
- Test type: [t-test / ANOVA / Regression / Other]
- Calculation tool: [G*Power / R / Other]
- Calculation result: Minimum required N = [  ]

Oversampling rate: [Accounting for ___% attrition, actual target N = ]
```

### 13. Stopping Rule [Required]
> When to stop data collection

```
Stopping rule:
- [ ] Stop when target sample size is reached
- [ ] Stop at specified date (Deadline: [Date])
- [ ] Stop when target power is reached (sequential analysis)
- [ ] Other: [Describe]
```

---

## D. Variables

### 14. Manipulated Variables [Required for experiments]
> Independent Variables

```
Independent variable 1: [Name]
Operational definition: [How it is manipulated]
Levels: [Level 1 / Level 2 / ...]

Independent variable 2: [If any]
```

### 15. Measured Variables [Required]
> Dependent Variables

```
Primary dependent variable: [Name]
Operational definition: [How it is measured]
Measurement instrument: [Scale name / Test name]
Reliability and validity: [Cite reliability/validity literature]

Secondary dependent variable: [If any]

Covariates/Control variables: [If any]
```

### 16. Indices [Required]
> Specific scoring method for each variable

```
Variable 1 scoring:
- Items: [Which items]
- Scoring method: [Sum / Mean / Factor score / Other]
- Reverse-scored items: [Which items need reverse scoring]
- Missing data handling: [How to handle missing values]

Variable 2 scoring: [Same format as above]
```

---

## E. Analysis Plan

### 17. Statistical Models [Required]
> Primary statistical analysis methods

```
Analysis for Hypothesis 1:
- Statistical method: [Independent t-test / ANOVA / Regression / HLM / SEM / Other]
- Detailed description: [Model specification, e.g., DV ~ IV + covariate + (1|cluster)]

Analysis for Hypothesis 2: [Same format as above]
```

### 18. Transformations [Optional]
> Data transformation plan

```
Planned transformations:
- [ ] No transformations
- [ ] Log transformation: Applied to [which variables], trigger condition [skewness > ]
- [ ] Standardization (Z-score)
- [ ] Other: [Describe]
```

### 19. Inference Criteria [Required]
> Statistical inference criteria

```
Significance level: alpha = [.05 / .01 / .005]
Multiple comparison correction: [Bonferroni / Holm / FDR / Not applicable]
Effect size reporting: [Cohen's d / eta-squared / R² / Other]
Confidence interval: [95% CI / 99% CI]
One-tailed/Two-tailed test: [Two-tailed / One-tailed, with justification]
```

### 20. Data Exclusion [Required]
> Data exclusion criteria

```
Exclusion criteria:
- [ ] Failed attention check (Specific criteria: [                ])
- [ ] Response time too short/long (Criteria: < [  ] minutes or > [  ] minutes)
- [ ] Outliers (Definition: [> 3 SD / IQR method / Other])
- [ ] Incomplete rate > [  ]%
- [ ] Other: [Describe]

Post-exclusion procedures:
- Report pre- and post-exclusion sample sizes
- Compare characteristics of excluded vs. retained samples
```

### 21. Exploratory Analyses [Optional]
> Planned exploratory analyses

```
Exploratory analyses (not primary hypotheses, but planned):
1. [Analysis description]
2. [Analysis description]

These analyses will be explicitly labeled as "exploratory" in the paper.
```

---

## F. Other

### Ethics Review [Optional]
```
IRB review status: [Approved / Under review / Exempt / Not applicable]
IRB number: [                ]
Reviewing institution: [                ]
```

### Data Availability [Optional]
```
Will data be made public: [Yes / No / Partially]
Data repository: [OSF / Dataverse / Other]
Timing: [After publication / After study completion / Other]
```

### Supplementary Materials [Optional]
```
- [ ] Full questionnaire/scale
- [ ] Stimulus materials
- [ ] Analysis code
- [ ] Power analysis report
- [ ] Pilot study results
```

---

## Pre-Submission Checklist

- [ ] All [Required] items have been completed
- [ ] Hypotheses are clearly stated and testable
- [ ] Analysis methods correspond to hypotheses
- [ ] Exclusion criteria were established before data collection
- [ ] Confirmatory and exploratory analyses have been distinguished
- [ ] IRB review status has been confirmed
- [ ] Preregistration platform has been selected (OSF Registries recommended)

> After completion, go to [OSF Registries](https://osf.io/registries) to submit the preregistration.
