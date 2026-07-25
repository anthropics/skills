# Preregistration Guide — Research Preregistration Guide

## Purpose
Decision guide and operational manual for research preregistration. Assists the research_architect_agent in determining whether preregistration is needed during the methodology design stage, and guides researchers through the preregistration process.

---

## 1. Preregistration Decision Tree

```
Does your research have the following characteristics?
│
├── Confirmatory research (hypothesis testing)
│   └── Strongly recommend preregistration
│       ├── Has pre-specified statistical hypotheses → Preregister
│       ├── Will conduct significance testing → Preregister
│       └── Has primary outcome variables → Preregister
│
├── Exploratory research
│   └── Preregistration not required (but optional)
│       ├── Qualitative research → Typically not preregistered
│       ├── Data mining / EDA → Typically not preregistered
│       └── But you can preregister the research design and analysis process
│
├── Systematic review / Meta-analysis
│   └── Strongly recommend registration (PROSPERO)
│       └── Many journals require systematic reviews to be pre-registered
│
├── Randomized controlled trial (RCT)
│   └── Must register
│       ├── ICMJE requires RCTs to be pre-registered
│       └── Most journals will not accept unregistered RCTs
│
├── Replication study
│   └── Strongly recommend preregistration
│       └── Preregistration clearly distinguishes original from modified hypotheses
│
└── Secondary data analysis
    └── Recommend preregistration
        └── Prevents HARKing (Hypothesizing After Results are Known)
```

### When Preregistration Is Not Needed

- Purely qualitative research (grounded theory, phenomenology)
- Exploratory data analysis (no pre-specified hypotheses)
- Theoretical or philosophical research
- Literature reviews (except systematic reviews)
- Case reports or case studies

### When Preregistration Is Strongly Recommended

- Any research involving hypothesis testing
- Research involving multiple comparisons
- Research needing to distinguish confirmatory vs. exploratory analyses
- Research that may be questioned for p-hacking or HARKing
- When applying for research funding (demonstrates research rigor)
- When journals explicitly require or encourage preregistration

---

## 2. Preregistration Platform Overview

| Platform | Applicable Field | Features | Cost |
|------|---------|------|------|
| **OSF Registries** | All disciplines | Most widely used, multiple templates, DOI, permanent preservation | Free |
| **PROSPERO** | Systematic reviews | Dedicated to systematic reviews and meta-analyses | Free |
| **AEA Registry** | Economics | American Economic Association's RCT registration platform | Free |
| **AsPredicted** | All disciplines | Simplified preregistration (9 questions), quick to complete | Free |
| **ClinicalTrials.gov** | Clinical trials | US FDA-required RCT registration | Free |
| **EGAP** | Political science | Experiments in Governance and Politics | Free |
| **RIDIE** | Development economics | Registry for International Development Impact Evaluations | Free |

### Platform Selection Guide

```
What is your research?
│
├── Systematic review / meta-analysis → PROSPERO
├── Clinical trial / medical intervention → ClinicalTrials.gov
├── Economics RCT → AEA Registry
├── Just need simple preregistration → AsPredicted
└── All other research → OSF Registries (recommended)
```

---

## 3. 21-Item Core Content Checklist

Based on the OSF Standard Pre-Data Collection Registration format, the following are the 21 core items:

### A. Study Information

| # | Item | Description |
|---|------|------|
| 1 | **Study title** | Descriptive title |
| 2 | **Authors/Research team** | All researchers' names and affiliations |
| 3 | **Research questions** | Main research questions (clear, specific) |
| 4 | **Hypotheses** | Pre-specified hypotheses (including directional predictions) |

### B. Design Plan

| # | Item | Description |
|---|------|------|
| 5 | **Study design** | Experiment/observational, between/within-subjects, factorial design, etc. |
| 6 | **Randomization** | Randomization method (if applicable) |
| 7 | **Blinding** | Blinding level and implementation (if applicable) |
| 8 | **Conditions/manipulations** | Specific description of each experimental condition/group |

### C. Sampling Plan

| # | Item | Description |
|---|------|------|
| 9 | **Existing data** | Whether existing data is being used; nature and status of data |
| 10 | **Data collection procedures** | How data will be collected (survey, interview, experiment, archival) |
| 11 | **Sample size** | Planned sample size and basis for determination |
| 12 | **Sample size rationale** | Power analysis or other sample size calculation method |
| 13 | **Stopping rule** | When to stop collecting data (fixed N / target power reached / time cutoff) |

### D. Variables

| # | Item | Description |
|---|------|------|
| 14 | **Manipulated variables** | Operational definition of independent variables |
| 15 | **Measured variables** | Operational definition and measurement instruments of dependent variables |
| 16 | **Indices** | Specific indicators for each variable (scales, items, scoring methods) |

### E. Analysis Plan

| # | Item | Description |
|---|------|------|
| 17 | **Statistical models** | Primary statistical methods for analysis |
| 18 | **Transformations** | Data transformation plan (e.g., log transformation, standardization) |
| 19 | **Inference criteria** | Significance level (alpha), correction methods, effect size reporting |
| 20 | **Data exclusion** | Exclusion criteria (outlier definition, attention check failure, etc.) |
| 21 | **Exploratory analyses** | Planned but non-primary hypothesis analyses |

---

## 4. Higher Education Research Preregistration Examples

### Example: Effect of Teaching Strategy on Learning Outcomes

```
Title: The Effect of Flipped Classroom on University Students' Critical Thinking
       Skills: A Randomized Controlled Trial

Hypotheses:
H1: Students receiving flipped classroom instruction will score significantly
    higher on the CCTST than students receiving traditional lectures
H2: The benefit of flipped classroom will be greater for students with low
    prior knowledge than for those with high prior knowledge

Design: Cluster-randomized controlled trial (class as randomization unit)
Sample: 12 classes (6 experimental / 6 control), approximately 40 students
        per class, total 480
Power: 80% power to detect d = 0.4, alpha = .05, ICC = 0.05

Primary outcome: CCTST post-test score (controlling for pre-test)
Secondary outcomes: Final exam grade, learning motivation scale
Analysis: Multilevel modeling (students nested in classes)

Exclusion criteria:
- Attendance rate < 50%
- Both pre-test and post-test incomplete
- Attention check questions answered incorrectly

Exploratory analyses:
- Gender × teaching method interaction effect
- Learning motivation as a mediating variable
```

### Example: Systematic Review of University Dropout Factors

```
Title: Factors Influencing University Student Dropout Decisions in Taiwan:
       A Systematic Literature Review

Research question: What factors influence university student dropout decisions
                   in Taiwan?
Databases: Airiti Library, TSSCI, Scopus, Web of Science
Search strategy: (dropout OR withdrawal OR leave)
                 AND (university OR higher education)
                 AND (Taiwan)
Time range: 2010-2025
Inclusion criteria:
- Studies with Taiwan university students as research subjects
- Explore causes or factors of dropout/withdrawal
- Peer-reviewed journal articles or theses/dissertations
Exclusion criteria:
- Research subjects below high school level
- Pure policy commentary (no empirical data)
Quality assessment: Mixed Methods Appraisal Tool (MMAT)
Synthesis method: Thematic synthesis
Registration platform: PROSPERO
```

---

## 5. Preregistration Disclosure Statement Templates

### Disclosing Preregistration in a Paper

#### Standard Statement (Preregistered)
```
This study was preregistered on [Platform] prior to data collection
(registration number: [NUMBER]; URL: [URL]). All hypotheses, sample size
rationale, and analysis plans were specified before data collection began.
Deviations from the preregistered plan are noted in [section/supplementary
materials].
```

#### Disclosure of Deviations from Preregistration
```
Deviations from preregistered plan:
1. [Deviation description]: [Reason for deviation]
2. [Deviation description]: [Reason for deviation]
These deviations do not affect the confirmatory nature of the primary analyses.
The preregistered analyses are reported as planned; additional exploratory
analyses are clearly labeled.
```

#### Disclosure When Not Preregistered
```
This study was not preregistered. While the hypotheses were formulated before
data analysis, the distinction between confirmatory and exploratory analyses
should be interpreted with this limitation in mind.
```

---

## 6. Preregistration vs. Registered Reports

| Aspect | Preregistration | Registered Reports |
|------|-------------------------|-------------------------------|
| **Definition** | Research plan publicly registered in advance | Research plan submitted to a journal for pre-review |
| **Review** | Does not undergo peer review | Stage 1 peer review (research design) |
| **Acceptance timing** | Paper submitted only after completion | Receives "In-Principle Acceptance" (IPA) after passing Stage 1 |
| **Results bias** | Reduced but not eliminated (researchers can still selectively report) | Substantially eliminated (published regardless of results) |
| **Publication bias** | Cannot solve | Effectively solved (null results also published) |
| **Applicable journals** | All journals | Only journals accepting Registered Reports |
| **Difficulty** | Low (just fill in a form) | High (requires complete methodology and passing review) |
| **Flexibility** | Higher (deviations require disclosure but don't block submission) | Lower (major deviations may affect acceptance) |

### Registered Reports Process

```
Stage 1: Submit research plan
├── Introduction (theoretical background, literature review)
├── Methods (complete methodology, analysis plan)
├── Pilot data (if available)
└── Interpretation plan for predicted results
         ↓
Stage 1 Review (research design quality)
├── Accept (In-Principle Acceptance, IPA)
├── Revise and resubmit
└── Reject
         ↓
Stage 2: Conduct research, write results
├── Strictly follow the Stage 1 plan
├── Report all preregistered analyses (including null results)
├── Exploratory analyses clearly labeled
└── Deviations disclosed and explained
         ↓
Stage 2 Review (execution quality)
├── Was the Stage 1 plan faithfully executed?
├── Are results reported completely?
└── Typically not rejected due to null results
         ↓
Publication
```

### Selected Higher Education Journals Supporting Registered Reports

- *Studies in Higher Education*
- *Higher Education*
- *Assessment & Evaluation in Higher Education*
- *Teaching in Higher Education*
- *Educational Research Review*
- *Learning and Instruction*

> Full list: [COS Registered Reports](https://www.cos.io/initiatives/registered-reports)

---

## Quick Reference: 3 Steps to Preregistration

1. **Decide whether to preregister**: Determine if your research involves hypothesis testing
2. **Choose a platform**: Use PROSPERO for systematic reviews, OSF for everything else
3. **Fill in the 21-item checklist**: Use the `templates/preregistration_template.md` template

> Preregistration is not a perfect solution, but it is currently the most practical transparency tool. Even an imperfect preregistration is better than no preregistration at all.
