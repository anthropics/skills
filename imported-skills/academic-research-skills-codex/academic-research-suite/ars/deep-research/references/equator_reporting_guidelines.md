# EQUATOR Reporting Guidelines — Research Design and Reporting Guideline Mapping

## Purpose
Quick reference for EQUATOR Network (Enhancing the QUAlity and Transparency Of health Research) reporting guidelines. Assists the research_architect_agent in selecting the appropriate reporting checklist during the methodology design stage, and the report_compiler_agent in ensuring report completeness during the writing stage.

---

## 1. Research Design → Reporting Guideline Mapping Table

| Research Design | Primary Reporting Guideline | Applicable Scenario |
|----------|------------|---------|
| Systematic review / Meta-analysis | **PRISMA** | Literature review integrating multiple studies |
| Randomized controlled trial (RCT) | **CONSORT** | Intervention experiments with random assignment |
| Observational study (cohort, case-control, cross-sectional) | **STROBE** | Non-interventional quantitative observational research |
| Qualitative research | **COREQ** | Interviews, focus groups, observation |
| Quality improvement study | **SQUIRE** | Systematic quality improvement project reports |
| Diagnostic accuracy study | STARD | Diagnostic tool evaluation |
| Prognostic study | TRIPOD | Prediction model development and validation |
| Case report | CARE | Single or small number of in-depth case reports |
| Economic evaluation | CHEERS | Cost-effectiveness analysis |
| Mixed methods research | GRAMMS | Mixed qualitative-quantitative designs |
| Animal study | ARRIVE | Animal experiments |
| Network meta-analysis | PRISMA-NMA | Multiple comparison meta-analysis |
| Scoping review | PRISMA-ScR | Scoping review (less stringent than systematic review) |

---

## 2. PRISMA — Systematic Review Condensed Checklist

**Full Name**: Preferred Reporting Items for Systematic Reviews and Meta-Analyses
**Version**: PRISMA 2020 (latest)

### Core Reporting Items

| # | Item | Description | Necessity |
|---|------|------|--------|
| 1 | **Title** | Clearly identify as a systematic review (with or without meta-analysis) | Required |
| 2 | **Abstract** | Structured abstract (background, purpose, methods, results, conclusions) | Required |
| 3 | **Registration** | Registration number and platform (e.g., PROSPERO) | Strongly recommended |
| 4 | **Eligibility criteria** | Inclusion/exclusion criteria in PICOS or PEO format | Required |
| 5 | **Information sources** | Databases searched and dates | Required |
| 6 | **Search strategy** | Complete search strategy for at least one database | Required |
| 7 | **Selection process** | Screening process (number of reviewers, how disagreements were resolved) | Required |
| 8 | **Data extraction** | Data extraction methods | Required |
| 9 | **Risk of bias** | Risk of bias assessment tool and results | Required |
| 10 | **Synthesis methods** | Synthesis method (narrative / meta-analytic) | Required |
| 11 | **PRISMA flow diagram** | Literature screening flow diagram | Required |
| 12 | **Results** | Characteristics of each study, bias assessment, synthesis results | Required |
| 13 | **Discussion** | Certainty of evidence, limitations, relationship to existing knowledge | Required |
| 14 | **Funding** | Funding sources and conflicts of interest | Required |

### PRISMA Flow Diagram Template

```
Records identified (n = )
├── Database searching (n = )
└── Other sources (n = )
         ↓
Duplicates removed (n = )
         ↓
Records screened (n = )
├── Excluded (n = )
         ↓
Reports sought for retrieval (n = )
├── Not retrieved (n = )
         ↓
Reports assessed for eligibility (n = )
├── Excluded, with reasons (n = )
│   ├── Reason 1 (n = )
│   ├── Reason 2 (n = )
│   └── Reason 3 (n = )
         ↓
Studies included in review (n = )
├── In qualitative synthesis (n = )
└── In quantitative synthesis (meta-analysis) (n = )
```

---

## 3. CONSORT — Randomized Controlled Trial Condensed Checklist

**Full Name**: Consolidated Standards of Reporting Trials
**Version**: CONSORT 2010 + extensions

### Core Reporting Items

| # | Item | Description |
|---|------|------|
| 1 | **Title & Abstract** | Identify as RCT; structured abstract |
| 2 | **Background** | Scientific background and trial rationale |
| 3 | **Objectives** | Specific objectives or hypotheses |
| 4 | **Trial design** | Design type (parallel, crossover, factorial, etc.) and allocation ratio |
| 5 | **Participants** | Eligibility criteria, settings, data collection locations |
| 6 | **Interventions** | Specific description of each group's intervention (including how and when administered) |
| 7 | **Outcomes** | Primary and secondary outcome measures, including definitions and time points |
| 8 | **Sample size** | Sample size calculation method (power analysis) |
| 9 | **Randomisation** | Random sequence generation method, allocation concealment mechanism |
| 10 | **Blinding** | Blinding implementation (who was blinded, how it was implemented) |
| 11 | **Statistical methods** | Statistical analysis methods, ITT/PP analysis |
| 12 | **Flow diagram** | Participant flow diagram (recruitment → allocation → follow-up → analysis) |
| 13 | **Results** | Results per group, effect sizes and precision (CI) |
| 14 | **Harms** | Adverse events or side effects |
| 15 | **Limitations** | Sources of bias, imprecision, multiple comparisons |
| 16 | **Registration** | Trial registration number |

### Higher Education Research Application Notes

RCTs in the education field (e.g., comparing teaching methods) commonly face:
- Inability to fully randomize (cluster randomization is more common)
- Difficulty implementing blinding (teachers/students know their group)
- Recommended to use **CONSORT-SPI** (Social and Psychological Interventions extension)

---

## 4. STROBE — Observational Study Condensed Checklist

**Full Name**: Strengthening the Reporting of Observational Studies in Epidemiology
**Applicable to**: Cohort studies, case-control studies, cross-sectional studies

### Core Reporting Items

| # | Item | Description |
|---|------|------|
| 1 | **Title & Abstract** | Indicate the study design type |
| 2 | **Background** | Scientific background, study rationale |
| 3 | **Objectives** | Specific objectives, pre-specified hypotheses |
| 4 | **Study design** | Clearly state the study design (cohort / case-control / cross-sectional) |
| 5 | **Setting** | Setting, location, relevant dates (recruitment, exposure, follow-up) |
| 6 | **Participants** | Eligibility criteria, data sources, sampling method |
| 7 | **Variables** | Outcome variables, exposure variables, potential confounders, effect modifiers |
| 8 | **Data sources** | Data sources and measurement methods for each variable |
| 9 | **Bias** | Methods for addressing potential sources of bias |
| 10 | **Study size** | How the sample size was determined |
| 11 | **Statistical methods** | Statistical methods (including confounder handling, missing data handling) |
| 12 | **Results** | Descriptive statistics, main results (including effect sizes, CI, p-value) |
| 13 | **Discussion** | Key findings, limitations, generalizability, consistency with other studies |
| 14 | **Funding** | Funding sources |

### Higher Education Research Application Notes

Common observational studies in higher education:
- Student learning outcome cross-sectional survey → cross-sectional STROBE
- Graduate employment tracking → cohort STROBE
- Dropout risk factor analysis → case-control STROBE

---

## 5. COREQ — Qualitative Research Condensed Checklist

**Full Name**: Consolidated Criteria for Reporting Qualitative Research
**Applicable to**: Interviews, focus groups

### Core Reporting Items (32 items, across 3 domains)

#### Domain 1: Research Team and Reflexivity

| # | Item | Description |
|---|------|------|
| 1 | **Interviewer/facilitator** | Who conducted the interviews or facilitated focus groups |
| 2 | **Credentials** | Researcher qualifications |
| 3 | **Occupation** | Researcher's professional identity |
| 4 | **Gender** | Researcher gender |
| 5 | **Experience & training** | Qualitative research experience and training |
| 6 | **Relationship with participants** | Researcher's relationship with participants |
| 7 | **Participant knowledge** | Participants' level of knowledge about the research |

#### Domain 2: Study Design

| # | Item | Description |
|---|------|------|
| 8 | **Methodological orientation** | Theoretical framework (e.g., grounded theory, phenomenology) |
| 9 | **Sampling** | Sampling strategy and method |
| 10 | **Method of approach** | How participants were contacted |
| 11 | **Sample size** | Number of participants |
| 12 | **Non-participation** | Number and reasons for refusal to participate |
| 13 | **Setting** | Interview location |
| 14 | **Presence of non-participants** | Whether non-participants were present during interviews |
| 15 | **Description of sample** | Participant demographics |
| 16 | **Interview guide** | Whether an interview guide was used and whether it was pilot-tested |
| 17 | **Repeat interviews** | Whether repeat interviews were conducted |
| 18 | **Audio/visual recording** | Whether audio/video was recorded |
| 19 | **Field notes** | Whether field notes were taken |
| 20 | **Duration** | Interview duration |
| 21 | **Data saturation** | Whether data saturation was discussed |
| 22 | **Transcripts returned** | Whether transcripts were returned to participants for feedback |

#### Domain 3: Analysis and Findings

| # | Item | Description |
|---|------|------|
| 23 | **Data analysis** | Analysis method (e.g., thematic analysis, IPA) |
| 24 | **Software** | Analysis software used |
| 25 | **Participant checking** | Whether participants confirmed the findings |
| 26 | **Quotations** | Whether quotations are presented to support themes |
| 27 | **Data and findings consistency** | Consistency between data and findings |
| 28 | **Clarity of major themes** | Whether major themes are clearly presented |
| 29 | **Clarity of minor themes** | Whether minor themes are clearly presented |

---

## 6. SQUIRE — Quality Improvement Study Condensed Checklist

**Full Name**: Standards for QUality Improvement Reporting Excellence
**Version**: SQUIRE 2.0
**Applicable to**: Quality improvement projects, systematic quality improvement, higher education quality assurance (QA) research

### Core Reporting Items

| # | Item | Description |
|---|------|------|
| 1 | **Title** | Identify as a quality improvement study |
| 2 | **Abstract** | Structured abstract |
| 3 | **Problem description** | Nature and severity of the quality problem |
| 4 | **Available knowledge** | Known relevant evidence |
| 5 | **Rationale** | Theoretical basis for the improvement initiative |
| 6 | **Specific aims** | Specific improvement goals (quantifiable) |
| 7 | **Context** | Environmental context of the improvement |
| 8 | **Intervention(s)** | Specific description of improvement measures |
| 9 | **Study of the intervention(s)** | How the improvement effectiveness was evaluated |
| 10 | **Measures** | Outcome measures, process measures, balancing measures |
| 11 | **Analysis** | Quantitative/qualitative analysis methods |
| 12 | **Ethical considerations** | Ethics review (if applicable) |
| 13 | **Results** | Improvement results (including time series data) |
| 14 | **Discussion** | Key findings, relationship to context, generalizability |
| 15 | **Limitations** | Study limitations |

### Particularly Applicable for Higher Education QA Research

SQUIRE is especially valuable as a reference for the following HE quality assurance research:
- **Teaching quality improvement**: Introduction and evaluation of new teaching strategies
- **Curriculum reform**: Tracking the effects of curriculum redesign
- **Student support service improvement**: Systematic improvement of tutoring, counseling, and learning support
- **HEEACT accreditation self-improvement**: Improvement actions and tracking in response to accreditation findings
- **Institutional research (IR)-driven improvement**: Data-based decision-making and improvement cycles

---

## 7. Higher Education Research Context Recommendations

### Commonly Used Guidelines Ranking

| Rank | Guideline | Common HE Usage Scenario |
|------|------|----------------|
| 1 | **PRISMA** | Systematic review of education policy, teaching strategy meta-analysis |
| 2 | **COREQ** | Teacher/student experience interviews, focus groups |
| 3 | **STROBE** | Student surveys, institutional data analysis |
| 4 | **SQUIRE** | Teaching quality improvement, QA accreditation |
| 5 | **CONSORT** | Teaching intervention experiments (less common but high impact) |

### Research Design Quick Selection

```
What is your research type?
│
├── Integrating existing research → PRISMA
│   ├── Systematic review → PRISMA 2020
│   ├── Scoping review → PRISMA-ScR
│   └── Meta-analysis → PRISMA + MOOSE
│
├── Intervention experiment → CONSORT
│   ├── Individual randomization → CONSORT 2010
│   ├── Class/school randomization → CONSORT-Cluster
│   └── Social/psychological intervention → CONSORT-SPI
│
├── Observational survey → STROBE
│   ├── Cross-sectional survey → STROBE-CS
│   ├── Follow-up study → STROBE-Cohort
│   └── Retrospective comparison → STROBE-CC
│
├── Qualitative research → COREQ
│   ├── Interviews → COREQ
│   ├── Focus groups → COREQ
│   └── Ethnography → SRQR (alternative)
│
└── Quality improvement → SQUIRE
    ├── PDSA cycle → SQUIRE 2.0
    └── QA/accreditation improvement → SQUIRE 2.0
```

---

## Quick Reference: 3 Steps to Choosing a Reporting Guideline

1. **Identify your research design**: What type of research design is your study?
2. **Check the mapping table**: Find the corresponding reporting guideline
3. **Download the checklist**: Go to [EQUATOR Network](https://www.equator-network.org/) and download the full checklist

> Reminder: Reporting guidelines represent the minimum standard, not the quality ceiling. Meeting the checklist doesn't guarantee high research quality, but failing to meet the checklist typically indicates deficiencies in reporting quality.
