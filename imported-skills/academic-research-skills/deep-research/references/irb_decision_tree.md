# IRB Decision Tree — Human Subjects Research Ethics Review Guide

## Purpose
IRB (Institutional Review Board) ethics review decision tree and Taiwan process guide. Used by the ethics_review_agent to determine whether research involves human subjects, and by the research_architect_agent to plan IRB review during methodology design.

---

## 1. Human Subjects Research Determination Decision Tree

```
Does your research collect, use, or analyze data from humans?
│
├── No → Does not involve human subjects, no IRB review needed
│         (e.g., pure theoretical research, literature review, secondary analysis of public statistics)
│
└── Yes → Is the data personally identifiable?
          │
          ├── No → Is the data publicly available public data?
          │        │
          │        ├── Yes → Typically exempt from review
          │        │         But must still submit an exempt review application to IRB for confirmation
          │        │
          │        └── No → Proceed to "Review Level Determination" below
          │
          └── Yes → Does the research involve direct interaction with subjects?
                    │
                    ├── No → Only uses existing data/specimens
                    │        │
                    │        ├── Data already de-identified → May apply for exempt review
                    │        └── Data contains identifiable information → Expedited or full board review
                    │
                    └── Yes → Proceed to "Review Level Determination" below
```

---

## 2. Three-Level Review System

### 2.1 Exempt Review

**Applicable Conditions** (any one of the following):
- [ ] Uses publicly available, de-identified datasets
- [ ] Research on educational practices in normal educational settings
- [ ] Involves only anonymous surveys (no sensitive topics)
- [ ] Observation of public behavior (no identifiable information recorded)
- [ ] Uses government public statistical data

**Note**: Exempt review does not mean exempt from application — you must still submit to IRB to confirm exempt status.

### 2.2 Expedited Review

**Applicable Conditions** (all must be met):
- [ ] Research risk is no greater than risks ordinarily encountered in daily life (minimal risk)
- [ ] Does not involve vulnerable populations
- [ ] Research methods are on the expedited review category list

**Common Categories**:
- Surveys (containing sensitive but not high-risk topics)
- Interviews (general topics)
- Teaching intervention research (non-invasive)
- Audio/video recording (with consent)
- Secondary analysis of previously collected clinical data

### 2.3 Full Board Review

**Applicable Conditions** (any one of the following):
- [ ] Greater than minimal risk
- [ ] Involves vulnerable populations (children, prisoners, pregnant women, individuals with cognitive impairments)
- [ ] Involves sensitive topics (sexual behavior, illegal behavior, mental health)
- [ ] Uses deception
- [ ] May cause psychological or social harm

---

## 3. Taiwan IRB Process

### 3.1 Governing Authorities

| Authority | Jurisdiction | Legal Basis |
|-----------|-------------|-------------|
| **National Science and Technology Council (formerly MOST)** | NSTC-funded projects involving human research | "NSTC Guidelines for Research Grant Applications" |
| **Ministry of Health and Welfare** | Human research, clinical trials, human biobanks | "Human Subjects Research Act" (2011) |
| **Ministry of Education** | Research ethics in educational settings | Institutional regulations |

### 3.2 Regulatory Framework

| Regulation | Scope | Key Requirements |
|-----------|-------|------------------|
| **Human Subjects Research Act** | Research involving human subjects (surveys, interviews, observations, interventions) | Prior review, informed consent, personal data protection |
| **Personal Data Protection Act** | Collection, processing, and use of personal data | Notification obligation, purpose limitation, security maintenance |
| **Regulations Governing Human Trials** | Drug/medical device clinical trials | GCP compliance, subject insurance |

### 3.3 Application Process

```
1. Write research proposal
   ↓
2. Determine whether human subjects are involved
   ↓ (Involved)
3. Confirm review level (Exempt / Expedited / Full Board)
   ↓
4. Submit application to institutional IRB
   - Research proposal
   - Informed consent form
   - Questionnaire/interview guide
   - Researcher qualification documentation (CITI or equivalent training)
   ↓
5. IRB review (timeline: Expedited 2-4 weeks, Full Board 4-8 weeks)
   ↓
6. Research may only begin after receiving approval letter
   ↓
7. Periodic progress reports (typically annual)
   ↓
8. Final report
```

### 3.4 Online Research Ethics Review Platforms

| Platform | Description | URL |
|----------|-------------|-----|
| **AREC** (Academic Research Ethics Committee) | Multi-institutional joint ethics review committee | Institutional IRB websites |
| **Institutional IRB systems** | Online application systems within universities | Institutional R&D office websites |
| **CITI Program** | Online research ethics training course | citiprogram.org |
| **Taiwan Research Ethics Education Resource Center** | Research ethics education materials | Institutional teaching development centers |

---

## 4. Higher Education Research Quick Reference Table

| Research Scenario | Involves Human Subjects | Recommended Review Level | Notes |
|-------------------|------------------------|--------------------------|-------|
| MOE public statistical data analysis | No | Exempt | Already publicly available de-identified data |
| Institutional research (IR) data analysis | Depends | Exempt/Expedited | Depends on whether data is de-identified |
| Student learning outcome survey | Yes | Expedited | Anonymous surveys typically qualify for expedited review |
| Teacher interviews (general teaching experience) | Yes | Expedited | Non-sensitive topics |
| Teaching experiment (A/B teaching method comparison) | Yes | Expedited/Full Board | Depends on whether it affects students' grades/rights |
| Student mental health survey | Yes | Full Board | Sensitive topic |
| Vulnerable student population study | Yes | Full Board | Vulnerable population protection |
| Student learning portfolio analysis | Depends | Expedited | Contains identifiable information requiring expedited review |
| Classroom observation (no personal data recorded) | Yes | Exempt/Expedited | Public setting observation |
| Graduate career tracking survey | Yes | Expedited | Contains personal data requiring expedited review |
| HEEACT accreditation data analysis | Depends | Exempt/Expedited | Publicly available portions exempt from review |
| University faculty salary/labor conditions survey | Yes | Expedited/Full Board | May involve institutional power dynamics |

---

## 5. Informed Consent Form Elements

### 5.1 Required Items

- [ ] Research title
- [ ] Research institution and principal investigator name
- [ ] Research purpose
- [ ] Research procedures description (what subjects need to do, how long it takes)
- [ ] Potential risks and discomfort
- [ ] Potential benefits
- [ ] Confidentiality measures (how data is stored, who has access, retention period)
- [ ] Voluntary nature of participation (may withdraw at any time, no penalties)
- [ ] Researcher contact information
- [ ] IRB contact information (complaint channel)
- [ ] Subject signature and date field

### 5.2 Special Situations

| Situation | Additional Requirements |
|-----------|------------------------|
| **Online survey** | Electronic consent (clicking "I agree" constitutes consent); must state that IP addresses will not be recorded |
| **Audio/video recording** | Separate checkbox item: consent to audio/video recording |
| **Minors** | Legal guardian consent + subject assent |
| **Cross-national research** | Comply with local IRB requirements + Taiwan IRB requirements |
| **Indigenous research** | Community consent (tribal consent) + individual informed consent |

### 5.3 Informed Consent Form Template Structure

```
Research Participation Consent Form

1. Research Project Title: [                    ]
2. Principal Investigator: [      ] / Institution: [        ]
3. Research Purpose: [                              ]
4. Research Methods and Procedures:
    You will be invited to [specific description of what the subject will do],
    estimated to take [  ] minutes.
5. Potential Risks or Discomfort: [                        ]
6. Potential Benefits: [                              ]
7. Confidentiality Measures:
    Your data will be processed using codes; research results will only be
    presented in aggregate form, and your personal identity will not be
    disclosed. Data will be destroyed after [X] years.
8. Voluntary Nature of Participation:
    You are free to decide whether to participate in this study and may
    withdraw at any time without any adverse consequences.
9. Contact Information:
    Principal Investigator: [Name] [Phone] [Email]
    IRB Contact: [Institution Name] [Phone] [Email]

□ I have read and understood the above explanation and agree to participate
  in this research.

Subject Signature: __________ Date: __________
Researcher Signature: __________ Date: __________
```

---

## 6. Data De-identification and Privacy Protection

### 6.1 De-identification Strategies

| Strategy | Description | Applicable Scenario |
|----------|-------------|---------------------|
| **Anonymization** | Complete removal of all identifiable information, irreversible | Final data publication |
| **Pseudonymization** | Replace with codes, retain a linkage table | Need to track during research process |
| **Data generalization** | Convert precise values to ranges (e.g., age → age group) | Statistical analysis |
| **Data masking** | Hide partial information (e.g., partially masked email) | Data display |
| **k-anonymity** | Ensure each record is indistinguishable from at least k-1 other records | Dataset release |

### 6.2 Common Privacy Risks in Higher Education Research

- **Small sample identification**: Small departments may allow re-identification through descriptive statistics
- **Cross-referencing**: Combining multiple de-identified datasets may enable re-identification
- **Narrative identification**: Qualitative research quotations may reveal interviewee identity
- **Institutional identification**: Overly specific institutional characteristics may allow institution identification

### 6.3 Recommended Practices

- [ ] Remove direct identifiers (names, student IDs, national ID numbers)
- [ ] Assess indirect identifier risks (department + year + gender combinations may identify individuals)
- [ ] Check qualitative quotations: remove identifiable details
- [ ] Handle institutional names: decide whether to anonymize based on research needs
- [ ] Encrypt data storage with access controls
- [ ] Establish data retention and destruction timeline

---

## Quick Reference: Researcher Self-Check

Before starting research, answer the following questions:

1. [ ] Does my research collect, use, or analyze human-related data?
2. [ ] If yes, is the data completely de-identified and publicly available?
3. [ ] If not, which level of IRB review do I need to apply for?
4. [ ] Have I completed research ethics training (CITI or equivalent)?
5. [ ] Does my informed consent form include all required elements?
6. [ ] Do I have an appropriate data protection plan?
7. [ ] If vulnerable populations are involved, are there additional protective measures?
8. [ ] Has the IRB review timeline been incorporated into the research project timeline?
