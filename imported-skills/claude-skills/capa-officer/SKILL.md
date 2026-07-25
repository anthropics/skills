---
name: "capa-officer"
description: CAPA system management for medical device QMS. Covers root cause analysis, corrective action planning, effectiveness verification, and CAPA metrics. Use when running CAPA investigations, 5-Why analysis, fishbone diagrams, root cause determination, corrective action tracking, effectiveness verification, or CAPA program optimization.
triggers:
  - CAPA investigation
  - root cause analysis
  - 5 Why analysis
  - fishbone diagram
  - corrective action
  - preventive action
  - effectiveness verification
  - CAPA metrics
  - nonconformance investigation
  - quality issue investigation
  - CAPA tracking
  - audit finding CAPA
---

# CAPA Officer

Corrective and Preventive Action (CAPA) management within Quality Management Systems, focusing on systematic root cause analysis, action implementation, and effectiveness verification.

---

## Table of Contents

- [CAPA Investigation Workflow](#capa-investigation-workflow)
- [Root Cause Analysis](#root-cause-analysis)
- [Corrective Action Planning](#corrective-action-planning)
- [Effectiveness Verification](#effectiveness-verification)
- [CAPA Metrics and Reporting](#capa-metrics-and-reporting)
- [Reference Documentation](#reference-documentation)
- [Tools](#tools)

---

## CAPA Investigation Workflow

Conduct systematic CAPA investigation from initiation through closure:

1. Document trigger event with objective evidence
2. Assess significance and determine CAPA necessity
3. Form investigation team with relevant expertise
4. Collect data and evidence systematically
5. Select and apply appropriate RCA methodology
6. Identify root cause(s) with supporting evidence
7. Develop corrective and preventive actions
8. **Validation:** Root cause explains all symptoms; if eliminated, problem would not recur

### CAPA Necessity Determination

| Trigger Type | CAPA Required | Criteria |
|--------------|---------------|----------|
| Customer complaint (safety) | Yes | Any complaint involving patient/user safety |
| Customer complaint (quality) | Evaluate | Based on severity and frequency |
| Internal audit finding (Major) | Yes | Systematic failure or absence of element |
| Internal audit finding (Minor) | Recommended | Isolated lapse or partial implementation |
| Nonconformance (recurring) | Yes | Same NC type occurring 3+ times |
| Nonconformance (isolated) | Evaluate | Based on severity and risk |
| External audit finding | Yes | All Major and Minor findings |
| Trend analysis | Evaluate | Based on trend significance |

### Investigation Team Composition

| CAPA Severity | Required Team Members |
|---------------|----------------------|
| Critical | CAPA Officer, Process Owner, QA Manager, Subject Matter Expert, Management Rep |
| Major | CAPA Officer, Process Owner, Subject Matter Expert |
| Minor | CAPA Officer, Process Owner |

### Evidence Collection Checklist

- [ ] Problem description with specific details (what, where, when, who, how much)
- [ ] Timeline of events leading to issue
- [ ] Relevant records and documentation
- [ ] Interview notes from involved personnel
- [ ] Photos or physical evidence (if applicable)
- [ ] Related complaints, NCs, or previous CAPAs
- [ ] Process parameters and specifications

---

## Root Cause Analysis

Select and apply appropriate RCA methodology based on problem characteristics.

### RCA Method Selection Decision Tree

```
Is the issue safety-critical or involves system reliability?
├── Yes → Use FAULT TREE ANALYSIS
└── No → Is human error the suspected primary cause?
    ├── Yes → Use HUMAN FACTORS ANALYSIS
    └── No → How many potential contributing factors?
        ├── 1-2 factors (linear causation) → Use 5 WHY ANALYSIS
        ├── 3-6 factors (complex, systemic) → Use FISHBONE DIAGRAM
        └── Unknown/proactive assessment → Use FMEA
```

### 5 Why Analysis

Use when: Single-cause issues with linear causation, process deviations with clear failure point.

**Template:**

```
PROBLEM: [Clear, specific statement]

WHY 1: Why did [problem] occur?
BECAUSE: [First-level cause]
EVIDENCE: [Supporting data]

WHY 2: Why did [first-level cause] occur?
BECAUSE: [Second-level cause]
EVIDENCE: [Supporting data]

WHY 3: Why did [second-level cause] occur?
BECAUSE: [Third-level cause]
EVIDENCE: [Supporting data]

WHY 4: Why did [third-level cause] occur?
BECAUSE: [Fourth-level cause]
EVIDENCE: [Supporting data]

WHY 5: Why did [fourth-level cause] occur?
BECAUSE: [Root cause]
EVIDENCE: [Supporting data]
```

**Example - Calibration Overdue:**

```
PROBLEM: pH meter (EQ-042) found 2 months overdue for calibration

WHY 1: Why was calibration overdue?
BECAUSE: Equipment was not on calibration schedule
EVIDENCE: Calibration schedule reviewed, EQ-042 not listed

WHY 2: Why was it not on the schedule?
BECAUSE: Schedule not updated when equipment was purchased
EVIDENCE: Purchase date 2023-06-15, schedule dated 2023-01-01

WHY 3: Why was the schedule not updated?
BECAUSE: No process requires schedule update at equipment purchase
EVIDENCE: SOP-EQ-001 reviewed, no such requirement

WHY 4: Why is there no such requirement?
BECAUSE: Procedure written before equipment tracking was centralized
EVIDENCE: SOP last revised 2019, equipment system implemented 2021

WHY 5: Why has procedure not been updated?
BECAUSE: Periodic review did not assess compatibility with new systems
EVIDENCE: No review against new equipment system documented

ROOT CAUSE: Procedure review process does not assess compatibility
with organizational systems implemented after original procedure creation.
```

### Fishbone Diagram Categories (6M)

| Category | Focus Areas | Typical Causes |
|----------|-------------|----------------|
| Man (People) | Training, competency, workload | Skill gaps, fatigue, communication |
| Machine (Equipment) | Calibration, maintenance, age | Wear, malfunction, inadequate capacity |
| Method (Process) | Procedures, work instructions | Unclear steps, missing controls |
| Material | Specifications, suppliers, storage | Out-of-spec, degradation, contamination |
| Measurement | Calibration, methods, interpretation | Instrument error, wrong method |
| Mother Nature | Temperature, humidity, cleanliness | Environmental excursions |

See `references/rca-methodologies.md` for complete method details and templates.

### Root Cause Validation

Before proceeding to action planning, validate root cause:

- [ ] Root cause can be verified with objective evidence
- [ ] If root cause is eliminated, problem would not recur
- [ ] Root cause is within organizational control
- [ ] Root cause explains all observed symptoms
- [ ] No other significant causes remain unaddressed

---

## Corrective Action Planning

Develop effective actions addressing identified root causes:

1. Define immediate containment actions
2. Develop corrective actions targeting root cause
3. Identify preventive actions for similar processes
4. Assign responsibilities and resources
5. Establish timeline with milestones
6. Define success criteria and verification method
7. Document in CAPA action plan
8. **Validation:** Actions directly address root cause; success criteria are measurable

### Action Types

| Type | Purpose | Timeline | Example |
|------|---------|----------|---------|
| Containment | Stop immediate impact | 24-72 hours | Quarantine affected product |
| Correction | Fix the specific occurrence | 1-2 weeks | Rework or replace affected items |
| Corrective | Eliminate root cause | 30-90 days | Revise procedure, add controls |
| Preventive | Prevent in other areas | 60-120 days | Extend solution to similar processes |

### Action Plan Components

```
ACTION PLAN TEMPLATE

CAPA Number: [CAPA-XXXX]
Root Cause: [Identified root cause]

ACTION 1: [Specific action description]
- Type: [ ] Containment [ ] Correction [ ] Corrective [ ] Preventive
- Responsible: [Name, Title]
- Due Date: [YYYY-MM-DD]
- Resources: [Required resources]
- Success Criteria: [Measurable outcome]
- Verification Method: [How success will be verified]

ACTION 2: [Specific action description]
...

IMPLEMENTATION TIMELINE:
Week 1: [Milestone]
Week 2: [Milestone]
Week 4: [Milestone]
Week 8: [Milestone]

APPROVAL:
CAPA Owner: _____________ Date: _______
Process Owner: _____________ Date: _______
QA Manager: _____________ Date: _______
```

### Action Effectiveness Indicators

| Indicator | Target | Red Flag |
|-----------|--------|----------|
| Action scope | Addresses root cause completely | Treats only symptoms |
| Specificity | Measurable deliverables | Vague commitments |
| Timeline | Aggressive but achievable | No due dates or unrealistic |
| Resources | Identified and allocated | Not specified |
| Sustainability | Permanent solution | Temporary fix |

---

## Effectiveness Verification

Verify corrective actions achieved intended results:

1. Allow adequate implementation period (minimum 30-90 days)
2. Collect post-implementation data
3. Compare to pre-implementation baseline
4. Evaluate against success criteria
5. Verify no recurrence during verification period
6. Document verification evidence
7. Determine CAPA effectiveness
8. **Validation:** All criteria met with objective evidence; no recurrence observed

### Verification Timeline Guidelines

| CAPA Severity | Wait Period | Verification Window |
|---------------|-------------|---------------------|
| Critical | 30 days | 30-90 days post-implementation |
| Major | 60 days | 60-180 days post-implementation |
| Minor | 90 days | 90-365 days post-implementation |

### Verification Methods

| Method | Use When | Evidence Required |
|--------|----------|-------------------|
| Data trend analysis | Quantifiable issues | Pre/post comparison, trend charts |
| Process audit | Procedure compliance issues | Audit checklist, interview notes |
| Record review | Documentation issues | Sample records, compliance rate |
| Testing/inspection | Product quality issues | Test results, pass/fail data |
| Interview/observation | Training issues | Interview notes, observation records |

### Effectiveness Determination

```
Did recurrence occur during verification period?
├── Yes → CAPA INEFFECTIVE (re-investigate root cause)
└── No → Were all effectiveness criteria met?
    ├── Yes → CAPA EFFECTIVE (proceed to closure)
    └── No → Extent of gap?
        ├── Minor gap → Extend verification or accept with justification
        └── Significant gap → CAPA INEFFECTIVE (revise actions)
```

See `references/effectiveness-verification-guide.md` for detailed procedures.

---

## CAPA Metrics and Reporting

Monitor CAPA program performance through key indicators.

### Key Performance Indicators

| Metric | Target | Calculation |
|--------|--------|-------------|
| CAPA cycle time | <60 days average | (Close Date - Open Date) / Number of CAPAs |
| Overdue rate | <10% | Overdue CAPAs / Total Open CAPAs |
| First-time effectiveness | >90% | Effective on first verification / Total verified |
| Recurrence rate | <5% | Recurred issues / Total closed CAPAs |
| Investigation quality | 100% root cause validated | Root causes validated / Total CAPAs |

### Aging Analysis Categories

| Age Bucket | Status | Action Required |
|------------|--------|-----------------|
| 0-30 days | On track | Monitor progress |
| 31-60 days | Monitor | Review for delays |
| 61-90 days | Warning | Escalate to management |
| >90 days | Critical | Management intervention required |

### Management Review Inputs

Monthly CAPA status report includes:
- Open CAPA count by severity and status
- Overdue CAPA list with owners
- Cycle time trends
- Effectiveness rate trends
- Source analysis (complaints, audits, NCs)
- Recommendations for improvement

---

## Reference Documentation

### Root Cause Analysis Methodologies

`references/rca-methodologies.md` contains:

- Method selection decision tree
- 5 Why analysis template and example
- Fishbone diagram categories and template
- Fault Tree Analysis for safety-critical issues
- Human Factors Analysis for people-related causes
- FMEA for proactive risk assessment
- Hybrid approach guidance

### Effectiveness Verification Guide

`references/effectiveness-verification-guide.md` contains:

- Verification planning requirements
- Verification method selection
- Effectiveness criteria definition (SMART)
- Closure requirements by severity
- Ineffective CAPA process
- Documentation templates

---

## Tools

### CAPA Tracker

```bash
# Generate CAPA status report
python scripts/capa_tracker.py --capas capas.json

# Interactive mode for manual entry
python scripts/capa_tracker.py --interactive

# JSON output for integration
python scripts/capa_tracker.py --capas capas.json --output json

# Generate sample data file
python scripts/capa_tracker.py --sample > sample_capas.json
```

Calculates and reports:
- Summary metrics (open, closed, overdue, cycle time, effectiveness)
- Status distribution
- Severity and source analysis
- Aging report by time bucket
- Overdue CAPA list
- Actionable recommendations

### Sample CAPA Input

```json
{
  "capas": [
    {
      "capa_number": "CAPA-2024-001",
      "title": "Calibration overdue for pH meter",
      "description": "pH meter EQ-042 found 2 months overdue",
      "source": "AUDIT",
      "severity": "MAJOR",
      "status": "VERIFICATION",
      "open_date": "2024-06-15",
      "target_date": "2024-08-15",
      "owner": "J. Smith",
      "root_cause": "Procedure review gap",
      "corrective_action": "Updated SOP-EQ-001"
    }
  ]
}
```

---

## Regulatory Requirements

### ISO 13485:2016 Clause 8.5

| Sub-clause | Requirement | Key Activities |
|------------|-------------|----------------|
| 8.5.2 Corrective Action | Eliminate cause of nonconformity | NC review, cause determination, action evaluation, implementation, effectiveness review |
| 8.5.3 Preventive Action | Eliminate potential nonconformity | Trend analysis, cause determination, action evaluation, implementation, effectiveness review |

### FDA CAPA authority — ISO 13485 §8.5.2/8.5.3 under the QMSR (legacy QSR 820.100, historical)

> **⚠️ STATUS — QMSR transition (effective 2026-02-02):** FDA's Quality Management System Regulation (QMSR) final rule (89 FR 7496) amended 21 CFR Part 820 to **incorporate ISO 13485:2016 by reference** and removed the legacy QSR subsection structure. The CAPA section number **820.100 no longer exists in the CFR** — it is retained below only as a familiar index. The current FDA authority for CAPA is **ISO 13485:2016 §8.5.2 (corrective action) and §8.5.3 (preventive action)** (see clause table above), with complaint-handling additions in retained **21 CFR 820.35**. Cite the ISO 13485 clauses — not 820.100 — in current compliance documentation.

CAPA elements required under ISO 13485 §8.5.2/§8.5.3 (legacy QSR 820.100, historical):
- Procedures for implementing corrective and preventive action
- Analyzing quality data sources (complaints, NCs, audits, service records)
- Investigating cause of nonconformities
- Identifying actions needed to correct and prevent recurrence
- Verifying actions are effective and do not adversely affect device
- Submitting relevant information for management review

### Common FDA 483 Observations

| Observation | Root Cause Pattern |
|-------------|-------------------|
| CAPA not initiated for recurring issue | Trend analysis not performed |
| Root cause analysis superficial | Inadequate investigation training |
| Effectiveness not verified | No verification procedure |
| Actions do not address root cause | Symptom treatment vs. cause elimination |

> **Decision discipline:** The tools in this skill structure investigations and track CAPA status — they do not certify CAPA closure or compliance. CAPA effectiveness conclusions and closure decisions are yours to make and must be reviewed and signed off by the named CAPA owner and Quality function; route regulatory-classification questions (e.g., reportability, 21 CFR 803 MDR, recall under 21 CFR 806) to Regulatory Affairs.
