# Nonconformity Classification

Severity classification, CAPA integration, and finding documentation guidance.

---

## Table of Contents

- [Classification Criteria](#classification-criteria)
- [Severity Matrix](#severity-matrix)
- [CAPA Integration](#capa-integration)
- [Finding Documentation](#finding-documentation)
- [Closure Requirements](#closure-requirements)

---

## Classification Criteria

### Nonconformity Definitions

| Category | Definition | Examples |
|----------|------------|----------|
| Major NC | Systematic failure or absence of required element | No design control procedure, no CAPA system |
| Minor NC | Isolated lapse or partial implementation | Single missing signature, one overdue calibration |
| Observation | Improvement opportunity, potential future NC | Trending toward noncompliance, unclear procedure |

### Classification Decision Tree

```
Is required element absent or failed?
├── Yes → Is failure systematic (multiple instances)?
│   ├── Yes → MAJOR NONCONFORMITY
│   └── No → Could it cause product safety issue?
│       ├── Yes → MAJOR NONCONFORMITY
│       └── No → MINOR NONCONFORMITY
└── No → Is there deviation from procedure?
    ├── Yes → Isolated or recurring?
    │   ├── Isolated → MINOR NONCONFORMITY
    │   └── Recurring → MAJOR NONCONFORMITY
    └── No → Is there improvement opportunity?
        ├── Yes → OBSERVATION
        └── No → NO FINDING
```

---

## Severity Matrix

### Impact vs. Occurrence Matrix

| | Low Occurrence (1 instance) | Medium (2-3 instances) | High (Systematic) |
|---|---|---|---|
| **High Impact** (Safety/Efficacy) | Major | Major | Major |
| **Medium Impact** (Quality/Compliance) | Minor | Major | Major |
| **Low Impact** (Administrative) | Observation | Minor | Minor |

### Clause-Specific Severity Guidance

| Clause | Major If... | Minor If... |
|--------|-------------|-------------|
| 4.2 Document Control | No document control system | Single obsolete document in use |
| 5.6 Management Review | Not conducted >12 months | Missing single input |
| 6.2 Training | No competency defined | Single training record missing |
| 7.3 Design Control | No design reviews | Review participant missing |
| 7.4 Purchasing | No supplier evaluation | Single evaluation overdue |
| 7.5 Production | Special process not validated | Minor deviation from WI |
| 8.2.2 Internal Audit | No audit program | Audit overdue <90 days |
| 8.5 CAPA | No CAPA system | Effectiveness not verified |

---

## CAPA Integration

### Finding-to-CAPA Workflow

1. **Classify finding** (Major/Minor/Observation)
2. **Document finding** with objective evidence
3. **Determine CAPA requirement** (see table below)
4. **Initiate CAPA** with finding as source
5. **Track resolution** through closure
6. **Verify effectiveness** at follow-up audit
7. **Validation:** Finding closed only after CAPA effective

### CAPA Requirement by Severity

| Severity | CAPA Required | Timeline | Verification |
|----------|---------------|----------|--------------|
| Major | Yes | 30 days for root cause, 90 days for implementation | Next audit or within 6 months |
| Minor | Recommended | 60 days for correction | Next scheduled audit |
| Observation | Optional | As appropriate | Noted at next audit |

### Root Cause Depth by Severity

| Severity | Root Cause Analysis Required |
|----------|------------------------------|
| Major | Full 5-Why or Fishbone, systemic causes |
| Minor | Immediate cause identification |
| Observation | Not required |

---

## Finding Documentation

### Finding Statement Structure

```
FINDING STATEMENT TEMPLATE:

Requirement: [Specific clause or procedure requirement]
Evidence: [What was observed, reviewed, or heard]
Gap: [How the evidence fails to meet the requirement]

Example:
Requirement: ISO 13485:2016 Clause 8.2.2 requires internal audits
at planned intervals to determine QMS conformity.

Evidence: Audit schedule shows Design Control audit planned for
Q2 2024. No audit records exist. Interview with QA Manager
confirmed audit was not conducted.

Gap: Internal audit for Design Control process not conducted as
planned, representing a gap in audit program execution.
```

### Evidence Types and Requirements

| Evidence Type | How to Document | Retention |
|---------------|-----------------|-----------|
| Document | Reference document number, version, date | Copy in audit file |
| Interview | Interviewee name, role, statement summary | Notes in audit file |
| Observation | What, where, when observed | Photo if appropriate |
| Record | Record identifier, date, content observed | Copy in audit file |

### Finding Writing Guidelines

**Do:**
- State objective evidence clearly
- Reference specific requirements
- Use factual, neutral language
- Include document/record identifiers

**Don't:**
- Use judgmental language ("poor", "inadequate")
- Generalize without evidence ("always", "never")
- Combine multiple findings
- Include corrective action suggestions

---

## Closure Requirements

### Closure Criteria by Severity

**Major Nonconformity:**
- [ ] Root cause analysis completed
- [ ] Corrective action implemented
- [ ] Effectiveness verified (objective evidence)
- [ ] No recurrence observed
- [ ] QA Manager sign-off
- [ ] Auditor verification

**Minor Nonconformity:**
- [ ] Immediate correction completed
- [ ] Root cause addressed (if applicable)
- [ ] Evidence of correction reviewed
- [ ] QA Manager sign-off

**Observation:**
- [ ] Action taken (if any) documented
- [ ] Noted for future reference

### Verification Methods

| Method | When to Use |
|--------|-------------|
| Record review | Correction documented in records |
| Interview | Process change understood by personnel |
| Observation | Physical correction verified |
| Follow-up audit | Systematic correction verified over time |

### Closure Documentation

```
CLOSURE RECORD TEMPLATE:

Finding ID: [NC-YYYY-XXX]
Original Finding: [Brief description]
Severity: [Major/Minor/Observation]

Corrective Action Taken:
[Description of action implemented]

Evidence of Implementation:
[Document numbers, dates, observations]

Effectiveness Verification:
[Method used, results, date]

Closure Approved By: [Name, Role, Date]
```

---

## Audit Finding Log

### Log Template

| ID | Date | Clause | Finding | Severity | Status | Due Date | Closed Date |
|----|------|--------|---------|----------|--------|----------|-------------|
| NC-2024-001 | | | | | | | |
| NC-2024-002 | | | | | | | |

### Status Definitions

| Status | Definition |
|--------|------------|
| Open | Finding documented, CAPA not started |
| In Progress | CAPA underway |
| Pending Verification | Action complete, awaiting verification |
| Closed | Effectiveness verified |
| Escalated | Overdue or ineffective, requires management attention |
