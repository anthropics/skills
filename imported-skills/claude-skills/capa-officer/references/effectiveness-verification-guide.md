# Effectiveness Verification Guide

CAPA effectiveness assessment procedures, verification methods, and closure criteria.

---

## Table of Contents

- [Verification Planning](#verification-planning)
- [Verification Methods](#verification-methods)
- [Effectiveness Criteria](#effectiveness-criteria)
- [Closure Requirements](#closure-requirements)
- [Ineffective CAPA Process](#ineffective-capa-process)
- [Documentation Templates](#documentation-templates)

---

## Verification Planning

### When to Plan Verification

Verification planning must occur BEFORE corrective action implementation:

| Stage | Planning Activity | Owner |
|-------|-------------------|-------|
| CAPA Initiation | Define preliminary verification approach | CAPA Owner |
| Root Cause Analysis | Refine criteria based on root cause | Investigation Team |
| Action Planning | Finalize verification method and timeline | CAPA Owner |
| Implementation | Schedule verification activities | Quality Assurance |

### Verification Timeline Guidelines

| CAPA Severity | Minimum Wait Period | Verification Window |
|---------------|---------------------|---------------------|
| Critical (Safety) | 30 days | 30-90 days post-implementation |
| Major | 60 days | 60-180 days post-implementation |
| Minor | 90 days | 90-365 days post-implementation |

**Rationale**: Waiting period ensures sufficient data collection and accounts for process variation.

### Verification Plan Components

```
VERIFICATION PLAN TEMPLATE

CAPA Number: [CAPA-XXXX]
Problem Statement: [Original issue]
Root Cause: [Identified root cause]
Corrective Action: [Implemented action]

VERIFICATION METHOD:
[ ] Data Trend Analysis
[ ] Process Audit
[ ] Record Review
[ ] Testing/Inspection
[ ] Interview/Observation
[ ] Multiple Methods (specify)

EFFECTIVENESS CRITERIA:
1. [Measurable criterion 1]
2. [Measurable criterion 2]
3. [Measurable criterion 3]

SUCCESS THRESHOLD:
- [Quantitative threshold, e.g., "Zero recurrence for 90 days"]
- [Qualitative threshold, e.g., "Procedure followed correctly 100%"]

DATA COLLECTION:
- Source: [Where data will come from]
- Sample Size: [Number of records/instances to review]
- Time Period: [Start and end dates]
- Responsible: [Who collects data]

VERIFICATION SCHEDULE:
- Implementation Complete: [Date]
- Waiting Period Ends: [Date]
- Verification Start: [Date]
- Verification Complete: [Date]
- Report Due: [Date]

APPROVAL:
CAPA Owner: _____________ Date: _______
Quality Assurance: _____________ Date: _______
```

---

## Verification Methods

### 1. Data Trend Analysis

**Best for:** Quantifiable issues with measurable outcomes (defect rates, cycle times, complaint trends)

**Procedure:**
1. Collect post-implementation data for defined period
2. Compare to pre-implementation baseline
3. Apply statistical analysis if sample size permits
4. Document trend direction and magnitude

**Example Criteria:**
- Defect rate reduced by ≥50% from baseline
- Zero recurrence of specific failure mode
- Process capability (Cpk) improved to ≥1.33

**Evidence Required:**
- Pre-implementation baseline data
- Post-implementation trend data
- Statistical analysis (if applicable)
- Trend charts with annotation

### 2. Process Audit

**Best for:** Procedure compliance issues, process control failures, systemic problems

**Procedure:**
1. Develop audit checklist based on corrective action
2. Conduct unannounced process audit
3. Interview operators and supervisors
4. Review records generated since implementation
5. Document compliance percentage

**Example Criteria:**
- 100% compliance with revised procedure
- All operators demonstrate competency
- No deviations observed during audit

**Evidence Required:**
- Audit checklist completed
- Interview notes
- Record samples reviewed
- Photos/observations (if applicable)

### 3. Record Review

**Best for:** Documentation issues, completeness problems, traceability failures

**Procedure:**
1. Define sample size based on volume (minimum 10 or 10%, whichever greater)
2. Review records generated post-implementation
3. Evaluate against specified requirements
4. Calculate compliance rate

**Example Criteria:**
- 100% of records meet completeness requirements
- All required signatures present
- Traceability maintained throughout

**Evidence Required:**
- List of records reviewed
- Compliance checklist results
- Non-compliance summary (if any)

### 4. Testing/Inspection

**Best for:** Product quality issues, equipment failures, specification non-conformances

**Procedure:**
1. Define test protocol based on corrective action
2. Conduct testing on post-implementation units
3. Compare results to acceptance criteria
4. Document pass/fail rates

**Example Criteria:**
- 100% of units pass revised inspection criteria
- All test results within specification
- Zero failures of targeted parameter

**Evidence Required:**
- Test protocol/method
- Test results data
- Pass/fail summary
- Comparison to pre-implementation results

### 5. Interview/Observation

**Best for:** Training issues, communication problems, human factors causes

**Procedure:**
1. Develop structured interview questions
2. Interview representative sample of affected personnel
3. Observe process execution in real-time
4. Document responses and observations

**Example Criteria:**
- All interviewed personnel demonstrate knowledge
- Observed practices match documented procedure
- No unsafe acts or workarounds observed

**Evidence Required:**
- Interview questions and responses
- Observation notes
- Training records (supporting)

---

## Effectiveness Criteria

### Defining Good Criteria

Criteria must be **SMART**:

| Element | Requirement | Example |
|---------|-------------|---------|
| **S**pecific | Clearly defined what to measure | "Calibration overdue rate" not "equipment issues" |
| **M**easurable | Quantifiable or objectively verifiable | "<2% overdue rate" not "improved timeliness" |
| **A**chievable | Realistic given the corrective action | Within capability of implemented solution |
| **R**elevant | Directly related to root cause | Addresses the actual problem |
| **T**ime-bound | Specified evaluation period | "For 90 consecutive days" |

### Criteria by Issue Type

| Issue Type | Typical Criteria | Threshold |
|------------|------------------|-----------|
| Nonconformance | Recurrence rate | Zero recurrence |
| Process deviation | Compliance rate | ≥95% compliance |
| Complaint | Complaint trend | ≥50% reduction |
| Calibration | Overdue rate | <2% overdue |
| Training | Competency pass rate | 100% pass |
| Documentation | Completeness rate | 100% complete |
| Supplier | Incoming reject rate | ≤1% reject rate |

### Sample Size Guidelines

| Population Size | Minimum Sample |
|-----------------|----------------|
| <10 | All (100%) |
| 10-50 | 10 |
| 51-100 | 15 |
| 101-500 | 20 |
| >500 | 25 or 10%, whichever less |

---

## Closure Requirements

### Closure Checklist

**CAPA Closure Prerequisites:**

- [ ] All corrective actions implemented
- [ ] Implementation evidence documented
- [ ] Verification waiting period complete
- [ ] Verification activities performed
- [ ] All effectiveness criteria met
- [ ] Verification evidence documented
- [ ] No recurrence during verification period
- [ ] CAPA owner review complete
- [ ] Quality Assurance review complete
- [ ] Documentation complete and filed

### Effectiveness Status Determination

```
EFFECTIVENESS DECISION TREE:

Did recurrence occur during verification period?
├── Yes → CAPA INEFFECTIVE (escalate per ineffective process)
└── No → Were all effectiveness criteria met?
    ├── Yes → Were any related issues identified?
    │   ├── Yes → Open new CAPA if needed, close original
    │   └── No → CAPA EFFECTIVE - proceed to closure
    └── No → How many criteria missed?
        ├── Minor gap (1 criterion, marginal miss) →
        │   Extend verification period OR accept with justification
        └── Significant gap → CAPA INEFFECTIVE

EFFECTIVENESS DETERMINATION:
[ ] EFFECTIVE - All criteria met, no recurrence
[ ] EFFECTIVE WITH CONDITIONS - Minor gap, justified acceptance
[ ] INEFFECTIVE - Significant gaps or recurrence
```

### Closure Documentation

```
EFFECTIVENESS VERIFICATION REPORT

CAPA Number: [CAPA-XXXX]
Verification Complete Date: [Date]
Verified By: [Name, Title]

VERIFICATION SUMMARY:
| Criterion | Target | Actual | Status |
|-----------|--------|--------|--------|
| [Criterion 1] | [Target] | [Result] | ☑ Met / ☐ Not Met |
| [Criterion 2] | [Target] | [Result] | ☑ Met / ☐ Not Met |
| [Criterion 3] | [Target] | [Result] | ☑ Met / ☐ Not Met |

RECURRENCE CHECK:
- Recurrence during verification period: [ ] Yes  [ ] No
- Related issues identified: [ ] Yes  [ ] No
- If yes, describe: [Description]

EVIDENCE SUMMARY:
[List of evidence documents, record numbers, data sources]

EFFECTIVENESS DETERMINATION:
[ ] EFFECTIVE
[ ] EFFECTIVE WITH CONDITIONS: [Justification]
[ ] INEFFECTIVE: [Reason]

RECOMMENDED ACTION:
[ ] Close CAPA
[ ] Extend verification period to [Date]
[ ] Open new CAPA [CAPA-XXXX] for [Issue]
[ ] Re-investigate (return to root cause analysis)

APPROVALS:
CAPA Owner: _____________ Date: _______
Quality Assurance: _____________ Date: _______
Management (if Major/Critical): _____________ Date: _______
```

---

## Ineffective CAPA Process

### Definition of Ineffective

CAPA is ineffective when:
1. Original problem recurs during or after verification period
2. Effectiveness criteria not met
3. Root cause still present
4. Corrective action created new problems

### Ineffective CAPA Workflow

```
INEFFECTIVE CAPA DETECTED
    │
    ├── 1. Immediate Actions
    │   ├── Reopen CAPA (do not close as effective)
    │   ├── Implement containment for recurrence
    │   └── Notify CAPA owner and management
    │
    ├── 2. Root Cause Re-evaluation
    │   ├── Was original root cause correct?
    │   │   ├── No → Conduct new root cause analysis
    │   │   └── Yes → Was corrective action appropriate?
    │   │       ├── No → Develop new corrective action
    │   │       └── Yes → Was implementation adequate?
    │   │           ├── No → Re-implement with improvements
    │   │           └── Yes → Escalate (systemic issue)
    │
    ├── 3. Escalation Criteria
    │   ├── Second ineffective attempt → Management review required
    │   ├── Safety-related recurrence → Immediate escalation
    │   └── Pattern across multiple CAPAs → Systemic CAPA
    │
    └── 4. Documentation
        ├── Document ineffective status with evidence
        ├── Record re-investigation results
        ├── Update CAPA metrics/trending
        └── Include in management review
```

### Preventing Ineffective CAPAs

| Common Cause | Prevention |
|--------------|------------|
| Superficial root cause | Validate root cause before action |
| Action addresses symptom not cause | Ensure action targets root cause |
| Implementation incomplete | Verify implementation before verification |
| Insufficient verification period | Allow adequate time for data collection |
| Wrong verification method | Match method to issue type |
| Unclear success criteria | Define SMART criteria upfront |

---

## Documentation Templates

### Verification Evidence Log

```
VERIFICATION EVIDENCE LOG

CAPA Number: [CAPA-XXXX]

| Doc/Record # | Description | Date | Reviewed By | Finding |
|--------------|-------------|------|-------------|---------|
| [Number] | [Description] | [Date] | [Reviewer] | [Compliant/Finding] |
| [Number] | [Description] | [Date] | [Reviewer] | [Compliant/Finding] |

SUMMARY:
- Total records reviewed: [Number]
- Compliant: [Number] ([Percentage]%)
- Non-compliant: [Number] ([Percentage]%)

CONCLUSION:
[Statement on whether evidence supports effectiveness]
```

### Trend Analysis Summary

```
TREND ANALYSIS FOR CAPA VERIFICATION

CAPA Number: [CAPA-XXXX]
Metric: [What is being measured]

BASELINE (Pre-Implementation):
- Period: [Start] to [End]
- Value: [Baseline value]
- Data points: [Number]

POST-IMPLEMENTATION:
- Period: [Start] to [End]
- Value: [Current value]
- Data points: [Number]

CHANGE:
- Absolute change: [Value]
- Percentage change: [Percentage]%
- Target: [Target value/change]
- Status: [ ] Met  [ ] Not Met

TREND CHART:
[Include or reference trend chart showing before/after comparison]

STATISTICAL SIGNIFICANCE (if applicable):
- Method: [t-test, chi-square, etc.]
- p-value: [Value]
- Conclusion: [Statistically significant / Not significant]
```

### Interview Summary Template

```
VERIFICATION INTERVIEW SUMMARY

CAPA Number: [CAPA-XXXX]
Interviewer: [Name]
Date: [Date]

INTERVIEWEE:
- Name: [Name]
- Role: [Job title]
- Department: [Department]
- Experience: [Years in role]

QUESTIONS AND RESPONSES:

Q1: [Question about awareness of change]
A1: [Response summary]
Knowledge demonstrated: [ ] Yes  [ ] Partial  [ ] No

Q2: [Question about implementation of change]
A2: [Response summary]
Compliance demonstrated: [ ] Yes  [ ] Partial  [ ] No

Q3: [Question about understanding rationale]
A3: [Response summary]
Understanding demonstrated: [ ] Yes  [ ] Partial  [ ] No

OBSERVATION NOTES:
[Any relevant observations during interview]

CONCLUSION:
[ ] Interviewee demonstrates full knowledge and compliance
[ ] Interviewee demonstrates partial knowledge (specify gaps)
[ ] Interviewee does not demonstrate required knowledge
```
