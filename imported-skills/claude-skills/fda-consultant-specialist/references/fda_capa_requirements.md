# FDA CAPA Requirements

Complete guide to Corrective and Preventive Action requirements per 21 CFR 820.100.

---

## Table of Contents

- [CAPA Regulation Overview](#capa-regulation-overview)
- [CAPA Sources](#capa-sources)
- [CAPA Process](#capa-process)
- [Root Cause Analysis](#root-cause-analysis)
- [Action Implementation](#action-implementation)
- [Effectiveness Verification](#effectiveness-verification)
- [Documentation Requirements](#documentation-requirements)
- [FDA Inspection Focus Areas](#fda-inspection-focus-areas)

---

## CAPA Regulation Overview

### 21 CFR 820.100 Requirements

```
§820.100 Corrective and preventive action

(a) Each manufacturer shall establish and maintain procedures for
implementing corrective and preventive action. The procedures shall
include requirements for:

(1) Analyzing processes, work operations, concessions, quality audit
    reports, quality records, service records, complaints, returned
    product, and other sources of quality data to identify existing
    and potential causes of nonconforming product, or other quality
    problems.

(2) Investigating the cause of nonconformities relating to product,
    processes, and the quality system.

(3) Identifying the action(s) needed to correct and prevent recurrence
    of nonconforming product and other quality problems.

(4) Verifying or validating the corrective and preventive action to
    ensure that such action is effective and does not adversely affect
    the finished device.

(5) Implementing and recording changes in methods and procedures needed
    to correct and prevent identified quality problems.

(6) Ensuring that information related to quality problems or nonconforming
    product is disseminated to those directly responsible for assuring
    the quality of such product or the prevention of such problems.

(7) Submitting relevant information on identified quality problems, as
    well as corrective and preventive actions, for management review.
```

### Definitions

| Term | Definition |
|------|------------|
| **Correction** | Action to eliminate a detected nonconformity |
| **Corrective Action** | Action to eliminate the cause of a detected nonconformity to prevent recurrence |
| **Preventive Action** | Action to eliminate the cause of a potential nonconformity to prevent occurrence |
| **Root Cause** | The fundamental reason for the occurrence of a problem |
| **Effectiveness** | Confirmation that actions achieved intended results |

### CAPA vs. Correction

```
Problem Detected
    ├── Correction (Immediate)
    │   └── Fix the immediate issue
    │       Example: Replace defective part
    │
    └── CAPA (Systemic)
        └── Address root cause
            Example: Fix process that caused defect
```

---

## CAPA Sources

### Data Sources for CAPA Input

**Internal Sources:**
- Nonconforming product reports (NCRs)
- Internal audit findings
- Process deviations
- Manufacturing data trends
- Equipment failures
- Employee observations
- Training deficiencies

**External Sources:**
- Customer complaints
- Service records
- Returned product
- Regulatory feedback (483s, warning letters)
- Adverse event reports (MDRs)
- Field safety corrective actions

### CAPA Threshold Criteria

**Mandatory CAPA Triggers:**

| Source | Threshold |
|--------|-----------|
| Audit findings | All major/critical findings |
| Customer complaints | Any safety-related |
| NCRs | Recurring (3+ occurrences) |
| Regulatory feedback | All observations |
| MDR/vigilance | All reportable events |

**Discretionary CAPA Evaluation:**

| Source | Consideration |
|--------|---------------|
| Trend data | Statistical significance |
| Process deviations | Impact assessment |
| Minor audit findings | Risk-based |
| Supplier issues | Frequency and severity |

### Trend Analysis

**Statistical Process Control:**

```markdown
## Monthly CAPA Trend Review

### Complaint Trending
- [ ] Complaints by product
- [ ] Complaints by failure mode
- [ ] Geographic distribution
- [ ] Customer type analysis

### NCR Trending
- [ ] NCRs by product/process
- [ ] NCRs by cause code
- [ ] NCRs by supplier
- [ ] Scrap/rework rates

### Threshold Monitoring
| Metric | Threshold | Current | Status |
|--------|-----------|---------|--------|
| Complaints/month | <10 | | |
| NCR rate | <2% | | |
| Recurring issues | 0 | | |
```

---

## CAPA Process

### CAPA Workflow

```
1. Initiation
   ├── Problem identification
   ├── Initial assessment
   └── CAPA determination

2. Investigation
   ├── Data collection
   ├── Root cause analysis
   └── Impact assessment

3. Action Planning
   ├── Correction (if applicable)
   ├── Corrective action
   └── Preventive action

4. Implementation
   ├── Execute actions
   ├── Document changes
   └── Train affected personnel

5. Verification
   ├── Verify implementation
   ├── Validate effectiveness
   └── Monitor for recurrence

6. Closure
   ├── Management approval
   ├── Final documentation
   └── Trend data update
```

### CAPA Form Template

```markdown
## CAPA Record

### Section 1: Identification
CAPA Number: ________________
Initiated By: ________________
Date Initiated: ______________
Priority: ☐ Critical ☐ Major ☐ Minor

Source:
☐ Audit Finding     ☐ Complaint        ☐ NCR
☐ Service Record    ☐ MDR              ☐ Trend Data
☐ Regulatory        ☐ Other: ____________

### Section 2: Problem Description
Products Affected: _______________________
Processes Affected: _____________________
Quantity/Scope: _________________________

Problem Statement:
[Clear, specific description of the nonconformity or potential problem]

### Section 3: Immediate Correction
Correction Taken: _______________________
Date Completed: _________________________
Verified By: ____________________________

### Section 4: Investigation
Investigation Lead: _____________________
Investigation Start Date: _______________

Data Collected:
☐ Complaint records      ☐ Production records
☐ Test data              ☐ Training records
☐ Process documentation  ☐ Supplier data

Root Cause Analysis Method:
☐ 5 Whys    ☐ Fishbone    ☐ Fault Tree    ☐ Other

Root Cause Statement:
[Specific, factual statement of the root cause]

Contributing Factors:
1. _____________________________________
2. _____________________________________

### Section 5: Action Plan

#### Corrective Actions
| Action | Owner | Target Date | Status |
|--------|-------|-------------|--------|
|        |       |             |        |

#### Preventive Actions
| Action | Owner | Target Date | Status |
|--------|-------|-------------|--------|
|        |       |             |        |

### Section 6: Verification
Verification Method: ____________________
Verification Criteria: __________________
Verification Date: _____________________
Verified By: ___________________________

Verification Results:
☐ Actions implemented as planned
☐ No adverse effects identified
☐ Documentation updated

### Section 7: Effectiveness Review
Effectiveness Review Date: ______________
Review Period: ________________________
Reviewer: _____________________________

Effectiveness Criteria:
[Specific, measurable criteria for success]

Results:
☐ Effective - problem has not recurred
☐ Not Effective - additional action required

Evidence:
[Reference to data showing effectiveness]

### Section 8: Closure
Closure Date: _________________________
Approved By: __________________________

Management Review Submitted: ☐ Yes ☐ No
Date: ________________________________
```

---

## Root Cause Analysis

### 5 Whys Technique

**Example: Device Fails Final Test**

```
Problem: 5% of devices fail functional test at final inspection

Why 1: Component X is out of tolerance
Why 2: Component X was accepted at incoming inspection
Why 3: Incoming inspection sampling missed defective lot
Why 4: Sampling plan inadequate for component criticality
Why 5: Risk classification of component not updated after design change

Root Cause: Risk classification process did not include design change trigger
```

**5 Whys Template:**

```markdown
## 5 Whys Analysis

Problem Statement: _________________________________

Why 1: _____________________________________________
Evidence: __________________________________________

Why 2: _____________________________________________
Evidence: __________________________________________

Why 3: _____________________________________________
Evidence: __________________________________________

Why 4: _____________________________________________
Evidence: __________________________________________

Why 5: _____________________________________________
Evidence: __________________________________________

Root Cause: ________________________________________

Verification: How do we know this is the root cause?
________________________________________________
```

### Fishbone (Ishikawa) Diagram

**Categories for Medical Device Manufacturing:**

```
                    ┌─────────────────────────────────────────┐
                    │              PROBLEM                     │
                    └─────────────────────────────────────────┘
                                       ▲
           ┌───────────────────────────┼───────────────────────────┐
           │                           │                           │
    ┌──────┴──────┐             ┌──────┴──────┐             ┌──────┴──────┐
    │  PERSONNEL  │             │   METHODS   │             │  MATERIALS  │
    │             │             │             │             │             │
    │ • Training  │             │ • SOP gaps  │             │ • Supplier  │
    │ • Skills    │             │ • Process   │             │ • Specs     │
    │ • Attention │             │ • Sequence  │             │ • Storage   │
    └─────────────┘             └─────────────┘             └─────────────┘
           │                           │                           │
           └───────────────────────────┼───────────────────────────┘
                                       │
    ┌──────────────┐            ┌──────┴──────┐            ┌──────────────┐
    │  MEASUREMENT │            │  EQUIPMENT  │            │ ENVIRONMENT  │
    │              │            │             │            │              │
    │ • Calibration│            │ • Maintenance│           │ • Temperature│
    │ • Method     │            │ • Capability │           │ • Humidity   │
    │ • Accuracy   │            │ • Tooling   │            │ • Cleanliness│
    └──────────────┘            └─────────────┘            └──────────────┘
```

### Fault Tree Analysis

**For Complex Failures:**

```
                    Top Event: Device Failure
                              │
              ┌───────────────┼───────────────┐
              │               │               │
           AND/OR          AND/OR          AND/OR
              │               │               │
        ┌─────┴─────┐   ┌─────┴─────┐   ┌─────┴─────┐
        │ Component │   │  Software │   │   User    │
        │  Failure  │   │  Failure  │   │   Error   │
        └─────┬─────┘   └─────┬─────┘   └─────┬─────┘
              │               │               │
         Basic Events    Basic Events    Basic Events
```

### Root Cause Categories

| Category | Examples | Evidence Sources |
|----------|----------|------------------|
| Design | Specification error, tolerance stack-up | DHF, design review records |
| Process | Procedure inadequate, sequence error | Process validation, work instructions |
| Personnel | Training gap, human error | Training records, interviews |
| Equipment | Calibration drift, maintenance | Calibration records, logs |
| Material | Supplier quality, storage | Incoming inspection, COCs |
| Environment | Temperature, contamination | Environmental monitoring |
| Management | Resource allocation, priorities | Management review records |

---

## Action Implementation

### Corrective Action Requirements

**Effective Corrective Actions:**
1. Address identified root cause
2. Are specific and measurable
3. Have assigned ownership
4. Have realistic target dates
5. Consider impact on other processes
6. Include verification method

**Action Types:**

| Type | Description | Example |
|------|-------------|---------|
| Process change | Modify procedure or method | Update SOP with additional step |
| Design change | Modify product design | Add tolerance specification |
| Training | Improve personnel capability | Conduct retraining |
| Equipment | Modify or replace equipment | Upgrade inspection equipment |
| Supplier | Address supplier quality | Audit supplier, add requirements |
| Documentation | Improve or add documentation | Create work instruction |

### Change Control Integration

```
CAPA Action Identified
        │
        ▼
Change Request Initiated
        │
        ▼
Impact Assessment
├── Regulatory impact
├── Product impact
├── Process impact
└── Documentation impact
        │
        ▼
Change Approved
        │
        ▼
Implementation
├── Document updates
├── Training
├── Validation (if required)
└── Effective date
        │
        ▼
CAPA Verification
```

### Training Requirements

**When Training is Required:**
- New or revised procedures
- New equipment or tools
- Process changes
- Findings related to personnel performance

**Training Documentation:**

```markdown
## CAPA-Related Training Record

CAPA Number: _______________
Training Subject: ___________
Training Date: ______________
Trainer: ___________________

Attendees:
| Name | Signature | Date |
|------|-----------|------|
|      |           |      |

Training Content:
- [ ] Root cause explanation
- [ ] Process/procedure changes
- [ ] New requirements
- [ ] Competency verification

Competency Verified By: _______________
Date: _______________
```

---

## Effectiveness Verification

### Verification vs. Validation

| Verification | Validation |
|--------------|------------|
| Actions implemented correctly | Actions achieved intended results |
| Short-term check | Long-term monitoring |
| Process-focused | Outcome-focused |

### Effectiveness Criteria

**SMART Criteria:**
- **S**pecific: Clearly defined outcome
- **M**easurable: Quantifiable metrics
- **A**chievable: Realistic expectations
- **R**elevant: Related to root cause
- **T**ime-bound: Defined monitoring period

**Examples:**

| Problem | Root Cause | Action | Effectiveness Criteria |
|---------|------------|--------|----------------------|
| 5% test failures | Inadequate sampling | Increase sampling | <1% failure rate for 3 months |
| Customer complaints | Unclear instructions | Revise IFU | Zero complaints on topic for 6 months |
| NCRs from supplier | No incoming inspection | Add inspection | Zero supplier NCRs for 90 days |

### Effectiveness Review Template

```markdown
## CAPA Effectiveness Review

CAPA Number: _______________
Review Date: _______________
Reviewer: __________________

### Review Criteria
Original Problem: _________________
Effectiveness Metric: ______________
Success Threshold: ________________
Review Period: ____________________

### Data Analysis
| Period | Metric Value | Threshold | Pass/Fail |
|--------|--------------|-----------|-----------|
| Month 1 |             |           |           |
| Month 2 |             |           |           |
| Month 3 |             |           |           |

### Conclusion
☐ Effective - Criteria met, CAPA may be closed
☐ Partially Effective - Additional monitoring required
☐ Not Effective - Additional actions required

### Evidence
[Reference to supporting data: complaint logs, NCR reports, audit results, etc.]

### Next Steps (if not effective)
___________________________________
___________________________________

### Approval
Reviewer Signature: _______________ Date: _______
Quality Approval: _________________ Date: _______
```

### Monitoring Period Guidelines

| CAPA Type | Minimum Monitoring |
|-----------|-------------------|
| Product quality | 3 production lots or 90 days |
| Process | 3 months of production |
| Complaints | 6 months |
| Audit findings | Until next audit |
| Supplier | 3 lots or 90 days |

---

## Documentation Requirements

### CAPA File Contents

```
CAPA File Structure:
├── CAPA Form (all sections completed)
├── Investigation Records
│   ├── Data collected
│   ├── Root cause analysis worksheets
│   └── Impact assessment
├── Action Documentation
│   ├── Action plans
│   ├── Change requests (if applicable)
│   └── Training records
├── Verification Evidence
│   ├── Implementation verification
│   ├── Effectiveness data
│   └── Trend analysis
└── Closure Documentation
    ├── Closure approval
    └── Management review submission
```

### Record Retention

Per 21 CFR 820.180:
- Records shall be retained for the design and expected life of the device
- Minimum of 2 years from date of release for commercial distribution

**CAPA Record Retention:**
- Retain for lifetime of product + 2 years
- Include all supporting documentation
- Maintain audit trail for changes

### Traceability

**Required Traceability:**
- CAPA to source (complaint, NCR, audit finding)
- CAPA to affected products/lots
- CAPA to corrective actions taken
- CAPA to verification evidence
- CAPA to management review

---

## FDA Inspection Focus Areas

### Common 483 Observations

| Observation | Prevention |
|-------------|------------|
| CAPA not initiated when required | Define clear CAPA triggers |
| Root cause analysis inadequate | Use structured RCA methods |
| Actions don't address root cause | Verify action-cause linkage |
| Effectiveness not verified | Define measurable criteria |
| CAPA not timely | Set and track target dates |
| Trend analysis not performed | Implement monthly trending |
| Management review missing CAPA input | Include in management review agenda |

### Inspection Preparation

**CAPA Readiness Checklist:**

```markdown
## FDA Inspection CAPA Preparation

### Documentation Review
- [ ] All CAPAs have complete documentation
- [ ] No overdue CAPAs
- [ ] Root cause documented with evidence
- [ ] Effectiveness verified and documented
- [ ] All open CAPAs have current status

### Metrics Available
- [ ] CAPA by source
- [ ] CAPA cycle time
- [ ] Overdue CAPA trend
- [ ] Effectiveness rate
- [ ] Recurring issues

### Process Evidence
- [ ] CAPA procedure current
- [ ] Training records complete
- [ ] Trend analysis documented
- [ ] Management review records show CAPA input

### Common Questions Prepared
- How do you initiate a CAPA?
- How do you determine root cause?
- How do you verify effectiveness?
- Show me your overdue CAPAs
- Show me CAPAs from complaints
```

### CAPA Metrics Dashboard

| Metric | Target | Calculation |
|--------|--------|-------------|
| On-time initiation | 100% | CAPAs initiated within 30 days |
| On-time closure | >90% | CAPAs closed by target date |
| Effectiveness rate | >85% | Effective at first review / Total |
| Average cycle time | <90 days | Average days to closure |
| Overdue CAPAs | 0 | CAPAs past target date |
| Recurring issues | <5% | Repeat CAPAs / Total |

---

## Quick Reference

### CAPA Decision Tree

```
Quality Issue Identified
        │
        ▼
Is it an isolated incident?
├── YES → Correction only (document, may not need CAPA)
│         Evaluate for trend
│
└── NO → Is it a systemic issue?
         ├── YES → Initiate CAPA
         │         Determine if Corrective or Preventive
         │
         └── MAYBE → Investigate further
                     Monitor for recurrence
                     May escalate to CAPA
```

### Root Cause vs. Symptom

| Symptom (NOT root cause) | Root Cause (Address this) |
|--------------------------|---------------------------|
| "Operator made error" | Training inadequate for task |
| "Component was defective" | Incoming inspection ineffective |
| "SOP not followed" | SOP unclear or impractical |
| "Equipment malfunctioned" | Maintenance schedule inadequate |
| "Supplier shipped wrong part" | Purchasing requirements unclear |

### Action Effectiveness Verification

| Action Type | Verification Method | Timeframe |
|-------------|---------------------|-----------|
| Procedure change | Audit for compliance | 30-60 days |
| Training | Competency assessment | Immediate |
| Design change | Product testing | Per protocol |
| Supplier action | Incoming inspection data | 3 lots |
| Equipment | Calibration/performance | Per schedule |

### Integration with Other Systems

| System | CAPA Integration Point |
|--------|------------------------|
| Complaints | Trigger for CAPA, complaint closure after CAPA |
| NCR | Trend to CAPA, NCR references CAPA |
| Audit | Findings generate CAPA, CAPA closure audit |
| Design Control | Design change via CAPA, DHF update |
| Supplier | Supplier CAPA, supplier audit findings |
| Risk Management | Risk file update post-CAPA |
