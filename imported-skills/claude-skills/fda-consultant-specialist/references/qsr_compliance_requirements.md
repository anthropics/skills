# Quality System Regulation (QSR) — Historical Structure with QMSR/ISO 13485:2016 Mapping

> ## ⚠️ STATUS: QMSR transition — the QSR structure below is HISTORICAL
>
> FDA's **Quality Management System Regulation (QMSR)** final rule (89 FR 7496) took effect **February 2, 2026**, amending 21 CFR Part 820 to **incorporate ISO 13485:2016 by reference** and removing the QSR subsection structure documented in this guide. The section numbers used below (820.20–820.250) **no longer exist in the CFR**; they are retained here only as a familiar index into requirements that now flow from ISO 13485:2016 clauses.
>
> **What remains in 21 CFR 820 under the QMSR:** 820.10 (requirements, incl. the ISO 13485:2016 incorporation by reference and Part 830 UDI linkage), 820.35 (records — complaint and servicing-record additions to ISO 13485), 820.45 (device labeling and packaging controls).
> **Unchanged:** 21 CFR Parts 801 (labeling), 803 (MDR), 806 (corrections and removals), 830 (UDI).
>
> Use the [Regulatory Cross-References](#regulatory-cross-references) table at the end of this guide to map every historical QSR section to its current QMSR/ISO 13485:2016 authority. The implementation guidance and templates below remain useful — quality system expectations are substantially the same under ISO 13485 — but **cite ISO 13485 clauses (or retained 820.10/.35/.45), not the historical subsection numbers, in current compliance documentation.**

Implementation guide to the historical 21 CFR Part 820 (QSR) structure for medical device manufacturers, mapped to the QMSR/ISO 13485:2016 requirements now in force.

---

## Table of Contents

- [QSR Overview](#qsr-overview)
- [Management Responsibility (820.20)](#management-responsibility-82020)
- [Design Controls (820.30)](#design-controls-82030)
- [Document Controls (820.40)](#document-controls-82040)
- [Purchasing Controls (820.50)](#purchasing-controls-82050)
- [Production and Process Controls (820.70-75)](#production-and-process-controls-82070-75)
- [CAPA (820.100)](#capa-820100)
- [Device Master Record (820.181)](#device-master-record-820181)
- [FDA Inspection Readiness](#fda-inspection-readiness)

---

## QSR Overview

### Applicability

The QSR applies to:
- Finished device manufacturers
- Specification developers
- Initial distributors of imported devices
- Contract manufacturers
- Repackagers and relabelers

### Exemptions

| Device Class | Exemption Status |
|--------------|------------------|
| Class I (most) | Exempt from design controls (820.30) |
| Class I (listed) | Fully exempt from QSR |
| Class II | Full QSR compliance |
| Class III | Full QSR compliance |

### QSR Structure (historical, pre-2026-02-02)

```
21 CFR Part 820 Subparts (removed by the QMSR; historical reference only):
├── A - General Provisions (820.1-5)
├── B - Quality System Requirements (820.20-25)
├── C - Design Controls (820.30)
├── D - Document Controls (820.40)
├── E - Purchasing Controls (820.50)
├── F - Identification and Traceability (820.60-65)
├── G - Production and Process Controls (820.70-75)
├── H - Acceptance Activities (820.80-86)
├── I - Nonconforming Product (820.90)
├── J - Corrective and Preventive Action (820.100)
├── K - Labeling and Packaging Control (820.120-130)
├── L - Handling, Storage, Distribution, Installation (820.140-170)
├── M - Records (820.180-198)
├── N - Servicing (820.200)
└── O - Statistical Techniques (820.250)
```

---

## Management Responsibility (820.20)

### Quality Policy

**Requirements:**
- Documented quality policy
- Objectives for quality
- Commitment to meeting requirements
- Communicated throughout organization

**Quality Policy Template:**

```markdown
## Quality Policy Statement

[Company Name] is committed to designing, manufacturing, and distributing
medical devices that meet customer requirements and applicable regulatory
standards. We achieve this through:

1. Maintaining an effective Quality Management System
2. Continuous improvement of our processes
3. Compliance with 21 CFR Part 820 and applicable standards
4. Training and empowering employees
5. Supplier quality management

Approved by: _______________  Date: _______________
Management Representative
```

### Organization

| Role | Responsibilities | Documentation |
|------|------------------|---------------|
| Management Representative | QMS oversight, FDA liaison | Org chart, job description |
| Quality Manager | Day-to-day QMS operations | Procedures, authority matrix |
| Design Authority | Design control decisions | DHF sign-offs |
| Production Manager | Manufacturing compliance | Process documentation |

### Management Review

**Frequency:** At least annually (more frequently recommended)

**Required Inputs:**
1. Audit results (internal and external)
2. Customer feedback and complaints
3. Process performance metrics
4. Product conformity data
5. CAPA status
6. Changes affecting QMS
7. Recommendations for improvement

**Required Outputs:**
- Decisions on improvement actions
- Resource needs
- Quality objectives updates

**Management Review Agenda Template:**

```markdown
## Management Review Meeting

Date: _______________
Attendees: _______________

### Agenda Items

1. Review of previous action items
2. Quality objectives and metrics
3. Internal audit results
4. Customer complaints summary
5. CAPA status report
6. Supplier quality performance
7. Regulatory updates
8. Resource requirements
9. Improvement opportunities

### Decisions and Actions
| Item | Decision | Owner | Due Date |
|------|----------|-------|----------|
|      |          |       |          |

### Next Review Date: _______________
```

---

## Design Controls (820.30)

### When Required

Design controls are required for:
- Class II devices (most)
- Class III devices (all)
- Class I devices with software
- Class I devices on exemption list exceptions

### Design Control Process Flow

```
Design Input (820.30c)
    ↓
Design Output (820.30d)
    ↓
Design Review (820.30e)
    ↓
Design Verification (820.30f)
    ↓
Design Validation (820.30g)
    ↓
Design Transfer (820.30h)
    ↓
Design Changes (820.30i)
    ↓
Design History File (820.30j)
```

### Design Input Requirements

**Must Include:**
- Intended use and user requirements
- Patient population
- Performance requirements
- Safety requirements
- Regulatory requirements
- Risk management requirements

**Verification Criteria:**
- Complete (all requirements captured)
- Unambiguous (clear interpretation)
- Not conflicting
- Verifiable or validatable

### Design Output Requirements

| Output Type | Examples | Verification Method |
|-------------|----------|---------------------|
| Device specifications | Drawings, BOMs | Inspection, testing |
| Manufacturing specs | Process parameters | Process validation |
| Software specs | Source code, architecture | Software V&V |
| Labeling | IFU, labels | Review against inputs |

**Essential Requirements:**
- Traceable to design inputs
- Contains acceptance criteria
- Identifies critical characteristics

### Design Review

**Review Stages:**
1. Concept review (feasibility)
2. Design input review (requirements complete)
3. Preliminary design review (architecture)
4. Critical design review (detailed design)
5. Final design review (transfer readiness)

**Participants:**
- Representative of each design function
- Other specialists as needed
- Independent reviewers (no direct design responsibility)

**Documentation:**
- Meeting minutes
- Issues identified
- Resolution actions
- Approval signatures

### Design Verification

**Methods:**
- Inspections and measurements
- Bench testing
- Analysis and calculations
- Simulations
- Comparisons to similar designs

**Verification Matrix Template:**

```markdown
| Req ID | Requirement | Verification Method | Pass Criteria | Result |
|--------|-------------|---------------------|---------------|--------|
| REQ-001 | Dimension tolerance | Measurement | ±0.5mm | |
| REQ-002 | Tensile strength | Testing per ASTM | >500 MPa | |
| REQ-003 | Software function | Unit testing | 100% pass | |
```

### Design Validation

**Definition:** Confirmation that device meets user needs and intended uses

**Validation Requirements:**
- Use initial production units (or equivalent)
- Simulated or actual use conditions
- Includes software validation

**Validation Types:**
1. **Bench validation** - Laboratory simulated use
2. **Clinical validation** - Human subjects (may require IDE)
3. **Usability validation** - Human factors testing

### Design Transfer

**Transfer Checklist:**

```markdown
## Design Transfer Verification

- [ ] DMR complete and approved
- [ ] Manufacturing processes validated
- [ ] Training completed
- [ ] Inspection procedures established
- [ ] Supplier qualifications complete
- [ ] Labeling approved
- [ ] Risk analysis updated
- [ ] Regulatory clearance/approval obtained
```

### Design History File (DHF)

**Contents:**
- Design and development plan
- Design input records
- Design output records
- Design review records
- Design verification records
- Design validation records
- Design transfer records
- Design change records
- Risk management file

---

## Document Controls (820.40)

### Document Approval and Distribution

**Requirements:**
- Documents reviewed and approved before use
- Approved documents available at point of use
- Obsolete documents removed or marked
- Changes reviewed and approved

### Document Control Matrix

| Document Type | Author | Reviewer | Approver | Distribution |
|---------------|--------|----------|----------|--------------|
| SOPs | Process owner | QA | Quality Manager | Controlled |
| Work Instructions | Supervisor | QA | Manager | Controlled |
| Forms | QA | QA | Quality Manager | Controlled |
| Drawings | Engineer | Peer | Design Authority | Controlled |

### Change Control

**Change Request Process:**

```
1. Initiate Change Request
   └── Description, justification, impact assessment

2. Technical Review
   └── Engineering, quality, regulatory assessment

3. Change Classification
   ├── Minor: No regulatory impact
   ├── Moderate: May affect compliance
   └── Major: Regulatory submission required

4. Approval
   └── Change Control Board (CCB) or designated authority

5. Implementation
   └── Training, document updates, inventory actions

6. Verification
   └── Confirm change implemented correctly

7. Close Change Request
   └── Documentation complete
```

---

## Purchasing Controls (820.50)

### Supplier Qualification

**Qualification Criteria:**
- Quality system capability
- Product/service quality history
- Financial stability
- Regulatory compliance history

**Qualification Methods:**

| Method | When Used | Documentation |
|--------|-----------|---------------|
| On-site audit | Critical suppliers, high risk | Audit report |
| Questionnaire | Initial screening | Completed form |
| Certification review | ISO certified suppliers | Cert copies |
| Product qualification | Incoming inspection data | Test results |

### Approved Supplier List (ASL)

**ASL Requirements:**
- Supplier name and contact
- Products/services approved
- Qualification date and method
- Qualification status
- Re-evaluation schedule

### Purchasing Data

**Purchase Order Requirements:**
- Complete product specifications
- Quality requirements
- Applicable standards
- Inspection/acceptance requirements
- Right of access for verification

---

## Production and Process Controls (820.70-75)

### Process Validation (820.75)

**When Required:**
- Process output cannot be fully verified
- Deficiencies would only appear after use
- Examples: sterilization, welding, molding

**Validation Protocol Elements:**

```markdown
## Process Validation Protocol

### 1. Protocol Approval
Prepared by: _______________  Date: _______________
Approved by: _______________  Date: _______________

### 2. Process Description
[Describe process, equipment, materials, parameters]

### 3. Acceptance Criteria
| Parameter | Specification | Test Method |
|-----------|---------------|-------------|
|           |               |             |

### 4. Equipment Qualification
- IQ (Installation Qualification): _______________
- OQ (Operational Qualification): _______________
- PQ (Performance Qualification): _______________

### 5. Validation Runs
Number of runs: _____ (minimum 3)
Lot sizes: _____

### 6. Results Summary
| Run | Date | Parameters | Results | Pass/Fail |
|-----|------|------------|---------|-----------|
| 1   |      |            |         |           |
| 2   |      |            |         |           |
| 3   |      |            |         |           |

### 7. Conclusion
Process validated: Yes / No
Revalidation triggers: _____
```

### Environmental Controls (820.70(c))

**Controlled Conditions:**
- Temperature and humidity
- Particulate contamination (cleanrooms)
- ESD (electrostatic discharge)
- Lighting levels

**Monitoring Requirements:**
- Continuous or periodic monitoring
- Documented limits
- Out-of-specification procedures
- Calibrated equipment

### Personnel (820.70(d))

**Training Requirements:**
- Job-specific training
- Competency verification
- Retraining for significant changes
- Training records maintained

**Training Record Template:**

```markdown
## Training Record

Employee: _______________ ID: _______________
Position: _______________

| Training Topic | Trainer | Date | Method | Competency Verified |
|----------------|---------|------|--------|---------------------|
|                |         |      |        | Signature: ________ |
```

### Equipment (820.70(g))

**Requirements:**
- Maintenance schedule
- Calibration program
- Adjustment limits documented
- Inspection before use

### Calibration (820.72)

**Calibration Program Elements:**
1. Equipment identification
2. Calibration frequency
3. Calibration procedures
4. Accuracy requirements
5. Traceability to NIST standards
6. Out-of-tolerance actions

---

## CAPA (820.100)

### CAPA Sources

- Customer complaints
- Nonconforming product
- Audit findings
- Process monitoring
- Returned products
- MDR/Vigilance reports
- Trend analysis

### CAPA Process

```
1. Identification
   └── Problem statement, data collection

2. Investigation
   └── Root cause analysis (5 Whys, Fishbone, etc.)

3. Action Determination
   ├── Correction: Immediate fix
   └── Corrective/Preventive: Address root cause

4. Implementation
   └── Action execution, documentation

5. Verification
   └── Confirm actions completed

6. Effectiveness Review
   └── Problem recurrence check (30-90 days)

7. Closure
   └── Management approval
```

### Root Cause Analysis Tools

**5 Whys Example:**

```
Problem: Device failed during use

Why 1: Component failed
Why 2: Component was out of specification
Why 3: Incoming inspection did not detect
Why 4: Inspection procedure inadequate
Why 5: Procedure not updated for new component

Root Cause: Document control failure - procedure not updated
```

**Fishbone Categories:**
- Man (People)
- Machine (Equipment)
- Method (Process)
- Material
- Measurement
- Environment

### CAPA Metrics

| Metric | Target | Frequency |
|--------|--------|-----------|
| CAPA on-time closure | >90% | Monthly |
| Overdue CAPAs | <5 | Monthly |
| Effectiveness rate | >85% | Quarterly |
| Average days to closure | <60 | Monthly |

---

## Device Master Record (820.181)

### DMR Contents

```
Device Master Record
├── Device specifications
│   ├── Drawings
│   ├── Composition/formulation
│   └── Component specifications
├── Production process specifications
│   ├── Manufacturing procedures
│   ├── Assembly instructions
│   └── Process parameters
├── Quality assurance procedures
│   ├── Acceptance criteria
│   ├── Inspection procedures
│   └── Test methods
├── Packaging and labeling specifications
│   ├── Package drawings
│   ├── Label content
│   └── IFU content
├── Installation, maintenance, servicing procedures
└── Environmental requirements
```

### Device History Record (DHR) - 820.184

**DHR Contents:**
- Dates of manufacture
- Quantity manufactured
- Quantity released for distribution
- Acceptance records
- Primary identification label
- Device identification and control numbers

### Quality System Record (QSR) - 820.186

**QSR Contents:**
- Procedures and changes
- Calibration records
- Distribution records
- Complaint files
- CAPA records
- Audit reports

---

## FDA Inspection Readiness

### Pre-Inspection Preparation

**30-Day Readiness Checklist:**

```markdown
## FDA Inspection Readiness

### Documentation Review
- [ ] Quality manual current
- [ ] SOPs reviewed and approved
- [ ] Training records complete
- [ ] CAPA files complete
- [ ] Complaint files organized
- [ ] DMR/DHR accessible
- [ ] Management review records current

### Facility Review
- [ ] Controlled areas properly identified
- [ ] Equipment calibration current
- [ ] Environmental monitoring records available
- [ ] Storage conditions appropriate
- [ ] Quarantine areas clearly marked

### Personnel Preparation
- [ ] Escort team identified
- [ ] Subject matter experts briefed
- [ ] Front desk/reception notified
- [ ] Conference room reserved
- [ ] FDA credentials verification process

### Record Accessibility
- [ ] Electronic records accessible
- [ ] Backup copies available
- [ ] Audit trail functional
- [ ] Archive records retrievable
```

### During Inspection

**Escort Guidelines:**
1. One designated escort with investigator at all times
2. Answer questions truthfully and concisely
3. Don't volunteer information not requested
4. Request clarification if question unclear
5. Get help from SME for technical questions
6. Document all requests and commitments

**Record Request Tracking:**

| Request # | Date | Document Requested | Provided By | Date Provided |
|-----------|------|-------------------|-------------|---------------|
|           |      |                   |             |               |

### Post-Inspection

**FDA 483 Response:**
- Due within 15 business days
- Address each observation specifically
- Include corrective actions and timeline
- Provide evidence of completion where possible

**Response Format:**

```markdown
## Observation [Number]

### FDA Observation:
[Copy verbatim from Form 483]

### Company Response:

#### Understanding of Observation:
[Demonstrate understanding of the concern]

#### Immediate Correction:
[Actions already taken]

#### Root Cause Analysis:
[Investigation findings]

#### Corrective Actions:
| Action | Responsible | Target Date | Status |
|--------|-------------|-------------|--------|
|        |             |             |        |

#### Preventive Actions:
[Systemic improvements]

#### Verification:
[How effectiveness will be verified]
```

---

## Compliance Metrics Dashboard

### Key Performance Indicators

| Category | Metric | Target | Current |
|----------|--------|--------|---------|
| CAPA | On-time closure rate | >90% | |
| CAPA | Effectiveness rate | >85% | |
| Complaints | Response time (days) | <5 | |
| Training | Compliance rate | 100% | |
| Calibration | On-time rate | 100% | |
| Audit | Findings closure rate | >95% | |
| NCR | Recurring issues | <5% | |
| Supplier | Quality rate | >98% | |

### Trend Analysis

**Monthly Review Items:**
- Complaint trends by product/failure mode
- NCR trends by cause code
- CAPA effectiveness
- Supplier quality
- Production yields
- Customer feedback

---

## Quick Reference

### Common 483 Observations

| Observation | Prevention |
|-------------|------------|
| CAPA not effective | Verify effectiveness before closure |
| Training incomplete | Competency-based training records |
| Document control gaps | Regular procedure reviews |
| Complaint investigation | Thorough, documented investigations |
| Supplier controls weak | Robust qualification and monitoring |
| Validation inadequate | Follow IQ/OQ/PQ protocols |

### Regulatory Cross-References

Historical QSR sections (removed effective 2026-02-02) mapped to their current QMSR/ISO 13485:2016 authority:

| Historical QSR Section | Title | Current QMSR / ISO 13485:2016 authority |
|------------------------|-------|------------------------------------------|
| 820.20 | Management responsibility | ISO 13485 §5.1, 5.5, 5.6 |
| 820.30 | Design controls | ISO 13485 §7.3 |
| 820.40 | Document controls | ISO 13485 §4.2.4 |
| 820.50 | Purchasing controls | ISO 13485 §7.4 |
| 820.60–.65 | Identification and traceability | ISO 13485 §7.5.8, 7.5.9 |
| 820.70 | Production and process controls | ISO 13485 §6.3, 6.4, 7.5.1 |
| 820.72 | Inspection, measuring, test equipment | ISO 13485 §7.6 |
| 820.75 | Process validation | ISO 13485 §7.5.6 |
| 820.80–.86 | Acceptance activities | ISO 13485 §7.4.3, 8.2.6 |
| 820.90 | Nonconforming product | ISO 13485 §8.3 |
| 820.100 | CAPA | ISO 13485 §8.5.2, 8.5.3 |
| 820.120–.130 | Labeling and packaging | 21 CFR 820.45 (retained) + ISO 13485 §7.5.1 |
| 820.140–.170 | Handling, storage, distribution, installation | ISO 13485 §7.5.5, 7.5.3 |
| 820.180–.186 | Records (incl. DMR 820.181, DHR 820.184, QSR 820.186) | ISO 13485 §4.2.3 (medical device file), 4.2.5 (records) + 21 CFR 820.35 (retained) |
| 820.198 | Complaint files | ISO 13485 §8.2.2 + 21 CFR 820.35(b) |
| 820.200 | Servicing | ISO 13485 §7.5.4 + 21 CFR 820.35 |
| 820.250 | Statistical techniques | ISO 13485 §8.1 |

Retained/renumbered under QMSR: 820.10 (requirements; incorporates ISO 13485:2016 by reference), 820.35 (records), 820.45 (device labeling and packaging controls). Unchanged: 21 CFR 801, 803, 806, 830.
