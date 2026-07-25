# ISO 13485:2016 Clause Requirements

Detailed requirements for each ISO 13485:2016 clause with implementation guidance and audit criteria.

---

## Table of Contents

- [Clause 4: Quality Management System](#clause-4-quality-management-system)
- [Clause 5: Management Responsibility](#clause-5-management-responsibility)
- [Clause 6: Resource Management](#clause-6-resource-management)
- [Clause 7: Product Realization](#clause-7-product-realization)
- [Clause 8: Measurement, Analysis and Improvement](#clause-8-measurement-analysis-and-improvement)

---

## Clause 4: Quality Management System

### 4.1 General Requirements

| Requirement | Implementation | Evidence |
|-------------|----------------|----------|
| Determine processes needed | Process map showing QMS processes | Documented process map |
| Determine sequence and interaction | Process interaction diagram | Cross-reference matrix |
| Determine criteria for operation | Process metrics and acceptance criteria | Documented criteria per process |
| Ensure resources available | Resource allocation per process | Training records, equipment logs |
| Monitor, measure, analyze | Process monitoring procedures | Trend data, performance reports |
| Implement actions for results | Improvement projects, CAPAs | Action records with verification |
| Document processes | Procedures, work instructions | Controlled document list |

**Audit Questions:**
- How are QMS processes identified and documented?
- What criteria determine if processes are operating effectively?
- How is outsourced process control demonstrated?

### 4.2 Documentation Requirements

#### 4.2.1 General

| Document Type | Requirement | Retention |
|---------------|-------------|-----------|
| Quality Policy | Documented statement of commitment | Life of QMS |
| Quality Objectives | Measurable objectives at relevant functions | Life of QMS |
| Quality Manual | QMS scope and processes | Current version |
| Documented Procedures | Required by standard | Life of QMS + 2 years |
| Records | Evidence of conformity | As defined per record type |

#### 4.2.2 Quality Manual

**Required Content:**
1. Scope of QMS including justification for exclusions
2. Documented procedures or reference to them
3. Description of process interactions

**Quality Manual Template Structure:**
```
QUALITY MANUAL
1. Company Overview
   1.1 Company Description
   1.2 Scope of QMS
   1.3 Exclusions and Justification
2. Quality Policy
3. Quality Objectives
4. QMS Structure
   4.1 Process Map
   4.2 Process Interactions
   4.3 Organizational Chart
5. Procedure References
   5.1 Document Control
   5.2 Record Control
   5.3 Management Review
   5.4 Internal Audit
   5.5 Nonconformity Control
   5.6 CAPA
6. Appendices
   6.1 Glossary
   6.2 Regulatory Cross-Reference
```

#### 4.2.3 Control of Documents

| Control Element | Requirement | Method |
|-----------------|-------------|--------|
| Approval | Adequate prior to issue | Signature/electronic approval |
| Review and update | Re-approval after changes | Periodic review process |
| Identification of changes | Change history visible | Revision log in document |
| Revision status | Current revision identifiable | Document master list |
| Legibility | Readable and identifiable | Format standards |
| External documents | Identified and controlled | Incoming document log |
| Obsolete documents | Prevented from unintended use | Archive system |

**Document Numbering Convention:**
```
[TYPE]-[AREA]-[SEQUENCE]-[REV]

TYPE:
  QM  = Quality Manual
  SOP = Standard Operating Procedure
  WI  = Work Instruction
  TF  = Template/Form
  POL = Policy

AREA:
  01 = Quality Management
  02 = Document Control
  03 = Training
  04 = Design
  05 = Purchasing
  06 = Production
  07 = Quality Control
  08 = CAPA

Example: SOP-02-001-03 = Document Control SOP, Revision 03
```

#### 4.2.4 Control of Records

> **⚠️ STATUS — QMSR transition (effective 2026-02-02):** Under FDA's Quality Management System Regulation (QMSR, 89 FR 7496), 21 CFR Part 820 now **incorporates ISO 13485:2016 by reference** and the legacy QSR subsection numbers below (820.30/.181/.184/.198) **no longer exist in the CFR** — they are shown only as a historical index. The current authority is **ISO 13485:2016 §4.2.5 (control of records)** plus retained **21 CFR 820.35** (records). Cite the ISO 13485 clause in current documentation.

| Record Category | Minimum Retention | Basis (current authority — legacy QSR shown for index) |
|-----------------|-------------------|-------|
| Device Master Record | Life of device + 2 years | ISO 13485 §4.2.3 (medical device file)/§4.2.5 (legacy QSR 820.181, historical) |
| Device History Record | Life of device + 2 years | ISO 13485 §4.2.5 + 21 CFR 820.35 (legacy QSR 820.184, historical) |
| Design History File | Life of device + 2 years | ISO 13485 §7.3.10/§4.2.5 (legacy QSR 820.30, historical) |
| Training Records | Employment + 3 years | Best practice |
| Audit Records | 7 years | Best practice |
| Complaint Records | Life of device + 2 years | ISO 13485 §8.2.2/§4.2.5 + 21 CFR 820.35(b) (legacy QSR 820.198, historical) |
| CAPA Records | 7 years | Best practice |
| Calibration Records | Equipment life + 2 years | Best practice |
| Supplier Records | Relationship + 3 years | Best practice |

---

## Clause 5: Management Responsibility

### 5.1 Management Commitment

| Commitment Area | Evidence Required |
|-----------------|-------------------|
| Communicate importance of requirements | Meeting minutes, communications |
| Establish quality policy | Documented policy, communication records |
| Ensure quality objectives established | Objective documentation |
| Conduct management reviews | Management review records |
| Ensure resources available | Budget records, staffing records |

### 5.2 Customer Focus

| Requirement | Implementation | Verification |
|-------------|----------------|--------------|
| Customer requirements determined | Requirements review process | Contract review records |
| Requirements met | Process controls | Inspection and test data |
| Regulatory requirements met | Regulatory register | Compliance assessments |
| Customer satisfaction enhanced | Feedback collection | Satisfaction data, complaints |

### 5.3 Quality Policy

**Policy Requirements:**
- Appropriate to organization purpose
- Commitment to compliance and effectiveness
- Framework for quality objectives
- Communicated and understood
- Reviewed for continuing suitability

**Sample Quality Policy Elements:**
```
[Company Name] Quality Policy

We are committed to:
- Designing and manufacturing safe, effective medical devices
- Meeting customer and regulatory requirements
- Maintaining an effective Quality Management System
- Continuously improving our processes and products
- Providing resources for QMS effectiveness

Signed: [Executive]
Date: [Date]
Review Date: [Annual]
```

### 5.4 Planning

#### 5.4.1 Quality Objectives

| Objective Criteria | Requirement |
|-------------------|-------------|
| Measurable | Quantifiable targets |
| Consistent with policy | Aligned to policy statements |
| Relevant functions | Cascaded to departments |
| Includes compliance | Regulatory and customer requirements |
| Includes product conformity | Product-related targets |

**Objective Template:**
```
QUALITY OBJECTIVE [Year]

Objective: [Statement]
Metric: [How measured]
Target: [Specific value]
Baseline: [Current performance]
Owner: [Responsible person]
Due Date: [Target date]
Reporting: [Frequency]
```

#### 5.4.2 Quality Management System Planning

**Planning Requirements:**
- QMS meets general requirements (4.1)
- QMS meets quality objectives (5.4.1)
- Integrity maintained during changes

### 5.5 Responsibility, Authority and Communication

#### 5.5.1 Responsibility and Authority

| Role | Responsibilities | Authority |
|------|-----------------|-----------|
| Top Management | QMS commitment, resources, policy | Budget, staffing, strategic decisions |
| Quality Manager | QMS implementation, reporting | Document approval, CAPA approval |
| Department Managers | Process ownership, resources | Process changes, training |
| Process Owners | Process performance, improvements | Procedure changes within scope |

#### 5.5.2 Management Representative

| QMR Responsibility | Activities |
|-------------------|------------|
| QMS establishment | Process definition, documentation |
| QMS implementation | Training, deployment, monitoring |
| QMS maintenance | Audits, reviews, improvements |
| Reporting to top management | Performance reports, recommendations |
| Awareness promotion | Training, communications |

#### 5.5.3 Internal Communication

| Communication Type | Method | Frequency |
|-------------------|--------|-----------|
| Policy and objectives | Posting, training | Annual and on change |
| QMS performance | Dashboards, reports | Monthly |
| Changes affecting quality | Email, meetings | As needed |
| Audit results | Reports, presentations | Per audit |

### 5.6 Management Review

#### 5.6.1 General

| Requirement | Specification |
|-------------|---------------|
| Frequency | Planned intervals (typically quarterly/semi-annually) |
| Purpose | Assess QMS suitability, adequacy, effectiveness |
| Records | Documented meeting records |

#### 5.6.2 Review Input

| Input | Source | Responsible |
|-------|--------|-------------|
| Audit results | Internal/external audits | QA Manager |
| Customer feedback | Complaints, surveys | Customer Quality |
| Process performance | Metrics, yields | Process Owners |
| Product conformity | Inspection data | QC Manager |
| CAPA status | CAPA system | CAPA Officer |
| Previous actions | Prior review records | QMR |
| Changes affecting QMS | Regulatory, organizational | RA, HR |
| Recommendations | All sources | All Managers |

#### 5.6.3 Review Output

| Output | Documentation |
|--------|---------------|
| QMS improvement decisions | Action items with owners |
| Process improvements | Project charters |
| Resource needs | Resource allocation plans |
| Product improvements | Design change requests |

---

## Clause 6: Resource Management

### 6.1 Provision of Resources

**Resource Categories:**
- Human resources (competent personnel)
- Infrastructure (facilities, equipment, software)
- Work environment (environmental conditions)

### 6.2 Human Resources

| Requirement | Implementation | Evidence |
|-------------|----------------|----------|
| Competence determined | Job descriptions, competency matrix | Role definitions |
| Training provided | Training programs | Training records |
| Effectiveness evaluated | Assessments, observations | Competency verification |
| Awareness ensured | Orientation, ongoing training | Acknowledgments |
| Records maintained | Training database | Training files |

**Competency Matrix Template:**
```
COMPETENCY MATRIX

Role: [Job Title]
Department: [Department]

Required Competencies:
| Competency | Requirement Level | Method | Verification |
|------------|------------------|--------|--------------|
| [Skill 1] | Expert/Proficient/Basic | Training/OJT | Assessment |
| [Skill 2] | Expert/Proficient/Basic | Training/OJT | Assessment |

Training Requirements:
| Training | Initial | Refresher | Record |
|----------|---------|-----------|--------|
| ISO 13485 Awareness | Yes | Annual | TR-001 |
| Document Control | Yes | On Change | TR-002 |
```

### 6.3 Infrastructure

| Infrastructure Type | Control Requirements |
|--------------------|---------------------|
| Buildings and workspace | Cleaning, maintenance schedules |
| Process equipment | Maintenance, calibration |
| Supporting services | Utilities, IT systems |
| Information systems | Backup, security, validation |

### 6.4 Work Environment and Contamination Control

| Environment Factor | Control Method | Monitoring |
|-------------------|----------------|------------|
| Temperature | HVAC control | Continuous logging |
| Humidity | HVAC control | Continuous logging |
| Cleanliness | Cleaning procedures | Particle counts |
| Lighting | Lux levels | Periodic verification |
| ESD protection | Grounding, ionization | Periodic testing |

---

## Clause 7: Product Realization

### 7.1 Planning of Product Realization

| Planning Element | Content |
|-----------------|---------|
| Quality objectives for product | Product-specific quality targets |
| Processes and documentation | Process flow, required documents |
| Verification and validation | Test methods, acceptance criteria |
| Records | Required quality records |
| Risk management | Per ISO 14971 |

### 7.2 Customer-Related Processes

#### 7.2.1 Determination of Requirements

| Requirement Type | Source |
|-----------------|--------|
| Customer-specified | Contract, purchase order |
| Not stated but necessary | Intended use analysis |
| Regulatory | Applicable standards, regulations |
| Organization-defined | Internal specifications |

#### 7.2.2 Review of Requirements

| Review Element | Verification |
|----------------|--------------|
| Requirements defined | Complete specification |
| Differences resolved | Documented resolution |
| Ability to meet | Feasibility assessment |
| Risk management | Initial risk assessment |

#### 7.2.3 Communication

| Communication Type | Method |
|-------------------|--------|
| Product information | Catalogs, IFU |
| Inquiries and orders | Sales process |
| Feedback and complaints | Customer feedback system |
| Advisory notices | Field safety notices |

### 7.3 Design and Development

| Stage | Clause | Requirements |
|-------|--------|--------------|
| Planning | 7.3.2 | Stages, reviews, responsibilities |
| Inputs | 7.3.3 | Functional, performance, regulatory |
| Outputs | 7.3.4 | Meet inputs, acceptance criteria |
| Review | 7.3.5 | Evaluate ability to meet requirements |
| Verification | 7.3.6 | Outputs meet inputs |
| Validation | 7.3.7 | Product meets intended use |
| Transfer | 7.3.8 | Verified before production |
| Changes | 7.3.9 | Controlled, reviewed, verified |

### 7.4 Purchasing

#### 7.4.1 Purchasing Process

| Control Element | Implementation |
|-----------------|----------------|
| Supplier evaluation | Qualification procedure |
| Selection criteria | Quality, delivery, cost |
| Monitoring | Performance metrics |
| Re-evaluation | Periodic review |

**Supplier Classification:**
```
Category A: Critical - Affects product safety/performance
  - Full qualification audit
  - Annual performance review
  - Quality agreement required

Category B: Major - Affects product quality
  - Qualification questionnaire
  - Periodic performance review
  - Quality requirements communicated

Category C: Minor - Indirect impact
  - Initial assessment
  - Issue-based review
  - Standard terms
```

#### 7.4.2 Purchasing Information

| Information Required | Purpose |
|---------------------|---------|
| Product specifications | Clear requirements |
| QMS requirements | Supplier system expectations |
| Personnel competence | Where applicable |
| Approval requirements | Where applicable |

#### 7.4.3 Verification of Purchased Product

| Verification Method | Application |
|--------------------|-------------|
| Incoming inspection | Standard verification |
| Source inspection | Critical items |
| Certificate of Conformance | Documented evidence |
| Certificate of Analysis | Material verification |

### 7.5 Production and Service Provision

#### 7.5.1 Control of Production and Service Provision

| Control Element | Implementation |
|-----------------|----------------|
| Product information | Specifications, drawings |
| Work instructions | Where necessary |
| Suitable equipment | Qualified equipment |
| Monitoring devices | Calibrated instruments |
| Implementation of monitoring | Inspections, tests |
| Defined processes | Process parameters |
| Labeling and packaging | Per requirements |

#### 7.5.2 Cleanliness of Product

| Cleanliness Control | Method |
|--------------------|--------|
| Product cleaning | Validated procedures |
| Contamination prevention | Controlled environment |
| Process aids | Qualified, controlled |

#### 7.5.3 Installation Activities

| Requirement | Implementation |
|-------------|----------------|
| Installation requirements | Documented instructions |
| Acceptance criteria | Defined criteria |
| Records | Installation records |

#### 7.5.4 Servicing Activities

| Requirement | Implementation |
|-------------|----------------|
| Documented requirements | Service procedures |
| Reference materials | Service manuals |
| Measurement equipment | Calibrated |
| Records | Service records |

#### 7.5.5 Particular Requirements for Sterile Medical Devices

| Process | Control |
|---------|---------|
| Sterilization validation | Per ISO 11135/11137/17665 |
| Parameter control | Monitoring records |
| Sterile barrier | Validated packaging |

#### 7.5.6 Validation of Processes

| Validation Required When | Evidence |
|-------------------------|----------|
| Output cannot be verified | Validation protocol and report |
| Deficiencies appear only in use | Process capability data |
| Special processes | Qualified operators |

**Process Validation Elements:**
- Equipment qualification (IQ/OQ/PQ)
- Process parameters
- Monitoring methods
- Operator qualification
- Revalidation criteria

#### 7.5.7 Particular Requirements for Validation

| Requirement | Implementation |
|-------------|----------------|
| Documented procedures | Validation SOPs |
| Defined methods | Statistical methods |
| Acceptance criteria | Predefined criteria |
| Software validation | Where applicable |
| Revalidation | Change-triggered |

#### 7.5.8 Identification

| Identification Type | Method |
|--------------------|--------|
| Product | Labels, markings |
| Documentation | Document numbers |
| Unique Device Identification | UDI per regulation |

#### 7.5.9 Traceability

| Traceability Element | Record |
|---------------------|--------|
| Components | Lot/batch numbers |
| Materials | Certificates |
| Work environment | Environmental records |
| Measurement equipment | Calibration records |
| Personnel | Training records |
| Distribution | Shipping records |

#### 7.5.10 Customer Property

| Control | Implementation |
|---------|----------------|
| Identification | Marking, segregation |
| Verification | Incoming inspection |
| Protection | Storage conditions |
| Safeguarding | Security measures |
| Reporting | Loss/damage notification |

#### 7.5.11 Preservation of Product

| Preservation Element | Control |
|---------------------|---------|
| Identification | Labels, markings |
| Handling | Procedures |
| Packaging | Specifications |
| Storage | Conditions, FIFO |
| Protection | Environmental controls |

### 7.6 Control of Monitoring and Measuring Equipment

| Control Element | Implementation |
|-----------------|----------------|
| Calibration | At specified intervals |
| Adjustment | As needed |
| Identification | Calibration status |
| Safeguarding | Protection from damage |
| Software validation | Where applicable |
| Records | Calibration records |

---

## Clause 8: Measurement, Analysis and Improvement

### 8.1 General

**Monitoring and Measurement Requirements:**
- Demonstrate product conformity
- Ensure QMS conformity
- Maintain QMS effectiveness

### 8.2 Monitoring and Measurement

#### 8.2.1 Feedback

| Feedback Source | Collection Method |
|-----------------|-------------------|
| Customer complaints | Complaint system |
| Customer surveys | Periodic surveys |
| Field feedback | Service reports |
| Regulatory feedback | Inspection findings |

#### 8.2.2 Complaint Handling

| Process Step | Requirements |
|--------------|--------------|
| Receipt | Timely logging |
| Investigation | Root cause analysis |
| Corrective action | If warranted |
| Regulatory reporting | If required |
| Trend analysis | Aggregate review |

#### 8.2.3 Reporting to Regulatory Authorities

| Report Type | Trigger | Timeline |
|-------------|---------|----------|
| MDR (Medical Device Report) | Death/serious injury | 30 days (5 if awareness) |
| FSCA (Field Safety Corrective Action) | Safety issue | Without delay |
| Periodic Safety Update | Per regulation | Per schedule |

#### 8.2.4 Internal Audit

| Audit Element | Requirement |
|---------------|-------------|
| Planned program | Risk-based schedule |
| Criteria and scope | Defined per audit |
| Auditor selection | Independent, competent |
| Procedure | Documented process |
| Records | Audit reports, findings |
| Follow-up | CAPA, verification |

**Audit Program Template:**
```
ANNUAL INTERNAL AUDIT PROGRAM

Year: [Year]

| Audit # | Area/Process | Scope | Auditor | Planned Date | Status |
|---------|--------------|-------|---------|--------------|--------|
| IA-01 | Document Control | 4.2.3, 4.2.4 | [Name] | Q1 | |
| IA-02 | Design Control | 7.3 | [Name] | Q2 | |
| IA-03 | Production | 7.5 | [Name] | Q2 | |
| IA-04 | Purchasing | 7.4 | [Name] | Q3 | |
| IA-05 | CAPA | 8.5.2, 8.5.3 | [Name] | Q3 | |
| IA-06 | Management Review | 5.6 | [Name] | Q4 | |

Risk Considerations:
- Previous audit findings
- Regulatory changes
- Process changes
- Complaint trends
```

#### 8.2.5 Monitoring and Measurement of Processes

| Monitoring Type | Method |
|-----------------|--------|
| Process metrics | KPIs, trend analysis |
| Process audits | Internal audits |
| Process reviews | Management review |

#### 8.2.6 Monitoring and Measurement of Product

| Stage | Verification |
|-------|--------------|
| Incoming | Incoming inspection |
| In-process | In-process inspection |
| Final | Final inspection and test |
| Release | Authorized release |

### 8.3 Control of Nonconforming Product

| Control Element | Requirement |
|-----------------|-------------|
| Identification | Clear marking |
| Segregation | Physical separation |
| Documentation | NC record |
| Disposition | Use as is/rework/scrap/return |
| Concession | If accepted |
| Reinspection | After rework |
| Investigation | For detected after delivery |

**Nonconformity Disposition Options:**
```
1. Use As Is (Concession)
   - Does not affect safety/performance
   - Customer approval if applicable
   - Documented justification

2. Rework
   - Per approved procedure
   - Reinspection required
   - Records maintained

3. Scrap/Reject
   - Physical destruction or marking
   - Prevented from reentry
   - Documented disposal

4. Return to Supplier
   - Communication with supplier
   - Replacement or credit
   - Root cause if systemic
```

### 8.4 Analysis of Data

| Data Source | Analysis |
|-------------|----------|
| Feedback | Complaint trends, satisfaction |
| Nonconformity | Defect Pareto, trends |
| Process performance | Capability, trends |
| Supplier | Performance trends |
| Audit | Finding trends |

### 8.5 Improvement

#### 8.5.1 General

**Improvement Sources:**
- Quality policy
- Quality objectives
- Audit results
- Data analysis
- Corrective actions
- Preventive actions
- Management review

#### 8.5.2 Corrective Action

| Process Step | Requirement |
|--------------|-------------|
| Review nonconformity | Including complaints |
| Determine cause | Root cause analysis |
| Evaluate action need | Based on risk |
| Determine action | Proportionate to risk |
| Implement action | Execute plan |
| Document results | Records |
| Review effectiveness | Verification |

#### 8.5.3 Preventive Action

| Process Step | Requirement |
|--------------|-------------|
| Determine potential NC | Risk analysis, trends |
| Evaluate action need | Prevention opportunity |
| Determine action | Proportionate to risk |
| Implement action | Execute plan |
| Document results | Records |
| Review effectiveness | Verification |
