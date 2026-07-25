# QMS Process Templates

Ready-to-use templates for ISO 13485 QMS processes including document control, internal audit, CAPA, and supplier management.

---

## Table of Contents

- [Document Control Templates](#document-control-templates)
- [Internal Audit Templates](#internal-audit-templates)
- [CAPA Templates](#capa-templates)
- [Supplier Management Templates](#supplier-management-templates)
- [Training Templates](#training-templates)
- [Nonconformity Templates](#nonconformity-templates)

---

## Document Control Templates

### Document Master List

```
DOCUMENT MASTER LIST

Organization: [Company Name]
Last Updated: [Date]
Maintained By: Document Control

| Doc # | Title | Rev | Effective Date | Status | Owner | Next Review |
|-------|-------|-----|----------------|--------|-------|-------------|
| QM-001 | Quality Manual | 03 | 2024-01-15 | Effective | QMR | 2025-01-15 |
| SOP-01-001 | Document Control | 04 | 2024-03-01 | Effective | QA Mgr | 2025-03-01 |
| SOP-01-002 | Record Control | 02 | 2024-02-01 | Effective | QA Mgr | 2025-02-01 |
| | | | | | | |

Status Values: Draft, Under Review, Effective, Obsolete
```

### Document Change Request

```
DOCUMENT CHANGE REQUEST

DCR Number: DCR-[YYYY]-[NNN]
Date Submitted: [Date]
Submitted By: [Name]

DOCUMENT INFORMATION
Document Number: [Number]
Document Title: [Title]
Current Revision: [Rev]

CHANGE REQUEST
Change Type: [ ] Administrative [ ] Minor [ ] Major [ ] Emergency
Requested Change: [Description of change]

Reason for Change:
[ ] Regulatory requirement
[ ] Process improvement
[ ] Nonconformity/CAPA
[ ] Organizational change
[ ] Error correction
[ ] Other: [Specify]

Justification: [Detailed justification]

IMPACT ASSESSMENT
Training Required: [ ] Yes [ ] No
  If yes, who: [Roles/departments]
Other Documents Affected: [List]
Regulatory Filing Impact: [ ] Yes [ ] No
  If yes, details: [Explain]

APPROVALS
Requested By: _________________ Date: _______
Document Owner: _________________ Date: _______
QA Approval: _________________ Date: _______

COMPLETION
New Revision: [Rev]
Effective Date: [Date]
Training Completed: [ ] Yes [ ] N/A
Distribution Completed: [ ] Yes
```

### Document Review Record

```
DOCUMENT REVIEW RECORD

Document Number: [Number]
Document Title: [Title]
Current Revision: [Rev]
Review Due Date: [Date]
Review Completed: [Date]

REVIEWERS
| Reviewer | Role | Review Date | Comments | Signature |
|----------|------|-------------|----------|-----------|
| [Name] | [Role] | [Date] | [Comments] | |
| [Name] | [Role] | [Date] | [Comments] | |

REVIEW OUTCOME
[ ] No changes required - document remains current
[ ] Minor changes required - see attached DCR
[ ] Major revision required - see attached DCR
[ ] Document obsolete - initiate retirement

NEXT REVIEW
Next Review Date: [Date]

APPROVAL
Review Completed By: _________________ Date: _______
Approved By: _________________ Date: _______
```

---

## Internal Audit Templates

### Annual Audit Schedule

```
INTERNAL AUDIT SCHEDULE

Year: [Year]
Prepared By: [Name]
Approved By: [Name]
Date: [Date]

AUDIT SCHEDULE
| Audit # | Process/Area | ISO Clauses | Lead Auditor | Q1 | Q2 | Q3 | Q4 |
|---------|--------------|-------------|--------------|----|----|----|----|
| IA-001 | Document Control | 4.2.3, 4.2.4 | [Name] | X | | | |
| IA-002 | Management Review | 5.6 | [Name] | | X | | |
| IA-003 | Training | 6.2 | [Name] | | X | | |
| IA-004 | Design Control | 7.3 | [Name] | | | X | |
| IA-005 | Purchasing | 7.4 | [Name] | | | X | |
| IA-006 | Production | 7.5 | [Name] | | | | X |
| IA-007 | CAPA | 8.5.2, 8.5.3 | [Name] | | | | X |

RISK FACTORS CONSIDERED
[ ] Previous audit findings
[ ] Regulatory changes
[ ] Process changes
[ ] Complaint trends
[ ] Management concerns

SCHEDULE REVISION LOG
| Rev | Date | Change | Approved By |
|-----|------|--------|-------------|
| 00 | [Date] | Initial release | [Name] |
```

### Audit Plan

```
INTERNAL AUDIT PLAN

Audit Number: IA-[YYYY]-[NNN]
Audit Date(s): [Date(s)]
Audit Type: [ ] Process [ ] System [ ] Product

SCOPE
Process/Area: [Name]
ISO 13485 Clauses: [List]
Regulatory Requirements: [If applicable]
Locations: [Locations]

AUDIT TEAM
Lead Auditor: [Name]
Auditor(s): [Names]
Observer(s): [If any]

AUDITEE CONTACTS
Process Owner: [Name]
Other Contacts: [Names]

AUDIT CRITERIA
- ISO 13485:2016
- [Organization procedures]
- [Regulatory requirements]

AUDIT SCHEDULE
| Time | Activity | Participants |
|------|----------|--------------|
| 09:00 | Opening meeting | All |
| 09:30 | Document review | Auditor, Doc Control |
| 10:30 | Process observation | Auditor, Operators |
| 12:00 | Lunch | |
| 13:00 | Record review | Auditor, QA |
| 14:30 | Interviews | Selected personnel |
| 15:30 | Auditor caucus | Audit team |
| 16:00 | Closing meeting | All |

PREPARATION CHECKLIST
[ ] Previous audit reports reviewed
[ ] Procedures reviewed
[ ] Checklist prepared
[ ] Auditees notified
[ ] Resources arranged
```

### Audit Checklist Template

```
INTERNAL AUDIT CHECKLIST

Audit Number: IA-[YYYY]-[NNN]
Process: [Process Name]
Auditor: [Name]
Date: [Date]

INSTRUCTIONS
C = Conforming, NC = Nonconforming, OBS = Observation, N/A = Not Applicable

CHECKLIST
| # | Requirement | Reference | Evidence Reviewed | Finding | Notes |
|---|-------------|-----------|-------------------|---------|-------|
| 1 | Is the procedure current and approved? | 4.2.3 | [Evidence] | C/NC/OBS | |
| 2 | Are personnel trained on the procedure? | 6.2 | [Evidence] | C/NC/OBS | |
| 3 | Are records maintained as required? | 4.2.4 | [Evidence] | C/NC/OBS | |
| 4 | Is the process performed as documented? | 4.1 | [Evidence] | C/NC/OBS | |
| 5 | Are monitoring activities performed? | 8.2.5 | [Evidence] | C/NC/OBS | |

INTERVIEWS CONDUCTED
| Person | Role | Topics Discussed |
|--------|------|------------------|
| [Name] | [Role] | [Topics] |

DOCUMENTS REVIEWED
| Document # | Title | Rev | Findings |
|------------|-------|-----|----------|
| [Number] | [Title] | [Rev] | [Findings] |

RECORDS SAMPLED
| Record Type | Sample Size | Sample IDs | Findings |
|-------------|-------------|------------|----------|
| [Type] | [N] | [IDs] | [Findings] |

AUDITOR SIGNATURE: _________________ Date: _______
```

### Audit Report

```
INTERNAL AUDIT REPORT

Audit Number: IA-[YYYY]-[NNN]
Report Date: [Date]
Report Status: [ ] Draft [ ] Final

AUDIT SUMMARY
Audit Date(s): [Date(s)]
Process/Area: [Name]
ISO Clauses Covered: [List]
Lead Auditor: [Name]
Audit Team: [Names]

AUDIT SCOPE
[Description of scope]

AUDIT OBJECTIVES
[List objectives]

EXECUTIVE SUMMARY
[Brief summary of audit results]

FINDINGS SUMMARY
| Type | Count |
|------|-------|
| Major Nonconformity | [N] |
| Minor Nonconformity | [N] |
| Observation | [N] |
| Opportunity for Improvement | [N] |

DETAILED FINDINGS

FINDING 1
Number: IA-[YYYY]-[NNN]-F01
Classification: [ ] Major NC [ ] Minor NC [ ] Observation [ ] OFI
Requirement: [Clause/requirement reference]
Statement: [Objective description of finding]
Evidence: [Evidence supporting finding]
Auditee Response Due: [Date]

[Repeat for each finding]

POSITIVE OBSERVATIONS
[List areas of good practice observed]

CONCLUSION
[Overall conclusion on process effectiveness]

REPORT DISTRIBUTION
| Name | Role | Date |
|------|------|------|
| [Name] | Process Owner | [Date] |
| [Name] | QA Manager | [Date] |
| [Name] | Management Rep | [Date] |

APPROVALS
Lead Auditor: _________________ Date: _______
QA Manager: _________________ Date: _______
```

---

## CAPA Templates

### CAPA Request Form

```
CORRECTIVE AND PREVENTIVE ACTION REQUEST

CAPA Number: CAPA-[YYYY]-[NNN]
Date Opened: [Date]
Initiated By: [Name]

CAPA TYPE
[ ] Corrective Action (response to existing nonconformity)
[ ] Preventive Action (prevent potential nonconformity)

SOURCE
[ ] Customer complaint: Reference #_______
[ ] Internal audit: Audit #_______
[ ] External audit: Audit #_______
[ ] Nonconformity: NC #_______
[ ] Process deviation
[ ] Management review action
[ ] Trend analysis
[ ] Risk assessment
[ ] Other: _______

CLASSIFICATION
Severity: [ ] Critical [ ] Major [ ] Minor
Regulatory Reportable: [ ] Yes [ ] No

PROBLEM DESCRIPTION
[Detailed description of the problem or potential problem]

IMMEDIATE CONTAINMENT (if applicable)
Actions Taken: [Description]
Date: [Date]
Responsible: [Name]

ASSIGNMENT
Process Owner: [Name]
CAPA Owner: [Name]
Due Date for Root Cause: [Date]
Target Closure Date: [Date]

APPROVAL TO PROCEED
Approved By: _________________ Date: _______
```

### Root Cause Analysis Record

```
ROOT CAUSE ANALYSIS

CAPA Number: CAPA-[YYYY]-[NNN]
Analysis Date: [Date]
Analyst: [Name]

PROBLEM STATEMENT
[Clear, specific statement of the problem]

INVESTIGATION TEAM
| Name | Role | Contribution |
|------|------|--------------|
| [Name] | [Role] | [Area of expertise] |

INVESTIGATION METHOD
[ ] 5 Why Analysis
[ ] Fishbone Diagram
[ ] Fault Tree Analysis
[ ] Human Factors Analysis
[ ] Other: _______

INVESTIGATION DETAILS

5 WHY ANALYSIS
Why 1: [First why]
Answer: [Answer]
Why 2: [Second why based on answer]
Answer: [Answer]
Why 3: [Third why based on answer]
Answer: [Answer]
Why 4: [Fourth why based on answer]
Answer: [Answer]
Why 5: [Fifth why based on answer]
Answer: [Answer]

ROOT CAUSE STATEMENT
[Clear statement of identified root cause]

ROOT CAUSE CATEGORY
[ ] Process/Procedure
[ ] Training/Competency
[ ] Equipment/Material
[ ] Design
[ ] Human Error
[ ] Communication
[ ] Management System
[ ] External Factor

CONTRIBUTING FACTORS
[List any contributing factors]

EVIDENCE SUPPORTING ROOT CAUSE
[List evidence]

APPROVAL
Analysis By: _________________ Date: _______
Reviewed By: _________________ Date: _______
```

### CAPA Action Plan

```
CAPA ACTION PLAN

CAPA Number: CAPA-[YYYY]-[NNN]
Root Cause: [Brief statement]
Plan Date: [Date]
Plan Owner: [Name]

CORRECTIVE/PREVENTIVE ACTIONS

Action 1:
Description: [Detailed action description]
Responsible: [Name]
Due Date: [Date]
Resources Required: [Resources]
Success Criteria: [How completion verified]

Action 2:
Description: [Detailed action description]
Responsible: [Name]
Due Date: [Date]
Resources Required: [Resources]
Success Criteria: [How completion verified]

[Continue for additional actions]

RELATED CHANGES
Documents Affected: [List]
Training Required: [Description]
Process Changes: [Description]
Equipment Changes: [Description]

RISK ASSESSMENT
Residual Risk After Implementation: [ ] High [ ] Medium [ ] Low
Justification: [Explanation]

APPROVAL
Plan Developed By: _________________ Date: _______
Approved By: _________________ Date: _______
```

### CAPA Effectiveness Verification

```
CAPA EFFECTIVENESS VERIFICATION

CAPA Number: CAPA-[YYYY]-[NNN]
Verification Date: [Date]
Verified By: [Name]

ACTIONS COMPLETED
| Action | Completion Date | Evidence |
|--------|-----------------|----------|
| [Action 1] | [Date] | [Reference] |
| [Action 2] | [Date] | [Reference] |

EFFECTIVENESS CRITERIA
[Criteria established during action planning]

VERIFICATION METHOD
[ ] Data analysis (trends, metrics)
[ ] Process audit
[ ] Record review
[ ] Product inspection
[ ] Customer feedback review
[ ] Other: _______

VERIFICATION PERIOD
From: [Date] To: [Date]

VERIFICATION RESULTS
[Detailed results of verification activities]

DATA/EVIDENCE REVIEWED
| Data Type | Period | Result |
|-----------|--------|--------|
| [Type] | [Period] | [Result] |

EFFECTIVENESS CONCLUSION
[ ] Effective - Root cause eliminated, problem resolved
[ ] Partially Effective - Improvement noted, additional action needed
[ ] Not Effective - Problem persists, reopen CAPA

If not effective, describe additional actions:
[Description]

CAPA CLOSURE
[ ] Approved for closure
[ ] Not approved - additional action required

Verified By: _________________ Date: _______
Approved By: _________________ Date: _______
```

---

## Supplier Management Templates

### Approved Supplier List

```
APPROVED SUPPLIER LIST

Organization: [Company Name]
Last Updated: [Date]
Maintained By: [Name]

| Supplier | Supplier # | Category | Products/Services | Status | Qualification Date | Next Review |
|----------|-----------|----------|-------------------|--------|-------------------|-------------|
| [Name] | SUP-001 | A | [Products] | Approved | [Date] | [Date] |
| [Name] | SUP-002 | B | [Products] | Conditional | [Date] | [Date] |

Category:
  A = Critical (affects safety/performance)
  B = Major (affects quality)
  C = Minor (indirect impact)

Status:
  Approved = Full use authorized
  Conditional = Limited use, monitoring
  Probation = Performance issues, enhanced monitoring
  Disqualified = Use not authorized

Revision History:
| Rev | Date | Change | Approved By |
|-----|------|--------|-------------|
| 01 | [Date] | Initial release | [Name] |
```

### Supplier Evaluation Form

```
SUPPLIER EVALUATION

Supplier Name: [Name]
Supplier Number: [Number]
Evaluation Date: [Date]
Evaluated By: [Name]
Evaluation Type: [ ] Initial [ ] Periodic [ ] For Cause

SUPPLIER INFORMATION
Address: [Address]
Contact: [Name, Title]
Phone: [Phone]
Email: [Email]
Products/Services: [Description]

PROPOSED CATEGORY
[ ] A - Critical (affects safety/performance)
[ ] B - Major (affects quality)
[ ] C - Minor (indirect impact)

EVALUATION CRITERIA

1. QUALITY MANAGEMENT SYSTEM (30 points max)
[ ] ISO 13485 Certified (30 pts)
[ ] ISO 9001 Certified (20 pts)
[ ] Documented QMS (10 pts)
[ ] No formal QMS (0 pts)
Score: ___/30

2. QUALITY HISTORY (25 points max)
Reject Rate: ___% (0-1% = 25 pts, 1-3% = 15 pts, >3% = 0 pts)
Score: ___/25

3. DELIVERY PERFORMANCE (20 points max)
On-Time Delivery: ___% (>95% = 20 pts, 90-95% = 10 pts, <90% = 0 pts)
Score: ___/20

4. TECHNICAL CAPABILITY (15 points max)
[ ] Exceeds requirements (15 pts)
[ ] Meets requirements (10 pts)
[ ] Marginally meets (5 pts)
Score: ___/15

5. FINANCIAL STABILITY (10 points max)
[ ] Strong (10 pts)
[ ] Adequate (5 pts)
[ ] Questionable (0 pts)
Score: ___/10

TOTAL SCORE: ___/100

QUALIFICATION DECISION
>80 = Approved
60-80 = Conditional (monitoring required)
<60 = Not Approved

Decision: [ ] Approved [ ] Conditional [ ] Not Approved

APPROVAL
Evaluated By: _________________ Date: _______
QA Approval: _________________ Date: _______
```

### Supplier Performance Scorecard

```
SUPPLIER PERFORMANCE SCORECARD

Supplier: [Name]
Supplier #: [Number]
Period: [Q1/Q2/Q3/Q4] [Year]
Prepared By: [Name]

PERFORMANCE METRICS

1. QUALITY (40% weight)
Total Lots Received: [N]
Lots Rejected: [N]
Accept Rate: ___% Target: >98%
Score: ___/40

2. DELIVERY (30% weight)
Total Orders: [N]
On-Time Deliveries: [N]
On-Time Rate: ___% Target: >95%
Score: ___/30

3. RESPONSIVENESS (15% weight)
Issues Reported: [N]
Resolved <5 days: [N]
Response Rate: ___% Target: >90%
Score: ___/15

4. DOCUMENTATION (15% weight)
CoC Required: [N]
CoC Complete: [N]
Documentation Rate: ___% Target: 100%
Score: ___/15

TOTAL SCORE: ___/100

PERFORMANCE TREND
| Period | Quality | Delivery | Response | Docs | Total |
|--------|---------|----------|----------|------|-------|
| Q1 | | | | | |
| Q2 | | | | | |
| Q3 | | | | | |
| Q4 | | | | | |

ISSUES/CONCERNS
[List any quality or delivery issues during period]

ACTIONS REQUIRED
[ ] None - Performance acceptable
[ ] Enhanced monitoring
[ ] Supplier corrective action request
[ ] Supplier audit
[ ] Consider alternative supplier

NEXT REVIEW: [Date]

Prepared By: _________________ Date: _______
Reviewed By: _________________ Date: _______
```

---

## Training Templates

### Training Record

```
EMPLOYEE TRAINING RECORD

Employee Name: [Name]
Employee ID: [ID]
Department: [Department]
Job Title: [Title]
Date of Hire: [Date]

REQUIRED TRAINING
| Training | Requirement | Initial Date | Last Date | Next Due | Status |
|----------|-------------|--------------|-----------|----------|--------|
| ISO 13485 Awareness | Initial + Annual | [Date] | [Date] | [Date] | Current |
| Document Control | Initial + On Change | [Date] | [Date] | [Date] | Current |
| CAPA Procedure | Initial + On Change | [Date] | [Date] | [Date] | Due |
| Job-Specific | Per competency matrix | [Date] | [Date] | [Date] | Current |

TRAINING HISTORY
| Date | Training | Method | Duration | Trainer | Assessment | Result |
|------|----------|--------|----------|---------|------------|--------|
| [Date] | [Title] | Classroom | 2 hrs | [Name] | Written test | Pass |
| [Date] | [Title] | OJT | 4 hrs | [Name] | Observation | Pass |

COMPETENCY VERIFICATION
| Competency | Method | Date | Verified By | Result |
|------------|--------|------|-------------|--------|
| [Skill] | Observation | [Date] | [Name] | Qualified |
| [Skill] | Test | [Date] | [Name] | Qualified |

Employee Signature: _________________ Date: _______
Supervisor Signature: _________________ Date: _______
```

### Training Attendance Record

```
TRAINING ATTENDANCE RECORD

Training Title: [Title]
Training Date: [Date]
Trainer: [Name]
Location: [Location]
Duration: [Hours]

TRAINING CONTENT
[Brief description of content covered]

ATTENDEES
| Name | Employee ID | Department | Signature | Assessment Result |
|------|-------------|------------|-----------|-------------------|
| [Name] | [ID] | [Dept] | | Pass/Fail |
| [Name] | [ID] | [Dept] | | Pass/Fail |

ASSESSMENT METHOD
[ ] Written test (attach copy)
[ ] Practical demonstration
[ ] Verbal Q&A
[ ] Observation
[ ] N/A

TRAINING MATERIALS
[ ] Presentation: [Reference]
[ ] Procedure: [Reference]
[ ] Other: [Reference]

Trainer Signature: _________________ Date: _______
Training Coordinator: _________________ Date: _______
```

---

## Nonconformity Templates

### Nonconformity Report

```
NONCONFORMITY REPORT

NC Number: NC-[YYYY]-[NNN]
Date Identified: [Date]
Identified By: [Name]

NONCONFORMITY TYPE
[ ] Product [ ] Process [ ] Document [ ] System

NONCONFORMITY SOURCE
[ ] Incoming inspection
[ ] In-process inspection
[ ] Final inspection
[ ] Customer complaint
[ ] Internal audit
[ ] External audit
[ ] Other: _______

PRODUCT IDENTIFICATION (if applicable)
Product Name: [Name]
Part Number: [Number]
Lot/Batch: [Number]
Quantity Affected: [N]

NONCONFORMITY DESCRIPTION
[Detailed, objective description of the nonconformity]

REQUIREMENT
[Reference to requirement that was not met]

CONTAINMENT ACTION
Action Taken: [Description]
Quantity Contained: [N]
Location: [Location]
Date: [Date]
By: [Name]

DISPOSITION
[ ] Use As Is - Justification: _______
[ ] Rework - Per procedure: _______
[ ] Scrap - Method: _______
[ ] Return to Supplier - RMA #: _______
[ ] Other: _______

Disposition By: [Name]
Disposition Date: [Date]

CAPA REQUIRED?
[ ] Yes - CAPA #: _______
[ ] No - Justification: _______

CLOSURE
All actions complete: [ ] Yes
NC Closed By: _________________ Date: _______
QA Approval: _________________ Date: _______
```

### Material Review Board Record

```
MATERIAL REVIEW BOARD (MRB) RECORD

MRB Number: MRB-[YYYY]-[NNN]
Date: [Date]
NC Reference: NC-[YYYY]-[NNN]

NONCONFORMING MATERIAL
Product: [Name]
Part Number: [Number]
Lot/Batch: [Number]
Quantity: [N]

NONCONFORMITY DESCRIPTION
[Description from NC report]

MRB PARTICIPANTS
| Name | Role | Signature |
|------|------|-----------|
| [Name] | QA Representative | |
| [Name] | Engineering | |
| [Name] | Production | |
| [Name] | Other | |

DISPOSITION OPTIONS CONSIDERED
1. Use As Is
   Technical Justification: [Justification]
   Risk Assessment: [Assessment]

2. Rework
   Procedure: [Reference]
   Feasibility: [Assessment]

3. Scrap
   Cost Impact: [Amount]

MRB DECISION
[ ] Use As Is - Customer notification required: [ ] Yes [ ] No
[ ] Rework per: [Procedure reference]
[ ] Scrap
[ ] Return to Supplier

RATIONALE
[Detailed rationale for decision]

APPROVALS
| Role | Name | Signature | Date |
|------|------|-----------|------|
| QA | [Name] | | [Date] |
| Engineering | [Name] | | [Date] |
| Production | [Name] | | [Date] |

FOLLOW-UP ACTIONS
[ ] CAPA initiated: CAPA-_______
[ ] Customer notified: Date: _______
[ ] Supplier notified: Date: _______
[ ] Other: _______
```
