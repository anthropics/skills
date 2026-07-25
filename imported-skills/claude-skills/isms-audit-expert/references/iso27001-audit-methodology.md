# ISO 27001 ISMS Audit Methodology

Complete audit framework and procedures for Information Security Management System assessments.

---

## Table of Contents

- [Audit Program Structure](#audit-program-structure)
- [Pre-Audit Phase](#pre-audit-phase)
- [Audit Execution](#audit-execution)
- [Finding Classification](#finding-classification)
- [Certification Audit Support](#certification-audit-support)

---

## Audit Program Structure

### Annual Audit Schedule

| Quarter | Focus Area | Audit Type |
|---------|------------|------------|
| Q1 | Access Control, Cryptography | Internal |
| Q2 | Operations Security, Communications | Internal |
| Q3 | System Acquisition, Supplier Relations | Internal |
| Q4 | Full ISMS Review | Pre-certification |

### Risk-Based Scheduling

Prioritize audit frequency based on:
- Asset criticality and data classification
- Previous finding history
- Regulatory requirements
- Recent security incidents
- Organizational changes

**High Risk Areas (Quarterly):**
- Access management systems
- Cryptographic key management
- Incident response processes
- Third-party access controls

**Medium Risk Areas (Semi-Annual):**
- Change management
- Backup and recovery
- Physical security
- Security awareness training

**Lower Risk Areas (Annual):**
- Documentation management
- Asset inventory
- Business continuity planning

---

## Pre-Audit Phase

### Documentation Review Checklist

- [ ] ISMS scope statement and boundaries
- [ ] Information security policy (signed, current)
- [ ] Statement of Applicability (SoA)
- [ ] Risk assessment methodology and results
- [ ] Risk treatment plan
- [ ] Security objectives and metrics
- [ ] Previous audit reports and corrective actions

### Audit Plan Template

```
ISMS Audit Plan

Audit ID: ISMS-[YEAR]-[NUMBER]
Scope: [ISMS scope or specific controls]
Date: [Start] to [End]
Lead Auditor: [Name]
Audit Team: [Names]

Day 1:
  09:00 - Opening meeting
  10:00 - Document review (policies, SoA)
  14:00 - Interview: Information Security Manager

Day 2:
  09:00 - Technical control verification
  14:00 - Process observation

Day 3:
  09:00 - Remaining interviews
  14:00 - Finding consolidation
  16:00 - Closing meeting
```

### Auditor Independence

Verify before audit assignment:
- No operational responsibility for audited area
- No recent (12 months) involvement in audited processes
- No conflict of interest with auditees
- Required competencies documented

---

## Audit Execution

### Evidence Collection Methods

| Method | Use Case | Evidence Type |
|--------|----------|---------------|
| Document review | Policy verification | Screenshots, copies |
| Interviews | Process understanding | Notes, recordings |
| Observation | Operational checks | Photos, timestamps |
| Technical testing | Control effectiveness | System logs, reports |

### Interview Protocol

1. Introduce audit purpose and confidentiality
2. Explain interview will be documented
3. Ask open-ended questions about processes
4. Request evidence to support statements
5. Clarify any inconsistencies
6. Summarize key points before closing

### Sample Interview Questions

**For Security Managers:**
- Describe the risk assessment process
- How are security incidents reported and managed?
- What metrics track ISMS effectiveness?

**For System Administrators:**
- How is privileged access managed?
- Walk through the change management process
- Show backup verification records

**For End Users:**
- What security training have you received?
- How do you report suspicious activity?
- Describe the password policy requirements

### Control Testing Procedures

**Access Control (A.9):**
1. Request user access list for critical system
2. Verify access rights match job roles
3. Check for terminated user accounts
4. Test password policy enforcement
5. Verify MFA configuration

**Logging (A.12.4):**
1. Confirm logging enabled on systems in scope
2. Verify log retention meets policy
3. Check log protection from tampering
4. Review sample security event alerts

---

## Finding Classification

### Severity Levels

| Level | Definition | Response Time |
|-------|------------|---------------|
| Major Nonconformity | Failure of control, significant risk | 30 days corrective action |
| Minor Nonconformity | Isolated deviation, limited impact | 90 days corrective action |
| Observation | Improvement opportunity | Next audit cycle |
| Good Practice | Exceeds requirements | Document and share |

### Finding Documentation

```
Finding ID: ISMS-2025-001
Control Reference: A.9.2.3 - Management of privileged access
Severity: Major Nonconformity

Evidence:
- 15 shared admin accounts identified
- No approval records for privileged access
- Last access review: 18 months ago

Risk Impact:
- Unauthorized access to critical systems
- No accountability for admin actions
- Regulatory non-compliance

Root Cause:
- No defined process for privileged access management
- Insufficient tooling for access tracking

Recommendation:
- Implement PAM solution within 30 days
- Document and enforce privileged access process
- Conduct immediate access review
```

### Corrective Action Tracking

| Field | Content |
|-------|---------|
| Finding ID | Link to original finding |
| Root Cause | Why the nonconformity occurred |
| Corrective Action | Specific steps to address |
| Responsible Person | Named accountable party |
| Target Date | Completion deadline |
| Verification Method | How closure will be confirmed |
| Status | Open / In Progress / Closed |

---

## Certification Audit Support

### Stage 1 Audit Preparation

Ensure availability of:
- [ ] ISMS documentation (scope, policy, SoA)
- [ ] Risk assessment records
- [ ] Internal audit results from past 12 months
- [ ] Management review minutes
- [ ] Corrective action evidence

### Stage 2 Audit Preparation

- [ ] All Stage 1 findings addressed
- [ ] ISMS operational for minimum 3 months
- [ ] Evidence of control effectiveness
- [ ] Training and awareness records
- [ ] Incident response records (if any)

### Surveillance Audit Cycle

| Year | Quarter | Focus |
|------|---------|-------|
| Year 1 | Q2 | High-risk controls, Stage 2 findings |
| Year 1 | Q4 | Remaining controls sample |
| Year 2 | Q2 | Full surveillance |
| Year 2 | Q4 | Continual improvement evidence |
| Year 3 | Q2 | Re-certification preparation |

### Audit Findings Response Template

```
Subject: Response to Finding ISMS-2025-001

Finding: Major Nonconformity - Privileged Access Management

Root Cause Analysis:
[5 Whys or fishbone analysis results]

Corrective Action Plan:
1. [Action] - [Owner] - [Date]
2. [Action] - [Owner] - [Date]

Evidence of Correction:
- [Document/screenshot reference]

Preventive Measures:
- [Steps to prevent recurrence]

Verification Request: [Date auditor can verify]
```
