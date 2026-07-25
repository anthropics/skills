# 21 CFR Part 11 Compliance Guide

Electronic records and electronic signatures compliance for FDA-regulated systems.

---

## Table of Contents

- [Part 11 Overview](#part-11-overview)
- [Electronic Record Requirements](#electronic-record-requirements)
- [Electronic Signature Requirements](#electronic-signature-requirements)
- [System Controls](#system-controls)
- [Validation Requirements](#validation-requirements)
- [Compliance Checklist](#compliance-checklist)

---

## Part 11 Overview

### Scope and Applicability

21 CFR Part 11 applies to electronic records and signatures used to meet FDA predicate rule requirements.

| Applies To | Does Not Apply To |
|------------|-------------------|
| Records required by FDA regulations | Paper records |
| Records submitted to FDA | Internal documents not required by regulation |
| Electronic signatures on required records | Digital communication (email) for general purposes |
| Systems creating/maintaining regulated records | Non-regulated systems |

### Key Terms

| Term | Definition |
|------|------------|
| Electronic Record | Any combination of text, graphics, data in digital form |
| Electronic Signature | Computer data compilation intended as legally binding signature |
| Digital Signature | Electronic signature based on cryptographic methods |
| Closed System | Environment with controlled access by responsible persons |
| Open System | Environment with uncontrolled access |
| Audit Trail | Secure, computer-generated, time-stamped record |

### Predicate Rules

Part 11 does not create new record requirements. It governs HOW records are maintained when electronic:

| Predicate Rule | Record Type |
|----------------|-------------|
| 21 CFR 820 (QMSR — incorporates ISO 13485:2016 by reference since 2026-02-02; formerly the QSR) | Device Master Records, Device History Records |
| 21 CFR 211 (cGMP) | Batch records, laboratory records |
| 21 CFR 58 (GLP) | Study records, raw data |
| 21 CFR 11.10(e) | Records required to be maintained |

---

## Electronic Record Requirements

### General Requirements (§11.10)

Closed systems must implement controls including:

1. **System Validation** - Accuracy, reliability, consistent intended performance
2. **Record Generation** - Accurate and complete copies in human-readable form
3. **Record Protection** - Throughout retention period
4. **Access Control** - Limit system access to authorized individuals
5. **Audit Trail** - Secure, computer-generated, time-stamped record
6. **Operational Checks** - Enforce permitted sequencing of steps
7. **Authority Checks** - Restrict functions to authorized individuals
8. **Device Checks** - Determine validity of input/output devices
9. **Training** - Personnel education and experience
10. **Documentation** - Written policies and accountability

### Audit Trail Requirements

| Requirement | Implementation |
|-------------|----------------|
| Secure | Cannot be modified or deleted by users |
| Computer-generated | System creates automatically, not manually entered |
| Time-stamped | Date and time of each action recorded |
| Independent | Stored separately from application data |
| Original values | Previous values retained when modified |
| Who, what, when | User identity, action taken, date/time |
| Reason for change | Where required by predicate rule |

### Audit Trail Entries

| Event Type | Data Captured |
|------------|---------------|
| Record Creation | User, date/time, initial values |
| Record Modification | User, date/time, old value, new value, reason |
| Record Deletion | User, date/time, reason (if permitted) |
| Login/Logout | User, date/time, success/failure |
| Signature Application | User, date/time, signature meaning |
| Failed Access | User attempted, date/time, reason |

### Record Copy Requirements

Must be able to generate accurate and complete copies:

| Format | Requirement |
|--------|-------------|
| Electronic | Export in standard format (PDF, XML) |
| Paper | Human-readable printout |
| FDA Inspection | Provide copies upon request |
| Audit Trail | Include with record or separately |

---

## Electronic Signature Requirements

### General Requirements (§11.50, 11.100)

| Requirement | Implementation |
|-------------|----------------|
| Unique to individual | Not shared between persons |
| Not reused | Identifier not assigned to another person |
| Identity verification | Verify identity before assignment |
| Certification | Certify to FDA that signatures are binding |

### Signature Components (§11.200)

| Type | Components Required |
|------|---------------------|
| Non-biometric | At least two distinct identification components |
| - First signing | Both components (user ID + password) |
| - Subsequent signings | At least one component within controlled session |
| Biometric | Biometric designed for individual identification |

### Signature Manifestations (§11.50)

Electronic signatures must include:

| Element | Requirement |
|---------|-------------|
| Printed name | Full name of signer |
| Date and time | When signature was applied |
| Meaning | Purpose of signature (e.g., review, approval, responsibility) |

### Signature/Record Linking (§11.70)

| Requirement | Implementation |
|-------------|----------------|
| Linked to record | Signature cannot be excised, copied, or transferred |
| Cannot falsify | Technical controls prevent counterfeiting |
| Cannot repudiate | Signer cannot deny signing |

### Signature Certification

Organizations must submit certification to FDA (§11.100(c)):

```
SAMPLE CERTIFICATION LETTER

[Date]

Food and Drug Administration
[Appropriate Center Address]

Subject: Electronic Signature Certification

[Company Name] hereby certifies that all electronic signatures
used in our FDA-regulated systems are the legally binding
equivalent of traditional handwritten signatures.

This certification is made in accordance with 21 CFR Part 11,
Section 11.100(c).

Sincerely,
[Authorized Representative]
[Title]
```

---

## System Controls

### Administrative Controls

| Control | Implementation |
|---------|----------------|
| Written policies | SOPs for electronic records and signatures |
| Roles and responsibilities | Defined system access roles |
| Training program | Initial and periodic training |
| Periodic review | Regular assessment of controls |
| Accountability | Individual responsibility for actions |

### Operational Controls

| Control | Implementation |
|---------|----------------|
| Sequence enforcement | System enforces step order |
| Time limits | Session timeout after inactivity |
| Event logging | All significant events recorded |
| Error handling | System prevents invalid operations |
| Backup/recovery | Regular backup and tested recovery |

### Technical Controls

| Control | Implementation |
|---------|----------------|
| User authentication | Unique ID + password minimum |
| Password complexity | Minimum length, character requirements |
| Password expiration | Periodic change requirement |
| Account lockout | Lock after failed attempts |
| Access control | Role-based permissions |
| Encryption | Data in transit and at rest |

### Password Requirements

| Requirement | Specification |
|-------------|---------------|
| Minimum length | 8 characters minimum |
| Complexity | Upper, lower, number, special character |
| History | Cannot reuse last 12 passwords |
| Expiration | Maximum 90 days |
| Lockout | 5 failed attempts, 30-minute lockout |
| Initial password | Must change on first login |

### Session Controls

| Control | Specification |
|---------|---------------|
| Inactivity timeout | Maximum 15 minutes |
| Session duration | Maximum 8 hours |
| Concurrent sessions | Limit or prevent |
| Re-authentication | Required for sensitive operations |

---

## Validation Requirements

### Validation Approach

| Phase | Activities |
|-------|------------|
| Planning | Validation plan, requirements, risk assessment |
| Specification | User requirements, functional specifications |
| Configuration | System setup, security configuration |
| Testing | IQ, OQ, PQ protocols and execution |
| Release | Validation summary report, release approval |
| Maintenance | Change control, periodic review |

### Validation Documentation

| Document | Purpose |
|----------|---------|
| Validation Plan | Scope, approach, responsibilities, schedule |
| User Requirements | What system must do (business requirements) |
| Functional Specification | How system will meet requirements |
| Design Specification | Technical implementation details |
| Test Protocols | IQ, OQ, PQ test procedures |
| Test Results | Executed protocols with evidence |
| Traceability Matrix | Requirements to test coverage |
| Validation Summary Report | Overall validation conclusion |

### Testing Categories

**Installation Qualification (IQ):**
- System installed per specifications
- Hardware and software inventory
- Configuration documentation

**Operational Qualification (OQ):**
- Functions operate as specified
- Audit trail verification
- Security control testing
- Error handling verification

**Performance Qualification (PQ):**
- System performs in production environment
- User acceptance testing
- Integration testing
- Load/stress testing (if applicable)

### Part 11 Specific Testing

| Test Area | Verification |
|-----------|--------------|
| Audit trail | All CRUD operations recorded correctly |
| Access control | Role permissions enforced |
| Electronic signatures | Signature components and linking |
| Record integrity | Data cannot be altered without detection |
| Backup/restore | Records restored accurately |
| Session controls | Timeout and lockout function |
| Password controls | Complexity and expiration enforced |

---

## Compliance Checklist

### System Assessment Checklist

**Administrative Controls:**
- [ ] Written policies for electronic records and signatures
- [ ] Defined roles and responsibilities
- [ ] Training program documented and executed
- [ ] Periodic review schedule established
- [ ] Accountability measures in place

**Access Controls:**
- [ ] Unique user identification for each person
- [ ] User IDs not shared or reassigned
- [ ] Password complexity requirements enforced
- [ ] Password expiration implemented
- [ ] Account lockout after failed attempts
- [ ] Role-based access control implemented
- [ ] Access periodically reviewed

**Audit Trail:**
- [ ] All record creation captured
- [ ] All record modifications captured
- [ ] Previous values retained
- [ ] User identity recorded
- [ ] Date/time stamp on all entries
- [ ] Audit trail secure from modification
- [ ] Audit trail available for review

**Electronic Signatures:**
- [ ] Signatures unique to individual
- [ ] At least two identification components
- [ ] Signature manifestation includes name, date/time, meaning
- [ ] Signatures linked to records
- [ ] Certification letter submitted to FDA

**Record Management:**
- [ ] Accurate copies can be generated
- [ ] Human-readable format available
- [ ] Records protected throughout retention
- [ ] Backup and recovery tested

**System Controls:**
- [ ] Session timeout implemented
- [ ] Operational sequence enforcement
- [ ] Input/output device validation
- [ ] Error handling documented

**Validation:**
- [ ] System validated for intended use
- [ ] Validation documentation complete
- [ ] Change control procedures in place
- [ ] Periodic review conducted

### Gap Assessment Template

```
PART 11 GAP ASSESSMENT

System: [System Name]
Assessment Date: [Date]
Assessor: [Name]

| Requirement | §11 Reference | Current State | Gap | Remediation | Priority |
|-------------|---------------|---------------|-----|-------------|----------|
| Audit trail | 11.10(e) | [Description] | [Y/N] | [Action] | [H/M/L] |
| Access control | 11.10(d) | [Description] | [Y/N] | [Action] | [H/M/L] |
| E-signatures | 11.50 | [Description] | [Y/N] | [Action] | [H/M/L] |

Summary:
- Total requirements assessed: [Number]
- Requirements met: [Number]
- Gaps identified: [Number]
- Remediation timeline: [Date]
```

### Periodic Review Schedule

| Review Type | Frequency | Scope |
|-------------|-----------|-------|
| Access review | Quarterly | User access appropriateness |
| Audit trail review | Monthly | Sample review of audit entries |
| Security review | Annually | Controls effectiveness |
| Validation review | Annually or on change | System still validated |
| Policy review | Annually | SOPs current and followed |

---

## Common Deficiencies

### FDA Warning Letter Themes

| Deficiency | Root Cause | Prevention |
|------------|------------|------------|
| Shared user accounts | Convenience over compliance | Enforce unique accounts |
| Inadequate audit trail | System limitation | Validate audit trail |
| Missing signatures | Process gap | Enforce signature workflow |
| Incomplete validation | Time/resource constraints | Plan adequate resources |
| No change control | Process not followed | Enforce change control |
| Password sharing | Culture issue | Training and enforcement |

### Remediation Priorities

| Priority | Deficiency Type | Timeline |
|----------|-----------------|----------|
| Critical | Audit trail missing/modifiable | Immediate |
| Critical | Signatures can be falsified | Immediate |
| High | Shared accounts in production | 30 days |
| High | Validation gaps | 60 days |
| Medium | Training gaps | 90 days |
| Low | Documentation gaps | 120 days |
