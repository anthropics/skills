# HIPAA Compliance Framework for Medical Devices

Complete guide to HIPAA requirements for medical device manufacturers and software developers.

---

## Table of Contents

- [HIPAA Overview](#hipaa-overview)
- [Privacy Rule Requirements](#privacy-rule-requirements)
- [Security Rule Requirements](#security-rule-requirements)
- [Medical Device Considerations](#medical-device-considerations)
- [Risk Assessment](#risk-assessment)
- [Implementation Specifications](#implementation-specifications)
- [Business Associate Agreements](#business-associate-agreements)
- [Breach Notification](#breach-notification)

---

## HIPAA Overview

### Applicability to Medical Devices

| Entity Type | HIPAA Applicability |
|-------------|---------------------|
| Healthcare providers | Covered Entity (CE) |
| Health plans | Covered Entity (CE) |
| Healthcare clearinghouses | Covered Entity (CE) |
| Device manufacturers | Business Associate (BA) if handling PHI |
| SaMD developers | Business Associate (BA) if handling PHI |
| Cloud service providers | Business Associate (BA) |

### Protected Health Information (PHI)

**PHI Definition:** Individually identifiable health information transmitted or maintained in any form.

**18 HIPAA Identifiers:**

```
1. Names
2. Geographic data (smaller than state)
3. Dates (except year) related to individual
4. Phone numbers
5. Fax numbers
6. Email addresses
7. Social Security numbers
8. Medical record numbers
9. Health plan beneficiary numbers
10. Account numbers
11. Certificate/license numbers
12. Vehicle identifiers
13. Device identifiers and serial numbers
14. Web URLs
15. IP addresses
16. Biometric identifiers
17. Full face photos
18. Any other unique identifying number
```

### Electronic PHI (ePHI)

PHI that is created, stored, transmitted, or received in electronic form. Most relevant for:
- Connected medical devices
- Medical device software (SaMD)
- Mobile health applications
- Cloud-based healthcare systems

---

## Privacy Rule Requirements

### Minimum Necessary Standard

**Principle:** Limit PHI access, use, and disclosure to the minimum necessary to accomplish the intended purpose.

**Implementation:**
- Role-based access controls
- Access audit logging
- Data segmentation
- Need-to-know policies

### Patient Rights

| Right | Device Implication |
|-------|---------------------|
| Access | Provide mechanism to view/export data |
| Amendment | Allow corrections to patient data |
| Accounting of disclosures | Log all PHI disclosures |
| Restriction requests | Support data sharing restrictions |
| Confidential communications | Secure communication channels |

### Use and Disclosure

**Permitted Uses:**
- Treatment, Payment, Healthcare Operations (TPO)
- With patient authorization
- Public health activities
- Required by law
- Health oversight activities

**Medical Device Context:**
- Device data for treatment: Permitted
- Data analytics by manufacturer: Requires BAA or de-identification
- Research use: Requires authorization or IRB waiver

---

## Security Rule Requirements

### Administrative Safeguards

#### Security Management Process (§164.308(a)(1))

**Required Specifications:**

```markdown
## Security Management Process

### Risk Analysis
- [ ] Identify systems with ePHI
- [ ] Document potential threats and vulnerabilities
- [ ] Assess likelihood and impact
- [ ] Document current controls
- [ ] Determine risk levels

### Risk Management
- [ ] Implement security measures
- [ ] Document residual risk
- [ ] Management approval

### Sanction Policy
- [ ] Define workforce sanctions
- [ ] Document enforcement procedures

### Information System Activity Review
- [ ] Define audit procedures
- [ ] Review logs regularly
- [ ] Document findings
```

#### Workforce Security (§164.308(a)(3))

| Specification | Type | Implementation |
|---------------|------|----------------|
| Authorization/supervision | Addressable | Access approval process |
| Workforce clearance | Addressable | Background checks |
| Termination procedures | Addressable | Access revocation |

#### Information Access Management (§164.308(a)(4))

**Access Control Elements:**
- Access authorization
- Access establishment and modification
- Unique user identification
- Automatic logoff

#### Security Awareness and Training (§164.308(a)(5))

**Training Topics:**
- Security reminders
- Protection from malicious software
- Login monitoring
- Password management

#### Security Incident Procedures (§164.308(a)(6))

**Incident Response Requirements:**
1. Identify and document incidents
2. Report security incidents
3. Respond to mitigate harmful effects
4. Document outcomes

#### Contingency Plan (§164.308(a)(7))

```markdown
## Contingency Plan Components

### Data Backup Plan (Required)
- Backup frequency: _____
- Backup verification: _____
- Off-site storage: _____

### Disaster Recovery Plan (Required)
- Recovery time objective: _____
- Recovery point objective: _____
- Recovery procedures: _____

### Emergency Mode Operation (Required)
- Critical functions: _____
- Manual procedures: _____
- Communication plan: _____

### Testing and Revision (Addressable)
- Test frequency: _____
- Last test date: _____
- Revision history: _____

### Applications and Data Criticality (Addressable)
- Critical systems: _____
- Priority recovery order: _____
```

### Physical Safeguards

#### Facility Access Controls (§164.310(a)(1))

| Specification | Type | Implementation |
|---------------|------|----------------|
| Contingency operations | Addressable | Physical access during emergency |
| Facility security plan | Addressable | Physical access policies |
| Access control/validation | Addressable | Visitor management |
| Maintenance records | Addressable | Physical maintenance logs |

#### Workstation Use (§164.310(b))

**Requirements:**
- Policies for workstation use
- Physical environment considerations
- Secure positioning
- Screen privacy

#### Workstation Security (§164.310(c))

**Physical Safeguards:**
- Cable locks
- Restricted areas
- Surveillance
- Clean desk policy

#### Device and Media Controls (§164.310(d)(1))

**Critical for Medical Devices:**

```markdown
## Device and Media Controls

### Disposal (Required)
- [ ] Wipe procedures for devices with ePHI
- [ ] Certificate of destruction
- [ ] Media sanitization per NIST 800-88

### Media Re-use (Required)
- [ ] Sanitization before re-use
- [ ] Verification of removal
- [ ] Documentation

### Accountability (Addressable)
- [ ] Hardware inventory
- [ ] Movement tracking
- [ ] Responsibility assignment

### Data Backup and Storage (Addressable)
- [ ] Retrievable copies
- [ ] Secure storage location
- [ ] Access controls on backup media
```

### Technical Safeguards

#### Access Control (§164.312(a)(1))

| Specification | Type | Implementation |
|---------------|------|----------------|
| Unique user identification | Required | Individual accounts |
| Emergency access | Required | Break-glass procedures |
| Automatic logoff | Addressable | Session timeout |
| Encryption and decryption | Addressable | At-rest encryption |

#### Audit Controls (§164.312(b))

**Audit Log Contents:**
- User identification
- Event type
- Date and time
- Success/failure
- Affected data

**Medical Device Considerations:**
- Log all access to patient data
- Protect logs from tampering
- Retain logs per policy (minimum 6 years)
- Real-time alerting for critical events

#### Integrity (§164.312(c)(1))

**ePHI Integrity Controls:**
- Hash verification
- Digital signatures
- Version control
- Change detection

#### Person or Entity Authentication (§164.312(d))

**Authentication Methods:**
- Passwords (strong requirements)
- Biometrics
- Hardware tokens
- Multi-factor authentication (recommended)

#### Transmission Security (§164.312(e)(1))

| Specification | Type | Implementation |
|---------------|------|----------------|
| Integrity controls | Addressable | TLS, message authentication |
| Encryption | Addressable | TLS 1.2+, AES-256 |

---

## Medical Device Considerations

### Connected Medical Device Security

**Data Flow Analysis:**

```
Device → Local Network → Internet → Cloud → EHR
  │           │            │         │       │
  └─ ePHI at rest    ePHI in transit    ePHI at rest
     Encrypt          Encrypt TLS       Encrypt + Access Control
```

### SaMD (Software as a Medical Device)

**HIPAA Requirements for SaMD:**
1. Encryption of stored patient data
2. Secure authentication
3. Audit logging
4. Access controls
5. Secure communication protocols
6. Backup and recovery
7. Incident response

### Mobile Medical Applications

**Additional Considerations:**
- Device loss/theft protection
- Remote wipe capability
- App sandboxing
- Secure data storage
- API security

### Cloud-Based Devices

**Cloud Provider Requirements:**
- BAA with cloud provider
- Data residency (US only for HIPAA)
- Encryption key management
- Audit log access
- Incident notification

---

## Risk Assessment

### HIPAA Risk Assessment Process

```
Step 1: Scope Definition
├── Identify systems with ePHI
├── Document data flows
└── Identify business associates

Step 2: Threat Identification
├── Natural threats (fire, flood)
├── Human threats (hackers, insiders)
├── Environmental threats (power, HVAC)
└── Technical threats (malware, system failure)

Step 3: Vulnerability Assessment
├── Administrative controls
├── Physical controls
├── Technical controls
└── Gap analysis

Step 4: Risk Analysis
├── Likelihood assessment
├── Impact assessment
├── Risk level determination
└── Risk prioritization

Step 5: Risk Treatment
├── Accept
├── Mitigate
├── Transfer
└── Avoid

Step 6: Documentation
├── Risk register
├── Risk management plan
└── Remediation tracking
```

### Risk Assessment Template

```markdown
## HIPAA Risk Assessment

### System Information
System Name: _____________________
System Owner: ____________________
Date: ___________________________

### Asset Inventory
| Asset | ePHI Type | Location | Classification |
|-------|-----------|----------|----------------|
|       |           |          |                |

### Threat Analysis
| Threat | Likelihood (1-5) | Impact (1-5) | Risk Score |
|--------|------------------|--------------|------------|
|        |                  |              |            |

### Vulnerability Assessment
| Safeguard Category | Gap Identified | Severity | Remediation |
|--------------------|----------------|----------|-------------|
| Administrative     |                |          |             |
| Physical           |                |          |             |
| Technical          |                |          |             |

### Risk Treatment Plan
| Risk | Treatment | Owner | Timeline | Status |
|------|-----------|-------|----------|--------|
|      |           |       |          |        |

### Approval
Risk Assessment Approved: _______________ Date: _______
Next Assessment Due: _______________
```

---

## Implementation Specifications

### Required vs. Addressable

**Required:** Must be implemented as specified

**Addressable:**
1. Implement as specified, OR
2. Implement alternative measure, OR
3. Not implement if not reasonable and appropriate (document rationale)

### Implementation Status Matrix

| Safeguard | Specification | Type | Status | Evidence |
|-----------|---------------|------|--------|----------|
| §164.308(a)(1)(ii)(A) | Risk analysis | R | ☐ | |
| §164.308(a)(1)(ii)(B) | Risk management | R | ☐ | |
| §164.308(a)(3)(ii)(A) | Authorization/supervision | A | ☐ | |
| §164.308(a)(5)(ii)(A) | Security reminders | A | ☐ | |
| §164.310(a)(2)(i) | Contingency operations | A | ☐ | |
| §164.310(d)(2)(i) | Disposal | R | ☐ | |
| §164.312(a)(2)(i) | Unique user ID | R | ☐ | |
| §164.312(a)(2)(ii) | Emergency access | R | ☐ | |
| §164.312(a)(2)(iv) | Encryption (at rest) | A | ☐ | |
| §164.312(e)(2)(ii) | Encryption (transit) | A | ☐ | |

---

## Business Associate Agreements

### When Required

BAA required when business associate:
- Creates, receives, maintains, or transmits PHI
- Provides services involving PHI use/disclosure

### BAA Requirements

**Required Provisions:**
1. Permitted and required uses of PHI
2. Subcontractor requirements
3. Appropriate safeguards
4. Breach notification
5. Termination provisions
6. Return or destruction of PHI

### Medical Device Manufacturer BAA Template

```markdown
## Business Associate Agreement

This Agreement is entered into as of [Date] between:

COVERED ENTITY: [Healthcare Provider/Plan Name]
BUSINESS ASSOCIATE: [Device Manufacturer Name]

### 1. Definitions
[Standard HIPAA definitions]

### 2. Obligations of Business Associate

Business Associate agrees to:

a) Not use or disclose PHI other than as permitted
b) Use appropriate safeguards to prevent improper use/disclosure
c) Report any security incident or breach
d) Ensure subcontractors agree to same restrictions
e) Make PHI available for individual access
f) Make PHI available for amendment
g) Document and make available disclosures
h) Make internal practices available to HHS
i) Return or destroy PHI at termination

### 3. Permitted Uses and Disclosures

Business Associate may:
a) Use PHI for device operation and maintenance
b) Use PHI for quality improvement
c) De-identify PHI per HIPAA standards
d) Create aggregate data
e) Report to FDA as required

### 4. Security Requirements

Business Associate shall implement:
a) Administrative safeguards per §164.308
b) Physical safeguards per §164.310
c) Technical safeguards per §164.312

### 5. Breach Notification

Business Associate shall:
a) Report breaches within [60 days/contractual period]
b) Provide information for breach notification
c) Mitigate harmful effects

### 6. Term and Termination
[Standard termination provisions]

### Signatures

COVERED ENTITY: _________________ Date: _______
BUSINESS ASSOCIATE: _____________ Date: _______
```

---

## Breach Notification

### Breach Definition

**Breach:** Acquisition, access, use, or disclosure of unsecured PHI in a manner not permitted that compromises security or privacy.

**Exceptions:**
1. Unintentional acquisition by workforce member acting in good faith
2. Inadvertent disclosure between authorized persons
3. Good faith belief that unauthorized person couldn't retain information

### Risk Assessment for Breach

**Factors to Consider:**
1. Nature and extent of PHI involved
2. Unauthorized person who received PHI
3. Whether PHI was actually acquired/viewed
4. Extent to which risk has been mitigated

### Notification Requirements

| Audience | Timing | Method |
|----------|--------|--------|
| Individuals | 60 days from discovery | First-class mail or email |
| HHS | 60 days (if >500) | HHS breach portal |
| HHS | Annual (if <500) | Annual report |
| Media | 60 days (if >500 in state) | Prominent media outlet |

### Breach Response Procedure

```markdown
## Breach Response Procedure

### Phase 1: Detection and Containment (Immediate)
- [ ] Identify scope of breach
- [ ] Contain breach (stop ongoing access)
- [ ] Preserve evidence
- [ ] Notify incident response team
- [ ] Document timeline

### Phase 2: Investigation (1-14 days)
- [ ] Determine what PHI was involved
- [ ] Identify affected individuals
- [ ] Assess risk of harm
- [ ] Document investigation findings

### Phase 3: Risk Assessment (15-30 days)
- [ ] Apply four-factor risk assessment
- [ ] Determine if notification required
- [ ] Document decision rationale

### Phase 4: Notification (Within 60 days)
- [ ] Prepare individual notification letters
- [ ] Submit to HHS (if required)
- [ ] Media notification (if required)
- [ ] Retain copies of notifications

### Phase 5: Remediation (Ongoing)
- [ ] Implement corrective actions
- [ ] Update policies and procedures
- [ ] Train workforce
- [ ] Monitor for additional impact
```

### Breach Notification Content

**Individual Notification Must Include:**
1. Description of what happened
2. Types of PHI involved
3. Steps individuals should take
4. What entity is doing to investigate
5. What entity is doing to prevent future breaches
6. Contact information for questions

---

## Compliance Checklist

### Administrative Safeguards Checklist

```markdown
## Administrative Safeguards

- [ ] Security Management Process
  - [ ] Risk analysis completed and documented
  - [ ] Risk management plan in place
  - [ ] Sanction policy documented
  - [ ] Information system activity review conducted

- [ ] Assigned Security Responsibility
  - [ ] Security Officer designated
  - [ ] Contact information documented

- [ ] Workforce Security
  - [ ] Authorization procedures
  - [ ] Background checks (if applicable)
  - [ ] Termination procedures

- [ ] Information Access Management
  - [ ] Access authorization policies
  - [ ] Access establishment procedures
  - [ ] Access modification procedures

- [ ] Security Awareness and Training
  - [ ] Training program established
  - [ ] Security reminders distributed
  - [ ] Protection from malicious software training
  - [ ] Password management training

- [ ] Security Incident Procedures
  - [ ] Incident response plan
  - [ ] Incident documentation procedures
  - [ ] Reporting mechanisms

- [ ] Contingency Plan
  - [ ] Data backup plan
  - [ ] Disaster recovery plan
  - [ ] Emergency mode operation plan
  - [ ] Testing and revision procedures
```

### Technical Safeguards Checklist

```markdown
## Technical Safeguards

- [ ] Access Control
  - [ ] Unique user identification
  - [ ] Emergency access procedure
  - [ ] Automatic logoff
  - [ ] Encryption (at rest)

- [ ] Audit Controls
  - [ ] Audit logging implemented
  - [ ] Log review procedures
  - [ ] Log retention policy

- [ ] Integrity
  - [ ] Mechanism to authenticate ePHI
  - [ ] Integrity controls in place

- [ ] Authentication
  - [ ] Person/entity authentication
  - [ ] Strong password policy

- [ ] Transmission Security
  - [ ] Integrity controls (in transit)
  - [ ] Encryption (TLS 1.2+)
```

---

## Quick Reference

### Common HIPAA Violations

| Violation | Prevention |
|-----------|------------|
| Unauthorized access | Role-based access, MFA |
| Lost/stolen devices | Encryption, remote wipe |
| Improper disposal | NIST 800-88 sanitization |
| Insufficient training | Annual training program |
| Missing BAAs | BA inventory and tracking |
| Insufficient audit logs | Comprehensive logging |

### Penalty Structure

| Tier | Knowledge | Per Violation | Annual Maximum |
|------|-----------|---------------|----------------|
| 1 | Unknown | $100-$50,000 | $1,500,000 |
| 2 | Reasonable cause | $1,000-$50,000 | $1,500,000 |
| 3 | Willful neglect (corrected) | $10,000-$50,000 | $1,500,000 |
| 4 | Willful neglect (not corrected) | $50,000 | $1,500,000 |

### FDA-HIPAA Intersection

| Device Scenario | FDA | HIPAA |
|-----------------|-----|-------|
| Standalone diagnostic | 510(k)/PMA | If transmits PHI |
| Connected insulin pump | Class III PMA | Yes (patient data) |
| Wellness app (no diagnosis) | Exempt | If stores PHI |
| EHR-integrated device | May apply | Yes |
| Research device | IDE | IRB may waive |
