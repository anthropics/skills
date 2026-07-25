# ISO 27001:2022 Controls Implementation Guide

Implementation guidance for Annex A controls with evidence requirements and audit preparation.

---

## Table of Contents

- [Control Categories Overview](#control-categories-overview)
- [Organizational Controls (A.5)](#organizational-controls-a5)
- [People Controls (A.6)](#people-controls-a6)
- [Physical Controls (A.7)](#physical-controls-a7)
- [Technological Controls (A.8)](#technological-controls-a8)
- [Evidence Requirements](#evidence-requirements)
- [Statement of Applicability](#statement-of-applicability)

---

## Control Categories Overview

ISO 27001:2022 Annex A contains 93 controls across 4 categories:

| Category | Controls | Focus Areas |
|----------|----------|-------------|
| Organizational (A.5) | 37 | Policies, governance, supplier management |
| People (A.6) | 8 | HR security, awareness, remote working |
| Physical (A.7) | 14 | Perimeters, equipment, environment |
| Technological (A.8) | 34 | Access, crypto, network, development |

---

## Organizational Controls (A.5)

### A.5.1 - Policies for Information Security

**Requirement:** Define, approve, publish, and communicate information security policies.

**Implementation:**
1. Draft information security policy covering scope, objectives, principles
2. Obtain management approval signature
3. Communicate to all employees and relevant parties
4. Review annually or after significant changes

**Evidence:**
- Signed policy document
- Communication records (email, intranet)
- Acknowledgment records
- Review meeting minutes

### A.5.2 - Information Security Roles and Responsibilities

**Requirement:** Define and allocate information security responsibilities.

**Implementation:**
1. Create RACI matrix for security activities
2. Appoint Information Security Manager
3. Define responsibilities in job descriptions
4. Establish reporting lines

**Evidence:**
- RACI matrix document
- ISM appointment letter
- Job descriptions with security duties
- Organizational chart

### A.5.9 - Inventory of Information and Assets

**Requirement:** Identify and maintain inventory of information assets.

**Implementation:**
1. Create asset register with classification
2. Assign owners for each asset
3. Define acceptable use rules
4. Review quarterly

**Evidence:**
- Asset inventory/register
- Classification scheme
- Owner assignment records
- Review logs

### A.5.15 - Access Control

**Requirement:** Establish and implement rules for controlling access.

**Implementation:**
1. Document access control policy
2. Implement role-based access control (RBAC)
3. Define access provisioning/deprovisioning process
4. Conduct access reviews quarterly

**Evidence:**
- Access control policy
- RBAC role definitions
- Access request forms
- Review reports

---

## People Controls (A.6)

### A.6.1 - Screening

**Requirement:** Verify backgrounds of candidates prior to employment.

**Implementation:**
1. Define screening requirements by role
2. Conduct background checks
3. Verify references and qualifications
4. Document screening results

**Evidence:**
- Screening policy
- Background check reports
- Verification records
- Consent forms

### A.6.3 - Information Security Awareness and Training

**Requirement:** Ensure personnel receive appropriate awareness and training.

**Implementation:**
1. Develop annual training program
2. Include role-specific training
3. Conduct phishing simulations
4. Track completion and effectiveness

**Evidence:**
- Training materials
- Completion records
- Test/quiz results
- Phishing simulation reports

### A.6.7 - Remote Working

**Requirement:** Implement security measures for remote working.

**Implementation:**
1. Establish remote working policy
2. Require VPN for network access
3. Mandate endpoint protection
4. Secure home network guidance

**Evidence:**
- Remote working policy
- VPN configuration records
- Endpoint compliance reports
- User acknowledgments

---

## Physical Controls (A.7)

### A.7.1 - Physical Security Perimeters

**Requirement:** Define and use security perimeters to protect information.

**Implementation:**
1. Define secure areas and boundaries
2. Implement access controls (badges, locks)
3. Monitor entry points
4. Maintain visitor logs

**Evidence:**
- Site security plan
- Access control system records
- CCTV footage retention
- Visitor logs

### A.7.4 - Physical Security Monitoring

**Requirement:** Monitor premises continuously for unauthorized access.

**Implementation:**
1. Deploy CCTV coverage
2. Implement intrusion detection
3. Define monitoring procedures
4. Establish incident response

**Evidence:**
- CCTV deployment records
- Monitoring procedures
- Alert configurations
- Incident logs

---

## Technological Controls (A.8)

### A.8.2 - Privileged Access Rights

**Requirement:** Restrict and manage privileged access.

**Implementation:**
1. Implement privileged access management (PAM)
2. Enforce separate admin accounts
3. Require MFA for privileged access
4. Monitor and log privileged activities

**Evidence:**
- PAM solution records
- Admin account inventory
- MFA enforcement reports
- Privileged activity logs

### A.8.5 - Secure Authentication

**Requirement:** Implement secure authentication mechanisms.

**Implementation:**
1. Enforce strong password policy
2. Implement MFA for all users
3. Use secure authentication protocols
4. Monitor authentication events

**Evidence:**
- Password policy
- MFA enrollment records
- Authentication configuration
- Failed login reports

### A.8.7 - Protection Against Malware

**Requirement:** Implement detection, prevention, and recovery for malware.

**Implementation:**
1. Deploy endpoint protection on all devices
2. Configure automatic updates
3. Implement email filtering
4. Define malware incident response

**Evidence:**
- Endpoint protection deployment
- Update/patch status
- Email filter configuration
- Malware incident records

### A.8.8 - Management of Technical Vulnerabilities

**Requirement:** Identify and address technical vulnerabilities.

**Implementation:**
1. Conduct regular vulnerability scans
2. Define remediation SLAs by severity
3. Track remediation progress
4. Verify patches applied

**Evidence:**
- Vulnerability scan reports
- Remediation tracking
- Patch deployment records
- Penetration test reports

### A.8.13 - Information Backup

**Requirement:** Maintain and test backup copies of information.

**Implementation:**
1. Define backup policy (frequency, retention)
2. Implement automated backups
3. Encrypt backup data
4. Test restoration regularly

**Evidence:**
- Backup policy
- Backup job logs
- Encryption configuration
- Restoration test records

### A.8.15 - Logging

**Requirement:** Produce, retain, and protect logs of activities.

**Implementation:**
1. Define logging requirements
2. Deploy centralized log management (SIEM)
3. Set retention periods per compliance
4. Protect log integrity

**Evidence:**
- Logging policy
- SIEM configuration
- Log retention settings
- Access controls on logs

### A.8.24 - Use of Cryptography

**Requirement:** Define and implement cryptographic controls.

**Implementation:**
1. Document cryptography policy
2. Encrypt data at rest (AES-256)
3. Encrypt data in transit (TLS 1.3)
4. Manage keys securely

**Evidence:**
- Cryptography policy
- Encryption configuration
- Certificate inventory
- Key management procedures

---

## Evidence Requirements

### Document Evidence

| Control Area | Required Documents |
|-------------|-------------------|
| Policies | Approved policy documents |
| Procedures | Documented processes with version control |
| Records | Completed forms, logs, reports |
| Contracts | Signed agreements with security clauses |

### Technical Evidence

| Control Area | Required Evidence |
|-------------|------------------|
| Access Control | System configurations, access lists |
| Logging | SIEM dashboards, sample logs |
| Encryption | Configuration screenshots, certificate details |
| Vulnerability | Scan reports, remediation tracking |

### Retention Requirements

| Evidence Type | Minimum Retention |
|--------------|-------------------|
| Policies | Current + 2 previous versions |
| Audit reports | 3 years |
| Access logs | 1 year minimum |
| Incident records | 3 years |
| Training records | Duration of employment + 2 years |

---

## Statement of Applicability

### SoA Structure

For each Annex A control, document:

| Field | Description |
|-------|-------------|
| Control ID | A.5.1, A.8.24, etc. |
| Control Name | Official control title |
| Applicable | Yes/No |
| Justification | Why applicable or not |
| Implementation Status | Implemented, Partial, Planned, N/A |
| Implementation Description | How control is implemented |
| Evidence Reference | Links to evidence |

### Sample SoA Entry

```
Control: A.8.5 - Secure Authentication

Applicable: Yes
Justification: Required for all user and system access to protect
information assets from unauthorized access.

Implementation Status: Implemented

Implementation Description:
- MFA enforced for all user accounts via Azure AD
- Admin accounts require hardware token
- Password policy: 12+ chars, complexity, 90-day rotation
- Failed login lockout after 5 attempts

Evidence:
- Azure AD MFA configuration (screenshot)
- Password policy document (DOC-SEC-015)
- Authentication audit logs (SIEM dashboard)
```

### Exclusion Justification Examples

| Control | Justification for Exclusion |
|---------|---------------------------|
| A.7.x (Physical) | Cloud-only operations, no physical facilities |
| A.8.19 (Software) | No user-installed software permitted |
| A.8.23 (Web filter) | Handled by cloud proxy service |
