# Security Control Testing Guide

Technical verification procedures for ISO 27002 control assessment.

---

## Table of Contents

- [Control Testing Approach](#control-testing-approach)
- [Organizational Controls (A.5)](#organizational-controls-a5)
- [People Controls (A.6)](#people-controls-a6)
- [Physical Controls (A.7)](#physical-controls-a7)
- [Technological Controls (A.8)](#technological-controls-a8)

---

## Control Testing Approach

### Testing Methods

| Method | Description | When to Use |
|--------|-------------|-------------|
| Inquiry | Interview control owners | All controls |
| Observation | Watch process execution | Operational controls |
| Inspection | Review documentation/config | Policy controls |
| Re-performance | Execute control procedure | Critical controls |

### Sampling Guidelines

| Population Size | Sample Size |
|-----------------|-------------|
| 1-10 | All items |
| 11-50 | 10 items |
| 51-250 | 15 items |
| 251+ | 25 items |

---

## Organizational Controls (A.5)

### A.5.1 - Policies for Information Security

**Test Procedure:**
1. Obtain current information security policy
2. Verify management signature and approval date
3. Check policy is accessible to all employees
4. Confirm review within past 12 months
5. Sample 5 employees: verify awareness of policy location

**Evidence Required:**
- Signed policy document
- Intranet/portal screenshot showing policy access
- Policy review meeting minutes
- Employee acknowledgment records

### A.5.15 - Access Control

**Test Procedure:**
1. Obtain access control policy
2. Select sample of 10 user accounts
3. Verify access rights match job descriptions
4. Check for segregation of duties violations
5. Verify access provisioning follows documented process

**Evidence Required:**
- Access control policy
- User access matrix
- Access request forms with approvals
- Role definitions

### A.5.24 - Information Security Incident Management

**Test Procedure:**
1. Review incident management procedure
2. Select 3 recent incidents from log
3. Verify incidents followed documented process
4. Check escalation thresholds were respected
5. Confirm lessons learned were documented

**Evidence Required:**
- Incident response procedure
- Incident tickets with timeline
- Escalation records
- Post-incident review reports

---

## People Controls (A.6)

### A.6.1 - Screening

**Test Procedure:**
1. Review background check policy
2. Select 10 recent hires
3. Verify background checks completed before start
4. Check checks match role sensitivity level
5. Confirm records are securely stored

**Evidence Required:**
- Screening policy
- Background check completion records
- Role risk classification matrix

### A.6.3 - Information Security Awareness

**Test Procedure:**
1. Obtain training program documentation
2. Select sample of 15 employees
3. Verify training completion records
4. Review training content for currency
5. Check phishing simulation results

**Evidence Required:**
- Training materials and schedule
- LMS completion reports
- Phishing test results
- Training effectiveness metrics

### A.6.7 - Remote Working

**Test Procedure:**
1. Review remote working policy
2. Verify VPN is required for remote access
3. Sample 5 remote worker devices for compliance
4. Check endpoint protection is active
5. Verify secure data handling requirements

**Evidence Required:**
- Remote working policy
- VPN connection logs
- Endpoint compliance reports
- Remote access agreement signatures

---

## Physical Controls (A.7)

### A.7.1 - Physical Security Perimeters

**Test Procedure:**
1. Walk perimeter of secure areas
2. Verify access controls at all entry points
3. Check visitor management process
4. Review after-hours access logs
5. Confirm emergency exits are secure

**Evidence Required:**
- Site security plan
- Access control system configuration
- Visitor logs
- Guard tour records

### A.7.4 - Physical Security Monitoring

**Test Procedure:**
1. Verify CCTV coverage of critical areas
2. Check recording retention period
3. Review sample of recent alert responses
4. Confirm monitoring is 24/7 or as required
5. Verify footage protection and access controls

**Evidence Required:**
- CCTV coverage map
- Retention policy and settings
- Alert response records
- Access logs for footage viewing

---

## Technological Controls (A.8)

### A.8.2 - Privileged Access Rights

**Test Procedure:**
1. Obtain list of privileged accounts
2. Verify each has documented justification
3. Check separation of admin and user accounts
4. Confirm MFA is required for privileged access
5. Review privileged activity logs

**Evidence Required:**
- Privileged account inventory
- Access justification records
- PAM solution configuration
- Activity audit logs

### A.8.5 - Secure Authentication

**Test Procedure:**
1. Review password policy configuration
2. Verify MFA enrollment rates
3. Test account lockout after failed attempts
4. Check authentication logging
5. Verify secure authentication protocols (no plaintext)

**Evidence Required:**
- Password policy settings screenshot
- MFA enrollment report
- Account lockout configuration
- Authentication audit logs

### A.8.7 - Protection Against Malware

**Test Procedure:**
1. Verify endpoint protection coverage
2. Check definition update frequency
3. Review quarantine/detection logs
4. Confirm central management console
5. Test sample detection (EICAR)

**Evidence Required:**
- Endpoint protection deployment report
- Update status dashboard
- Detection/quarantine logs
- EICAR test results

### A.8.8 - Management of Technical Vulnerabilities

**Test Procedure:**
1. Obtain vulnerability scanning schedule
2. Review recent scan results
3. Verify critical vulnerabilities patched within SLA
4. Check vulnerability tracking system
5. Sample 5 critical findings for remediation evidence

**Evidence Required:**
- Scanning schedule and scope
- Scan reports with severity breakdown
- Patch deployment records
- Remediation tracking tickets

### A.8.13 - Information Backup

**Test Procedure:**
1. Review backup policy and schedule
2. Verify backup completion logs
3. Check encryption of backup data
4. Request recent restoration test results
5. Verify offsite/cloud backup location

**Evidence Required:**
- Backup policy
- Backup job completion logs
- Encryption configuration
- Restoration test records

### A.8.15 - Logging

**Test Procedure:**
1. Identify systems requiring logging
2. Verify logging is enabled and configured
3. Check log retention meets requirements
4. Confirm log integrity protection
5. Verify SIEM integration and alerting

**Evidence Required:**
- Logging requirements matrix
- Log configuration screenshots
- Retention settings
- SIEM alert rules

### A.8.24 - Use of Cryptography

**Test Procedure:**
1. Review cryptography policy
2. Verify encryption at rest configuration
3. Check TLS configuration (version, ciphers)
4. Review key management procedures
5. Verify certificate inventory and expiration tracking

**Evidence Required:**
- Cryptography policy
- Encryption configuration settings
- SSL/TLS scan results
- Key management procedures
- Certificate inventory
