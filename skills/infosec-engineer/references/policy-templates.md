# Security Policy Templates

Starter templates for common security policies. Customize sections in brackets to match organizational specifics.

## Table of Contents
- [Acceptable Use Policy](#acceptable-use-policy)
- [Access Control Policy](#access-control-policy)
- [Incident Response Policy](#incident-response-policy)
- [Data Classification Policy](#data-classification-policy)
- [Vulnerability Management Policy](#vulnerability-management-policy)
- [Change Management Policy](#change-management-policy)

---

## Acceptable Use Policy

### Purpose
Define acceptable use of [Organization] information systems and assets.

### Scope
All employees, contractors, and third parties with access to [Organization] systems.

### Policy

**Permitted use:**
- Business purposes and authorized personal use during breaks
- Accessing only systems and data required for job responsibilities

**Prohibited activities:**
- Sharing credentials or using another person's account
- Installing unauthorized software
- Connecting unauthorized devices to the corporate network
- Accessing, downloading, or distributing illegal or offensive content
- Attempting to bypass security controls
- Storing sensitive data on personal devices or unapproved cloud services
- Sending sensitive data via unencrypted channels

**Email and communication:**
- Do not open suspicious attachments or click unknown links
- Report phishing attempts to [security team email]
- Do not auto-forward corporate email to personal accounts

**Remote work:**
- Use VPN when accessing corporate resources remotely
- Lock screens when stepping away
- Do not use public Wi-Fi without VPN
- Ensure home network uses WPA2/WPA3 encryption

### Enforcement
Violations may result in disciplinary action up to termination and legal action.

---

## Access Control Policy

### Purpose
Ensure access to information systems is authorized, appropriate, and regularly reviewed.

### Principles
- **Least privilege** — Users receive minimum access required for their role
- **Need to know** — Access granted only when a business need is demonstrated
- **Separation of duties** — Critical functions require multiple people

### Account Management
- Unique user IDs for all accounts (no shared accounts)
- Accounts provisioned based on role-based access matrix
- Accounts deactivated within [24 hours] of employment termination
- Temporary accounts expire automatically after [90 days]

### Authentication Requirements
- Minimum password length: [12 characters]
- MFA required for: all remote access, admin accounts, access to sensitive data
- Session timeout: [15 minutes] of inactivity for sensitive systems
- Account lockout after [5 failed attempts], progressive delay

### Access Reviews
- User access reviewed [quarterly] by system owners
- Privileged access reviewed [monthly]
- Dormant accounts (no login for [90 days]) flagged for review
- Access changes documented and approved by manager

### Privileged Access
- Admin access requires separate privileged account
- Privileged sessions logged and monitored
- Just-in-time access preferred over standing privileges
- Privileged access requires MFA and re-authentication

---

## Incident Response Policy

### Purpose
Establish procedures for detecting, responding to, and recovering from security incidents.

### Severity Levels

| Severity | Criteria | Response Time | Notification |
|---|---|---|---|
| Critical | Data breach, active exploitation, total outage | 15 min | CISO, Legal, Executive team |
| High | Partial breach, vulnerability under exploitation | 1 hour | Security team, IT management |
| Medium | Vulnerability discovered, minor exposure | 4 hours | Security team |
| Low | Policy violation, informational | 24 hours | Security team |

### Incident Response Team
- **Incident Commander** — Coordinates response, makes decisions
- **Technical Lead** — Leads investigation and remediation
- **Communications Lead** — Handles internal and external communication
- **Legal/Compliance** — Advises on regulatory obligations

### Response Phases

**1. Detection and Analysis**
- Validate the incident (confirm it's not a false positive)
- Classify severity
- Document initial findings
- Notify appropriate personnel per severity table

**2. Containment**
- Short-term: isolate affected systems to stop spread
- Long-term: implement temporary fixes while preserving evidence
- Document all containment actions with timestamps

**3. Eradication**
- Identify and eliminate root cause
- Remove attacker access (rotate credentials, patch vulnerabilities)
- Verify eradication through scanning and monitoring

**4. Recovery**
- Restore systems from clean backups
- Verify system integrity before returning to production
- Monitor closely for recurrence ([30 days])

**5. Post-Incident Review**
- Conduct blameless retrospective within [5 business days]
- Document timeline, root cause, impact, and lessons learned
- Update runbooks and detection rules
- Track remediation actions to completion

### Communication
- Internal status updates every [1 hour] during active Critical/High incidents
- External notification per regulatory requirements (GDPR: 72 hours, HIPAA: 60 days)
- Customer notification coordinated through Communications Lead and Legal

---

## Data Classification Policy

### Classification Levels

| Level | Description | Examples | Handling |
|---|---|---|---|
| **Restricted** | Highest sensitivity; breach causes severe harm | PII, PHI, payment data, credentials, encryption keys | Encrypted at rest and in transit, access logged, MFA required |
| **Confidential** | Internal only; breach causes significant harm | Financial reports, strategic plans, source code, employee records | Encrypted in transit, access controlled, no external sharing without approval |
| **Internal** | For internal use; breach causes minor harm | Internal policies, meeting notes, project documentation | Available to employees, not published externally |
| **Public** | No restrictions | Marketing materials, published documentation, job postings | No handling restrictions |

### Labeling
- Documents must be labeled with classification level
- Default classification is **Internal** if not explicitly labeled
- Classification set by data owner; security team advises on level

### Handling Requirements
- **Storage**: Restricted data only in approved, encrypted systems
- **Transmission**: Restricted and Confidential data encrypted in transit
- **Disposal**: Restricted data securely wiped (cryptographic erasure or physical destruction)
- **Sharing**: Restricted data requires approval and data processing agreement with recipients

---

## Vulnerability Management Policy

### Scanning Requirements
- Infrastructure vulnerability scanning: [weekly]
- Application security testing (DAST): [monthly]
- Static code analysis (SAST): [on every pull request]
- Dependency scanning (SCA): [on every build]
- Penetration testing: [annually] and after major changes

### Remediation SLAs

| Severity | CVSS Score | Remediation Timeline |
|---|---|---|
| Critical | 9.0-10.0 | [72 hours] |
| High | 7.0-8.9 | [7 days] |
| Medium | 4.0-6.9 | [30 days] |
| Low | 0.1-3.9 | [90 days] |

### Exception Process
- Exceptions require documented business justification
- Approved by [CISO or Security Lead]
- Compensating controls must be implemented
- Exceptions reviewed [quarterly] and expire after [6 months]

### Reporting
- Vulnerability metrics reported to management [monthly]
- Metrics: open vulnerabilities by severity, mean time to remediate, exception count

---

## Change Management Policy

### Scope
All changes to production systems, infrastructure, and configurations.

### Change Categories

| Category | Approval | Examples |
|---|---|---|
| **Standard** | Pre-approved, follows documented procedure | Dependency updates, config changes within parameters |
| **Normal** | Requires review and approval | New features, architecture changes, new integrations |
| **Emergency** | Post-hoc approval, expedited process | Critical security patches, production outage fixes |

### Change Process

**1. Request** — Submitter documents: what, why, risk, rollback plan, testing
**2. Review** — Peer review of code and configuration changes
**3. Approve** — Change Advisory Board (CAB) or designated approver
**4. Implement** — Deploy during approved maintenance window
**5. Verify** — Confirm change works as expected; monitor for issues
**6. Close** — Document results, update CMDB if applicable

### Requirements
- All changes require at least one peer review
- Changes to security controls require security team review
- Rollback plan documented before implementation
- Changes tested in staging before production
- Emergency changes documented within [24 hours] after implementation
