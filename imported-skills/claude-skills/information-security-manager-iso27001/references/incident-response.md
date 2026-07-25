# Incident Response Procedures

Security incident detection, response, and recovery procedures per ISO 27001 requirements.

---

## Table of Contents

- [Incident Classification](#incident-classification)
- [Response Procedures](#response-procedures)
- [Escalation Matrix](#escalation-matrix)
- [Communication Templates](#communication-templates)
- [Recovery Checklists](#recovery-checklists)
- [Post-Incident Activities](#post-incident-activities)

---

## Incident Classification

### Incident Categories

| Category | Description | Examples |
|----------|-------------|----------|
| Security Breach | Unauthorized access to systems/data | Account compromise, data exfiltration |
| Malware | Malicious software infection | Ransomware, virus, trojan |
| Data Leakage | Unauthorized data disclosure | Accidental email, misconfigured storage |
| Denial of Service | Service availability impact | DDoS attack, resource exhaustion |
| Policy Violation | Security policy breach | Unauthorized software, data handling |
| Physical | Physical security incident | Theft, unauthorized entry |

### Severity Levels

| Level | Criteria | Response Time | Examples |
|-------|----------|---------------|----------|
| **Critical (P1)** | Active breach, data loss, system down | Immediate (15 min) | Ransomware, confirmed breach |
| **High (P2)** | Active threat, potential data exposure | 1 hour | Malware detected, suspicious access |
| **Medium (P3)** | Contained threat, limited impact | 4 hours | Failed attacks, policy violations |
| **Low (P4)** | Minor issue, no immediate risk | 24 hours | Suspicious emails, minor violations |

### Severity Decision Tree

```
Is there active data loss or system compromise?
├── Yes → CRITICAL (P1)
└── No → Is there an active uncontained threat?
          ├── Yes → HIGH (P2)
          └── No → Is there potential for data exposure?
                    ├── Yes → MEDIUM (P3)
                    └── No → LOW (P4)
```

---

## Response Procedures

### Phase 1: Detection and Reporting

**Objective:** Identify and report security incidents promptly.

**Steps:**
1. Identify potential incident through monitoring, alerts, or reports
2. Document initial observations (time, systems, symptoms)
3. Report to Security Team via designated channel
4. Assign incident ID and log in tracking system

**Validation:** Incident logged within 15 minutes of detection.

**Documentation Required:**
- Date/time of detection
- Detection source (monitoring, user report, automated alert)
- Affected systems/users (initial assessment)
- Reporter information

### Phase 2: Triage and Assessment

**Objective:** Determine incident scope and severity.

**Steps:**
1. Gather additional information (logs, system state)
2. Determine incident category and severity
3. Identify affected assets and potential impact
4. Assign incident owner and response team

**Validation:** Severity assigned and escalation triggered if needed.

**Assessment Checklist:**
- [ ] Systems affected identified
- [ ] Data types potentially impacted
- [ ] Attack vector determined
- [ ] Scope (single system vs. widespread)
- [ ] Business impact assessed

### Phase 3: Containment

**Objective:** Limit damage and prevent spread.

**Immediate Containment (Short-term):**
1. Isolate affected systems from network
2. Disable compromised accounts
3. Block malicious IPs/domains
4. Preserve evidence before changes

**Long-term Containment:**
1. Apply temporary fixes
2. Implement additional monitoring
3. Strengthen access controls
4. Prepare for eradication

**Validation:** Containment confirmed, no ongoing spread.

**Containment Actions by Incident Type:**

| Incident Type | Containment Actions |
|---------------|---------------------|
| Account Compromise | Disable account, revoke sessions, reset credentials |
| Malware | Isolate host, block C2 domains, scan related systems |
| Data Breach | Block exfiltration path, revoke access, enable DLP |
| DDoS | Enable DDoS protection, rate limiting, traffic scrubbing |

### Phase 4: Eradication

**Objective:** Remove threat from environment.

**Steps:**
1. Identify root cause
2. Remove malware/backdoors
3. Close vulnerabilities exploited
4. Reset compromised credentials
5. Verify threat elimination

**Validation:** No indicators of compromise remain.

**Eradication Checklist:**
- [ ] Malware removed from all systems
- [ ] Vulnerabilities patched
- [ ] Backdoors/persistence removed
- [ ] Compromised credentials rotated
- [ ] Security gaps closed

### Phase 5: Recovery

**Objective:** Restore systems to normal operation.

**Steps:**
1. Restore from clean backups if needed
2. Rebuild compromised systems
3. Verify system integrity
4. Monitor for re-infection
5. Return to production gradually

**Validation:** Systems operational with enhanced monitoring.

**Recovery Checklist:**
- [ ] Systems restored to known-good state
- [ ] Integrity verification completed
- [ ] Enhanced monitoring in place
- [ ] Business operations resumed
- [ ] User access restored (verified accounts only)

### Phase 6: Lessons Learned

**Objective:** Improve security posture and response capability.

**Steps:**
1. Conduct post-incident review (within 5 business days)
2. Document timeline and actions taken
3. Identify what worked and what didn't
4. Update procedures and controls
5. Share relevant findings (internally, externally if required)

**Validation:** Post-incident report completed and actions tracked.

---

## Escalation Matrix

### Escalation Paths

| Severity | Initial Response | 1 Hour | 4 Hours | 24 Hours |
|----------|------------------|--------|---------|----------|
| Critical | Security Team | CISO + Management | Executive Team | Board notification |
| High | Security Team | CISO | Management | - |
| Medium | Security Team | Security Manager | CISO if unresolved | - |
| Low | Security Analyst | Security Team Lead | - | - |

### Contact Information (Template)

| Role | Primary | Backup | Contact Method |
|------|---------|--------|----------------|
| Security On-Call | [Name] | [Name] | Phone, Slack |
| CISO | [Name] | [Name] | Phone, Email |
| IT Director | [Name] | [Name] | Phone, Email |
| Legal Counsel | [Name] | [Firm] | Phone |
| PR/Communications | [Name] | [Name] | Phone |
| Executive Sponsor | [Name] | [Name] | Phone |

### External Notifications

| Condition | Notify | Timeline |
|-----------|--------|----------|
| Patient data breach | HHS (HIPAA) | 60 days |
| EU personal data breach | Supervisory Authority (GDPR) | 72 hours |
| Significant breach | Law enforcement | As appropriate |
| Third-party involved | Affected vendor | Immediately |

---

## Communication Templates

### Internal Notification (Initial)

```
Subject: [SEVERITY] Security Incident - [Brief Description]

INCIDENT SUMMARY
----------------
Incident ID: INC-[YYYY]-[###]
Detected: [Date/Time]
Severity: [Critical/High/Medium/Low]
Status: [Investigating/Contained/Resolved]

WHAT HAPPENED
[Brief description of the incident]

CURRENT IMPACT
[Systems affected, business impact]

ACTIONS BEING TAKEN
[Current response activities]

WHAT YOU NEED TO DO
[Any required user actions]

NEXT UPDATE
Expected by: [Time]

Contact: Security Team - [contact info]
```

### External Notification (Breach)

```
Subject: Important Security Notice from [Organization]

Dear [Affected Party],

We are writing to inform you of a security incident that may have
involved your personal information.

WHAT HAPPENED
On [date], we discovered [brief description].

WHAT INFORMATION WAS INVOLVED
[Types of data potentially affected]

WHAT WE ARE DOING
[Actions taken to address the incident]

WHAT YOU CAN DO
[Recommended protective actions]

FOR MORE INFORMATION
[Contact information, resources]

We sincerely regret any concern this may cause and are committed
to protecting your information.

[Signature]
```

### Status Update

```
Subject: UPDATE: Security Incident INC-[ID] - [Status]

CURRENT STATUS
--------------
Status: [Contained/Eradicating/Recovering]
Last Update: [Time]

PROGRESS SINCE LAST UPDATE
[Actions completed]

CURRENT ACTIVITIES
[Ongoing response work]

REMAINING ACTIONS
[What still needs to be done]

ESTIMATED RESOLUTION
[Timeframe if known]

NEXT UPDATE
Expected: [Time]
```

---

## Recovery Checklists

### System Recovery Checklist

- [ ] Verify backup integrity before restoration
- [ ] Restore to isolated environment first
- [ ] Scan restored systems for malware
- [ ] Apply all security patches
- [ ] Reset all credentials on system
- [ ] Review and harden configurations
- [ ] Verify application functionality
- [ ] Enable enhanced logging/monitoring
- [ ] Conduct security scan before production
- [ ] Document recovery steps taken

### Account Compromise Recovery

- [ ] Disable compromised account
- [ ] Revoke all active sessions
- [ ] Reset password with strong credential
- [ ] Enable MFA if not already
- [ ] Review account activity logs
- [ ] Check for unauthorized changes
- [ ] Review connected applications
- [ ] Verify account recovery options
- [ ] Notify account owner securely
- [ ] Monitor for suspicious activity

### Ransomware Recovery

- [ ] Isolate affected systems immediately
- [ ] Identify ransomware variant
- [ ] Check for decryption tools available
- [ ] Assess backup availability/integrity
- [ ] Report to law enforcement
- [ ] Document encrypted files/systems
- [ ] Restore from clean backups
- [ ] Rebuild systems that cannot be restored
- [ ] Patch vulnerability exploited
- [ ] Implement additional controls

---

## Post-Incident Activities

### Post-Incident Review Meeting

**Timing:** Within 5 business days of resolution

**Attendees:**
- Incident response team
- Affected system owners
- Security management
- Relevant stakeholders

**Agenda:**
1. Incident timeline review
2. What worked well
3. What could be improved
4. Root cause analysis
5. Preventive measures
6. Action items and owners

### Post-Incident Report Template

```
INCIDENT POST-MORTEM REPORT
===========================

Incident ID: INC-[YYYY]-[###]
Date: [Report date]
Author: [Name]
Classification: [Internal/Confidential]

EXECUTIVE SUMMARY
[2-3 paragraph summary]

INCIDENT TIMELINE
[Detailed chronological events]

ROOT CAUSE ANALYSIS
[5 Whys or similar analysis]

IMPACT ASSESSMENT
- Systems affected: [list]
- Data impacted: [description]
- Business impact: [description]
- Financial impact: [estimate if known]

RESPONSE EFFECTIVENESS
What worked well:
- [item]
- [item]

Areas for improvement:
- [item]
- [item]

RECOMMENDATIONS
| # | Recommendation | Priority | Owner | Due Date |
|---|----------------|----------|-------|----------|
| 1 | [action] | High | [name] | [date] |
| 2 | [action] | Medium | [name] | [date] |

LESSONS LEARNED
[Key takeaways for future incidents]

APPENDICES
- Detailed logs
- Evidence inventory
- Communication records
```

### Metrics to Track

| Metric | Target | Purpose |
|--------|--------|---------|
| Mean Time to Detect (MTTD) | < 1 hour | Detection capability |
| Mean Time to Respond (MTTR) | < 4 hours | Response speed |
| Mean Time to Contain (MTTC) | < 2 hours | Containment effectiveness |
| Incidents by severity | Decreasing trend | Overall security posture |
| Repeat incidents | 0 | Root cause resolution |
