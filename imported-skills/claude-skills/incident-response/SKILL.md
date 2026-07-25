---
name: "incident-response"
description: "Use when a security incident has been detected or declared and needs classification, triage, escalation path determination, and forensic evidence collection. Covers SEV1-SEV4 classification, false positive filtering, incident taxonomy, and NIST SP 800-61 lifecycle."
---

# Incident Response

Incident response skill for the full lifecycle from initial triage through forensic collection, severity declaration, and escalation routing. This is NOT threat hunting (see threat-detection) or post-incident compliance mapping (see governance/compliance-mapping) — this is about classifying, triaging, and managing declared security incidents.

---

## Table of Contents

- [Overview](#overview)
- [Incident Triage Tool](#incident-triage-tool)
- [Incident Classification](#incident-classification)
- [Severity Framework](#severity-framework)
- [False Positive Filtering](#false-positive-filtering)
- [Forensic Evidence Collection](#forensic-evidence-collection)
- [Escalation Paths](#escalation-paths)
- [Regulatory Notification Obligations](#regulatory-notification-obligations)
- [Workflows](#workflows)
- [Anti-Patterns](#anti-patterns)
- [Cross-References](#cross-references)

---

## Overview

### What This Skill Does

This skill provides the methodology and tooling for **incident triage and response** — classifying security events into typed incidents, scoring severity, filtering false positives, determining escalation paths, and initiating forensic evidence collection under chain-of-custody controls.

### Distinction from Other Security Skills

| Skill | Focus | Approach |
|-------|-------|----------|
| **incident-response** (this) | Active incidents | Reactive — classify, escalate, collect evidence |
| threat-detection | Pre-incident hunting | Proactive — find threats before alerts fire |
| cloud-security | Cloud posture assessment | Preventive — IAM, S3, network misconfiguration |
| red-team | Offensive simulation | Offensive — test detection and response capability |

### Prerequisites

A security event must be ingested before triage. Events can come from SIEM alerts, EDR detections, threat intel feeds, or user reports. The triage tool accepts JSON event payloads; see the input schema below.

---

## Incident Triage Tool

The `incident_triage.py` tool classifies events, checks false positives, scores severity, determines escalation, and performs forensic pre-analysis.

```bash
# Classify an event from JSON file
python3 scripts/incident_triage.py --input event.json --classify --json

# Classify with false positive filtering enabled
python3 scripts/incident_triage.py --input event.json --classify --false-positive-check --json

# Force a severity level for tabletop exercises
python3 scripts/incident_triage.py --input event.json --severity sev1 --json

# Read event from stdin
echo '{"event_type": "ransomware", "host": "prod-db-01", "raw_payload": {}}' | \
  python3 scripts/incident_triage.py --classify --false-positive-check --json
```

### Input Event Schema

```json
{
  "event_type": "ransomware",
  "host": "prod-db-01",
  "user": "svc_backup",
  "source_ip": "10.1.2.3",
  "timestamp": "2024-01-15T14:32:00Z",
  "raw_payload": {}
}
```

### Exit Codes

| Code | Meaning | Required Response |
|------|---------|-------------------|
| 0 | SEV3/SEV4 or clean | Standard ticket-based handling |
| 1 | SEV2 — elevated | 1-hour bridge call, async coordination |
| 2 | SEV1 — critical | Immediate 15-minute war room, all-hands |

---

## Incident Classification

Security events are classified into 14 incident types. Classification drives default severity, MITRE technique mapping, and response SLA.

### Incident Taxonomy

| Incident Type | Default Severity | MITRE Technique | Response SLA |
|--------------|-----------------|-----------------|--------------|
| ransomware | SEV1 | T1486 | 15 minutes |
| data_exfiltration | SEV1 | T1048 | 15 minutes |
| apt_intrusion | SEV1 | T1566 | 15 minutes |
| supply_chain_compromise | SEV1 | T1195 | 15 minutes |
| domain_controller_breach | SEV1 | T1078.002 | 15 minutes |
| credential_compromise | SEV2 | T1110 | 1 hour |
| lateral_movement | SEV2 | T1021 | 1 hour |
| malware_infection | SEV2 | T1204 | 1 hour |
| insider_threat | SEV2 | T1078 | 1 hour |
| cloud_account_compromise | SEV2 | T1078.004 | 1 hour |
| unauthorized_access | SEV3 | T1190 | 4 hours |
| policy_violation | SEV3 | N/A | 4 hours |
| phishing_attempt | SEV4 | T1566.001 | 24 hours |
| security_alert | SEV4 | N/A | 24 hours |

### SEV Escalation Triggers

Any of the following automatically re-declare a higher severity:

| Trigger | New Severity |
|---------|-------------|
| Ransomware note found | SEV1 |
| Active exfiltration confirmed | SEV1 |
| CloudTrail or SIEM disabled | SEV1 |
| Domain controller access confirmed | SEV1 |
| Second system compromised | SEV1 |
| Exfiltration volume exceeds 1 GB | SEV2 minimum |
| C-suite account accessed | SEV2 minimum |

---

## Severity Framework

### SEV Level Matrix

| Level | Name | Criteria | Skills Invoked | Escalation Path |
|-------|------|----------|---------------|-----------------|
| SEV1 | Critical | Confirmed ransomware; active PII/PHI exfiltration (>10K records); domain controller breach; defense evasion (CloudTrail disabled); supply chain compromise | All skills (parallel) | SOC Lead → CISO → CEO → Board Chair |
| SEV2 | High | Confirmed unauthorized access to sensitive systems; credential compromise with elevated privileges; lateral movement confirmed; ransomware indicators without confirmed execution | triage + containment + forensics | SOC Lead → CISO |
| SEV3 | Medium | Suspected unauthorized access (unconfirmed); malware detected and contained; single account compromise (no priv escalation) | triage + containment | SOC Lead → Security Manager |
| SEV4 | Low | Security alert with no confirmed impact; informational indicator; policy violation with no data risk | triage only | L3 Analyst queue |

---

## False Positive Filtering

The triage tool applies five filters before escalating to prevent false positive inflation.

### False Positive Filter Types

| Filter | Description | Example Pattern |
|--------|-------------|----------------|
| CI/CD agent activity | Known build/deploy agents flagged as anomalies | jenkins, github-actions, circleci, gitlab-runner |
| Test environment tagging | Assets tagged as non-production | test-, staging-, dev-, sandbox- |
| Scheduled job patterns | Expected batch processes triggering alerts | cron, scheduled_task, batch_job, backup_ |
| Whitelisted identities | Explicitly approved service accounts | svc_monitoring, svc_backup, datadog-agent |
| Scanner activity | Known security scanners and vulnerability tools | nessus, qualys, rapid7, aws_inspector |

A confirmed false positive suppresses escalation and logs the suppression reason for audit purposes. Recurring false positives from the same source should be tuned out at the detection layer, not filtered repeatedly at triage.

---

## Forensic Evidence Collection

Evidence collection follows the DFRWS six-phase framework and the principle of volatile-first acquisition.

### DFRWS Six Phases

| Phase | Activity | Priority |
|-------|----------|----------|
| Identification | Identify what evidence exists and where | Immediate |
| Preservation | Prevent modification — write-block, snapshot, legal hold | Immediate |
| Collection | Acquire evidence in order of volatility | Immediate |
| Examination | Technical analysis of collected evidence | Within 2 hours |
| Analysis | Interpret findings in investigative context | Within 4 hours |
| Presentation | Produce findings report with chain of custody | Before incident closure |

### Volatile Evidence — Collect First

1. Live memory (RAM dump) — lost on reboot
2. Running processes and open network connections (`netstat`, `ps`)
3. Logged-in users and active sessions
4. System uptime and current time (for timeline anchoring)
5. Environment variables and loaded kernel modules

### Chain of Custody Requirements

Every evidence item must be recorded with:
- SHA-256 hash at acquisition time
- Acquisition timestamp in UTC with timezone offset
- Tool provenance (FTK Imager, Volatility, dd, AWS CloudTrail export)
- Investigator identity
- Transfer log (who had custody and when)

---

## Escalation Paths

### By Severity

| Severity | Immediate Contact | Bridge Call | External Notification |
|----------|------------------|-------------|----------------------|
| SEV1 | SOC Lead + CISO (15 min) | Immediate war room | Legal + PR standby; regulatory notification per deadline table |
| SEV2 | SOC Lead (30 min async) | 1-hour bridge | Legal notification if PII involved |
| SEV3 | Security Manager (4 hours) | Async only | None unless scope expands |
| SEV4 | L3 Analyst queue (24 hours) | None | None |

### By Incident Type

| Incident Type | Primary Escalation | Secondary |
|--------------|-------------------|-----------|
| Ransomware / APT | CISO + CEO | Board if data at risk |
| PII/PHI breach | Legal + CISO | Regulatory body (per deadline table) |
| Cloud account compromise | Cloud security team | CISO |
| Insider threat | HR + Legal + CISO | Law enforcement if criminal |
| Supply chain | CISO + Vendor management | Board |

---

## Regulatory Notification Obligations

The notification clock starts at incident declaration, not at investigation completion.

| Framework | Incident Type | Deadline | Penalty |
|-----------|--------------|----------|---------|
| GDPR (EU 2016/679) | Personal data breach | 72 hours after discovery | Up to 4% global revenue |
| PCI-DSS v4.0 | Cardholder data breach | 24 hours to acquirer | Card brand fines |
| HIPAA (45 CFR 164) | PHI breach (>500 individuals) | 60 days after discovery | Up to $1.9M per violation category |
| NY DFS 23 NYCRR 500 | Cybersecurity event | 72 hours to DFS | Regulatory sanctions |
| SEC Rule (17 CFR 229.106) | Material cybersecurity incident | 4 business days after materiality determination | SEC enforcement |
| CCPA / CPRA | Breach of sensitive PI | Without unreasonable delay | AG enforcement; private right of action |
| NIS2 (EU 2022/2555) | Significant incident (essential services) | 24-hour early warning; 72-hour notification | National authority sanctions |

**Operational rule:** If scope is unclear at declaration, assume the most restrictive applicable deadline and confirm scope within the first response window.

Full deadline reference: `references/regulatory-deadlines.md`

---

## Workflows

### Workflow 1: Quick Triage (15 Minutes)

For single alert requiring classification before escalation decision:

```bash
# 1. Classify the event with false positive filtering
python3 scripts/incident_triage.py --input alert.json \
  --classify --false-positive-check --json

# 2. Review severity, escalation_path, and false_positive_flag in output
# 3. If severity = sev1 or sev2, page SOC Lead immediately
# 4. If false_positive_flag = true, document and close
```

**Decision**: Exit code 2 = SEV1 war room now. Exit code 1 = SEV2 bridge call within 30 minutes.

### Workflow 2: Full Incident Response (SEV1)

```
T+0   Detection arrives (SIEM alert, EDR, user report)
T+5   Classify with incident_triage.py --classify --false-positive-check
T+10  If SEV1: page CISO, open war room, start regulatory clock
T+15  Initiate forensic collection (volatile evidence first)
T+15  Containment assessment (parallel with forensics)
T+30  Human approval gate for any containment action
T+45  Execute approved containment
T+60  Assess containment effectiveness, brief Legal if PII/PHI scope
T+4h  Final forensic evidence package, dwell time estimate
T+8h  Eradication and recovery plan
T+72h Regulatory notification submission (if GDPR/NIS2 triggered)
```

```bash
# Full classification with forensic context
python3 scripts/incident_triage.py --input incident.json \
  --classify --false-positive-check --severity sev1 --json > incident_triage_output.json

# Forensic pre-analysis
python3 scripts/incident_triage.py --input incident.json --json | \
  jq '.forensic_findings, .chain_of_custody_steps'
```

### Workflow 3: Tabletop Exercise Simulation

Simulate incidents at specific severity levels without real events:

```bash
# Simulate SEV1 ransomware incident
echo '{"event_type": "ransomware", "host": "prod-db-01", "user": "svc_backup"}' | \
  python3 scripts/incident_triage.py --classify --severity sev1 --json

# Simulate SEV2 credential compromise
echo '{"event_type": "credential_compromise", "user": "admin_user", "source_ip": "203.0.113.5"}' | \
  python3 scripts/incident_triage.py --classify --false-positive-check --json

# Verify escalation paths for all 14 incident types
for type in ransomware data_exfiltration credential_compromise lateral_movement; do
  echo "{\"event_type\": \"$type\"}" | python3 scripts/incident_triage.py --classify --json
done
```

---

## Anti-Patterns

1. **Starting the notification clock at investigation completion** — Regulatory clocks (GDPR 72 hours, PCI 24 hours) start at discovery, not investigation completion. Declaring late exposes the organization to maximum penalties even if the incident itself was minor.
2. **Containing before collecting volatile evidence** — Rebooting or isolating a system destroys RAM, running processes, and active connections. Forensic collection of volatile evidence must happen in parallel with containment, never after.
3. **Skipping false positive verification before escalation** — Escalating every alert to SEV1 degrades SOC credibility and causes alert fatigue. Always run false positive filters before paging the CISO.
4. **Undocumented incident command decisions** — Every decision made during a SEV1, including decisions made under uncertainty, must be logged in the evidence chain with timestamp and rationale. Undocumented decisions cannot be defended in regulatory investigations.
5. **Treating incident closure as investigation completion** — Incidents are closed when eradication and recovery are complete, not when the investigation is done. The forensic report and regulatory submissions may continue after operational closure.
6. **Single-source classification** — Classifying an incident from a single data source (one SIEM alert) without corroborating evidence frequently leads to misclassification. Collect at least two independent signals before declaring SEV1.
7. **Bypassing human approval gates for containment** — Automated containment actions (network isolation, credential revocation) taken without human approval can cause production outages, destroy evidence, and create liability. Human approval is non-negotiable for all mutating containment actions.

---

## Cross-References

| Skill | Relationship |
|-------|-------------|
| [threat-detection](../threat-detection/SKILL.md) | Confirmed hunting findings escalate to incident-response for triage and classification |
| [cloud-security](../cloud-security/SKILL.md) | Cloud posture findings (IAM compromise, S3 exposure) may trigger incident classification |
| [red-team](../red-team/SKILL.md) | Red team findings validate detection coverage; confirmed gaps become hunting hypotheses |
| [security-pen-testing](../security-pen-testing/SKILL.md) | Pen test vulnerabilities exploited in the wild escalate to incident-response for active incident handling |
