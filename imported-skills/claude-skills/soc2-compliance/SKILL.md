---
name: "soc2-compliance"
description: "Use when the user asks to prepare for SOC 2 audits, map Trust Service Criteria, build control matrices, collect audit evidence, perform gap analysis, or assess SOC 2 Type I vs Type II readiness."
---

# SOC 2 Compliance

SOC 2 Type I and Type II compliance preparation for SaaS companies. Covers Trust Service Criteria mapping, control matrix generation, evidence collection, gap analysis, and audit readiness assessment.

## Table of Contents

- [Overview](#overview)
- [Trust Service Criteria](#trust-service-criteria)
- [Control Matrix Generation](#control-matrix-generation)
- [Gap Analysis Workflow](#gap-analysis-workflow)
- [Evidence Collection](#evidence-collection)
- [Audit Readiness Checklist](#audit-readiness-checklist)
- [Vendor Management](#vendor-management)
- [Continuous Compliance](#continuous-compliance)
- [Anti-Patterns](#anti-patterns)
- [Tools](#tools)
- [References](#references)
- [Cross-References](#cross-references)

---

## Overview

### What Is SOC 2?

SOC 2 (System and Organization Controls 2) is an auditing framework developed by the AICPA that evaluates how a service organization manages customer data. It applies to any technology company that stores, processes, or transmits customer information — primarily SaaS, cloud infrastructure, and managed service providers.

### Type I vs Type II

| Aspect | Type I | Type II |
|--------|--------|---------|
| **Scope** | Design of controls at a point in time | Design AND operating effectiveness over a period |
| **Duration** | Snapshot (single date) | Observation window (3-12 months, typically 6) |
| **Evidence** | Control descriptions, policies | Control descriptions + operating evidence (logs, tickets, screenshots) |
| **Cost** | $20K-$50K (audit fees) | $30K-$100K+ (audit fees) |
| **Timeline** | 1-2 months (audit phase) | 6-12 months (observation + audit) |
| **Best For** | First-time compliance, rapid market need | Mature organizations, enterprise customers |

### Who Needs SOC 2?

- **SaaS companies** selling to enterprise customers
- **Cloud infrastructure providers** handling customer workloads
- **Data processors** managing PII, PHI, or financial data
- **Managed service providers** with access to client systems
- **Any vendor** whose customers require third-party assurance

### Typical Journey

```
Gap Assessment → Remediation → Type I Audit → Observation Period → Type II Audit → Annual Renewal
    (4-8 wk)      (8-16 wk)     (4-6 wk)       (6-12 mo)          (4-6 wk)       (ongoing)
```

---

## Trust Service Criteria

SOC 2 is organized around five Trust Service Criteria (TSC) categories. **Security** is required for every SOC 2 report; the remaining four are optional and selected based on business need.

### Security (Common Criteria CC1-CC9) — Required

The foundation of every SOC 2 report. Maps to COSO 2013 principles.

| Criteria | Domain | Key Controls |
|----------|--------|-------------|
| **CC1** | Control Environment | Integrity/ethics, board oversight, org structure, competence, accountability |
| **CC2** | Communication & Information | Internal/external communication, information quality |
| **CC3** | Risk Assessment | Risk identification, fraud risk, change impact analysis |
| **CC4** | Monitoring Activities | Ongoing monitoring, deficiency evaluation, corrective actions |
| **CC5** | Control Activities | Policies/procedures, technology controls, deployment through policies |
| **CC6** | Logical & Physical Access | Access provisioning, authentication, encryption, physical restrictions |
| **CC7** | System Operations | Vulnerability management, anomaly detection, incident response |
| **CC8** | Change Management | Change authorization, testing, approval, emergency changes |
| **CC9** | Risk Mitigation | Vendor/business partner risk management |

### Availability (A1) — Optional

| Criteria | Focus | Key Controls |
|----------|-------|-------------|
| **A1.1** | Capacity management | Infrastructure scaling, resource monitoring, capacity planning |
| **A1.2** | Recovery operations | Backup procedures, disaster recovery, BCP testing |
| **A1.3** | Recovery testing | DR drills, failover testing, RTO/RPO validation |

**Select when:** Customers depend on your uptime; you have SLAs; downtime causes direct business impact.

### Confidentiality (C1) — Optional

| Criteria | Focus | Key Controls |
|----------|-------|-------------|
| **C1.1** | Identification | Data classification policy, confidential data inventory |
| **C1.2** | Protection | Encryption at rest and in transit, DLP, access restrictions |
| **C1.3** | Disposal | Secure deletion procedures, media sanitization, retention enforcement |

**Select when:** You handle trade secrets, proprietary data, or contractually confidential information.

### Processing Integrity (PI1) — Optional

| Criteria | Focus | Key Controls |
|----------|-------|-------------|
| **PI1.1** | Accuracy | Input validation, processing checks, output verification |
| **PI1.2** | Completeness | Transaction monitoring, reconciliation, error handling |
| **PI1.3** | Timeliness | SLA monitoring, processing delay alerts, batch job monitoring |
| **PI1.4** | Authorization | Processing authorization controls, segregation of duties |

**Select when:** Data accuracy is critical (financial processing, healthcare records, analytics platforms).

### Privacy (P1-P8) — Optional

| Criteria | Focus | Key Controls |
|----------|-------|-------------|
| **P1** | Notice | Privacy policy, data collection notice, purpose limitation |
| **P2** | Choice & Consent | Opt-in/opt-out, consent management, preference tracking |
| **P3** | Collection | Minimal collection, lawful basis, purpose specification |
| **P4** | Use, Retention, Disposal | Purpose limitation, retention schedules, secure disposal |
| **P5** | Access | Data subject access requests, correction rights |
| **P6** | Disclosure & Notification | Third-party sharing, breach notification |
| **P7** | Quality | Data accuracy verification, correction mechanisms |
| **P8** | Monitoring & Enforcement | Privacy program monitoring, complaint handling |

**Select when:** You process PII and customers expect privacy assurance (complements GDPR compliance).

---

## Control Matrix Generation

A control matrix maps each TSC criterion to specific controls, owners, evidence, and testing procedures.

### Matrix Structure

| Field | Description |
|-------|-------------|
| **Control ID** | Unique identifier (e.g., SEC-001, AVL-003) |
| **TSC Mapping** | Which criteria the control addresses (e.g., CC6.1, A1.2) |
| **Control Description** | What the control does |
| **Control Type** | Preventive, Detective, or Corrective |
| **Owner** | Responsible person/team |
| **Frequency** | Continuous, Daily, Weekly, Monthly, Quarterly, Annual |
| **Evidence Type** | Screenshot, Log, Policy, Config, Ticket |
| **Testing Procedure** | How the auditor verifies the control |

### Control Naming Convention

```
{CATEGORY}-{NUMBER}
SEC-001 through SEC-NNN  → Security
AVL-001 through AVL-NNN  → Availability
CON-001 through CON-NNN  → Confidentiality
PRI-001 through PRI-NNN  → Processing Integrity
PRV-001 through PRV-NNN  → Privacy
```

### Workflow

1. Select applicable TSC categories based on business needs
2. Run `control_matrix_builder.py` to generate the baseline matrix
3. Customize controls to match your actual environment
4. Assign owners and evidence requirements
5. Validate coverage — every selected TSC criterion must have at least one control

---

## Gap Analysis Workflow

### Phase 1: Current State Assessment

1. **Document existing controls** — inventory all security policies, procedures, and technical controls
2. **Map to TSC** — align existing controls to Trust Service Criteria
3. **Collect evidence samples** — gather proof that controls exist and operate
4. **Interview control owners** — verify understanding and execution

### Phase 2: Gap Identification

Run `gap_analyzer.py` against your current controls to identify:

- **Missing controls** — TSC criteria with no corresponding control
- **Partially implemented** — Control exists but lacks evidence or consistency
- **Design gaps** — Control designed but does not adequately address the criteria
- **Operating gaps** (Type II only) — Control designed correctly but not operating effectively

### Phase 3: Remediation Planning

For each gap, define:

| Field | Description |
|-------|-------------|
| Gap ID | Reference identifier |
| TSC Criteria | Affected criteria |
| Gap Description | What is missing or insufficient |
| Remediation Action | Specific steps to close the gap |
| Owner | Person responsible for remediation |
| Priority | Critical / High / Medium / Low |
| Target Date | Completion deadline |
| Dependencies | Other gaps or projects that must complete first |

### Phase 4: Timeline Planning

| Priority | Target Remediation |
|----------|--------------------|
| Critical | 2-4 weeks |
| High | 4-8 weeks |
| Medium | 8-12 weeks |
| Low | 12-16 weeks |

---

## Evidence Collection

### Evidence Types by Control Category

| Control Area | Primary Evidence | Secondary Evidence |
|--------------|-----------------|-------------------|
| Access Management | User access reviews, provisioning tickets | Role matrix, access logs |
| Change Management | Change tickets, approval records | Deployment logs, test results |
| Incident Response | Incident tickets, postmortems | Runbooks, escalation records |
| Vulnerability Management | Scan reports, patch records | Remediation timelines |
| Encryption | Configuration screenshots, certificate inventory | Key rotation logs |
| Backup & Recovery | Backup logs, DR test results | Recovery time measurements |
| Monitoring | Alert configurations, dashboard screenshots | On-call schedules, escalation records |
| Policy Management | Signed policies, version history | Training completion records |
| Vendor Management | Vendor assessments, SOC 2 reports | Contract reviews, risk registers |

### Automation Opportunities

| Area | Automation Approach |
|------|-------------------|
| Access reviews | Integrate IAM with ticketing (automatic quarterly review triggers) |
| Configuration evidence | Infrastructure-as-code snapshots, compliance-as-code tools |
| Vulnerability scans | Scheduled scanning with auto-generated reports |
| Change management | Git-based audit trail (commits, PRs, approvals) |
| Uptime monitoring | Automated SLA dashboards with historical data |
| Backup verification | Automated restore tests with success/failure logging |

### Continuous Monitoring

Move from point-in-time evidence collection to continuous compliance:

1. **Automated evidence gathering** — scripts that pull evidence on schedule
2. **Control dashboards** — real-time visibility into control status
3. **Alert-based monitoring** — notify when a control drifts out of compliance
4. **Evidence repository** — centralized, timestamped evidence storage

---

## Audit Readiness Checklist

### Pre-Audit Preparation (4-6 Weeks Before)

- [ ] All controls documented with descriptions, owners, and frequencies
- [ ] Evidence collected for the entire observation period (Type II)
- [ ] Control matrix reviewed and gaps remediated
- [ ] Policies signed and distributed within the last 12 months
- [ ] Access reviews completed within the required frequency
- [ ] Vulnerability scans current (no critical/high unpatched > SLA)
- [ ] Incident response plan tested within the last 12 months
- [ ] Vendor risk assessments current for all subservice organizations
- [ ] DR/BCP tested and documented within the last 12 months
- [ ] Employee security training completed for all staff

### Readiness Scoring

| Score | Rating | Meaning |
|-------|--------|---------|
| 90-100% | Audit Ready | Proceed with confidence |
| 75-89% | Minor Gaps | Address before scheduling audit |
| 50-74% | Significant Gaps | Remediation required |
| < 50% | Not Ready | Major program build-out needed |

### Common Audit Findings

| Finding | Root Cause | Prevention |
|---------|-----------|-----------|
| Incomplete access reviews | Manual process, no reminders | Automate quarterly review triggers |
| Missing change approvals | Emergency changes bypass process | Define emergency change procedure with post-hoc approval |
| Stale vulnerability scans | Scanner misconfigured | Automated weekly scans with alerting |
| Policy not acknowledged | No tracking mechanism | Annual e-signature workflow |
| Missing vendor assessments | No vendor inventory | Maintain vendor register with review schedule |

---

## Vendor Management

### Third-Party Risk Assessment

Every vendor that accesses, stores, or processes customer data must be assessed:

1. **Vendor inventory** — maintain a register of all service providers
2. **Risk classification** — categorize vendors by data access level
3. **Due diligence** — collect SOC 2 reports, security questionnaires, certifications
4. **Contractual protections** — ensure DPAs, security requirements, breach notification clauses
5. **Ongoing monitoring** — annual reassessment, continuous news monitoring

### Vendor Risk Tiers

| Tier | Data Access | Assessment Frequency | Requirements |
|------|-------------|---------------------|-------------|
| Critical | Processes/stores customer data | Annual + continuous monitoring | SOC 2 Type II, penetration test, security review |
| High | Accesses customer environment | Annual | SOC 2 Type II or equivalent, questionnaire |
| Medium | Indirect access, support tools | Annual questionnaire | Security certifications, questionnaire |
| Low | No data access | Biennial questionnaire | Basic security questionnaire |

### Subservice Organizations

When your SOC 2 report relies on controls at a subservice organization (e.g., AWS, GCP, Azure):

- **Inclusive method** — your report covers the subservice org's controls (requires their cooperation)
- **Carve-out method** — your report excludes their controls but references their SOC 2 report
- Most companies use **carve-out** and include complementary user entity controls (CUECs)

---

## Continuous Compliance

### From Point-in-Time to Continuous

| Aspect | Point-in-Time | Continuous |
|--------|---------------|-----------|
| Evidence collection | Manual, before audit | Automated, ongoing |
| Control monitoring | Periodic review | Real-time dashboards |
| Drift detection | Found during audit | Alert-based, immediate |
| Remediation | Reactive | Proactive |
| Audit preparation | 4-8 week scramble | Always ready |

### Implementation Steps

1. **Automate evidence gathering** — cron jobs, API integrations, IaC snapshots
2. **Build control dashboards** — aggregate control status into a single view
3. **Configure drift alerts** — notify when controls fall out of compliance
4. **Establish review cadence** — weekly control owner check-ins, monthly steering
5. **Maintain evidence repository** — centralized, timestamped, auditor-accessible

### Annual Re-Assessment Cycle

| Quarter | Activities |
|---------|-----------|
| Q1 | Annual risk assessment, policy refresh, vendor reassessment launch |
| Q2 | Internal control testing, remediation of findings |
| Q3 | Pre-audit readiness review, evidence completeness check |
| Q4 | External audit, management assertion, report distribution |

---

## Anti-Patterns

| Anti-Pattern | Why It Fails | Better Approach |
|--------------|-------------|----------------|
| Point-in-time compliance | Controls degrade between audits; gaps found during audit | Implement continuous monitoring and automated evidence |
| Manual evidence collection | Time-consuming, inconsistent, error-prone | Automate with scripts, IaC, and compliance platforms |
| Missing vendor assessments | Auditors flag incomplete vendor due diligence | Maintain vendor register with risk-tiered assessment schedule |
| Copy-paste policies | Generic policies don't match actual operations | Tailor policies to your actual environment and technology stack |
| Security theater | Controls exist on paper but aren't followed | Verify operating effectiveness; build controls into workflows |
| Skipping Type I | Jumping to Type II without foundational readiness | Start with Type I to validate control design before observation |
| Over-scoping TSC | Including all 5 categories when only Security is needed | Select categories based on actual customer/business requirements |
| Treating audit as a project | Compliance degrades after the report is issued | Build compliance into daily operations and engineering culture |

---

## Tools

### Control Matrix Builder

Generates a SOC 2 control matrix from selected TSC categories.

```bash
# Generate full security matrix in markdown
python scripts/control_matrix_builder.py --categories security --format md

# Generate matrix for multiple categories as JSON
python scripts/control_matrix_builder.py --categories security,availability,confidentiality --format json

# All categories, CSV output
python scripts/control_matrix_builder.py --categories security,availability,confidentiality,processing-integrity,privacy --format csv
```

### Evidence Tracker

Tracks evidence collection status per control.

```bash
# Check evidence status from a control matrix
python scripts/evidence_tracker.py --matrix controls.json --status

# JSON output for integration
python scripts/evidence_tracker.py --matrix controls.json --status --json
```

### Gap Analyzer

Analyzes current controls against SOC 2 requirements and identifies gaps.

```bash
# Type I gap analysis
python scripts/gap_analyzer.py --controls current_controls.json --type type1

# Type II gap analysis (includes operating effectiveness)
python scripts/gap_analyzer.py --controls current_controls.json --type type2 --json
```

---

## References

- [Trust Service Criteria Reference](references/trust_service_criteria.md) — All 5 TSC categories with sub-criteria, control objectives, and evidence examples
- [Evidence Collection Guide](references/evidence_collection_guide.md) — Evidence types per control, automation tools, documentation requirements
- [Type I vs Type II Comparison](references/type1_vs_type2.md) — Detailed comparison, timeline, cost analysis, and upgrade path

---

## Cross-References

- **[gdpr-dsgvo-expert](../gdpr-dsgvo-expert/SKILL.md)** — SOC 2 Privacy criteria overlaps significantly with GDPR requirements; use together when processing EU personal data
- **[information-security-manager-iso27001](../information-security-manager-iso27001/SKILL.md)** — ISO 27001 Annex A controls map closely to SOC 2 Security criteria; organizations pursuing both can share evidence
- **[isms-audit-expert](../isms-audit-expert/SKILL.md)** — Audit methodology and finding management patterns transfer directly to SOC 2 audit preparation
