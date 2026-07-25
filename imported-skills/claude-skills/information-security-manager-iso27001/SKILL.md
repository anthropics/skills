---
name: "information-security-manager-iso27001"
description: ISO 27001 ISMS implementation and cybersecurity governance for HealthTech and MedTech companies. Use when designing an ISMS, running security risk assessments, implementing controls, pursuing ISO 27001 certification, preparing security audits, responding to security incidents, or verifying compliance. Covers ISO 27001, ISO 27002, healthcare security, and medical device cybersecurity.
---

# Information Security Manager - ISO 27001

Implement and manage Information Security Management Systems (ISMS) aligned with ISO 27001:2022 and healthcare regulatory requirements.

---

## Table of Contents

- [Trigger Phrases](#trigger-phrases)
- [Quick Start](#quick-start)
- [Tools](#tools)
- [Workflows](#workflows)
- [Reference Guides](#reference-guides)
- [Validation Checkpoints](#validation-checkpoints)

---

## Trigger Phrases

Use this skill when you hear:
- "implement ISO 27001"
- "ISMS implementation"
- "security risk assessment"
- "information security policy"
- "ISO 27001 certification"
- "security controls implementation"
- "incident response plan"
- "healthcare data security"
- "medical device cybersecurity"
- "security compliance audit"

---

## Quick Start

### Run Security Risk Assessment

```bash
python scripts/risk_assessment.py --scope "patient-data-system" --output risk_register.json
```

### Check Compliance Status

```bash
python scripts/compliance_checker.py --standard iso27001 --controls-file controls.csv
```

### Generate Gap Analysis Report

```bash
python scripts/compliance_checker.py --standard iso27001 --gap-analysis --output gaps.md
```

---

## Tools

### risk_assessment.py

Automated security risk assessment following ISO 27001 Clause 6.1.2 methodology.

**Usage:**

```bash
# Full risk assessment
python scripts/risk_assessment.py --scope "cloud-infrastructure" --output risks.json

# Healthcare-specific assessment
python scripts/risk_assessment.py --scope "ehr-system" --template healthcare --output risks.json

# Quick asset-based assessment
python scripts/risk_assessment.py --assets assets.csv --output risks.json
```

**Parameters:**

| Parameter | Required | Description |
|-----------|----------|-------------|
| `--scope` | Yes | System or area to assess |
| `--template` | No | Assessment template: `general`, `healthcare`, `cloud` |
| `--assets` | No | CSV file with asset inventory |
| `--output` | No | Output file (default: stdout) |
| `--format` | No | Output format: `json`, `csv`, `markdown` |

**Output:**
- Asset inventory with classification
- Threat and vulnerability mapping
- Risk scores (likelihood × impact)
- Treatment recommendations
- Residual risk calculations

### compliance_checker.py

Verify ISO 27001/27002 control implementation status.

**Usage:**

```bash
# Check all ISO 27001 controls
python scripts/compliance_checker.py --standard iso27001

# Gap analysis with recommendations
python scripts/compliance_checker.py --standard iso27001 --gap-analysis

# Check specific control domains
python scripts/compliance_checker.py --standard iso27001 --domains "access-control,cryptography"

# Export compliance report
python scripts/compliance_checker.py --standard iso27001 --output compliance_report.md
```

**Parameters:**

| Parameter | Required | Description |
|-----------|----------|-------------|
| `--standard` | Yes | Standard to check: `iso27001`, `iso27002`, `hipaa` |
| `--controls-file` | No | CSV with current control status |
| `--gap-analysis` | No | Include remediation recommendations |
| `--domains` | No | Specific control domains to check |
| `--output` | No | Output file path |

**Output:**
- Control implementation status
- Compliance percentage by domain
- Gap analysis with priorities
- Remediation recommendations

---

## Workflows

### Workflow 1: ISMS Implementation

**Step 1: Define Scope and Context**

Document organizational context and ISMS boundaries:
- Identify interested parties and requirements
- Define ISMS scope and boundaries
- Document internal/external issues

**Validation:** Scope statement reviewed and approved by management.

**Step 2: Conduct Risk Assessment**

```bash
python scripts/risk_assessment.py --scope "full-organization" --template general --output initial_risks.json
```

- Identify information assets
- Assess threats and vulnerabilities
- Calculate risk levels
- Determine risk treatment options

**Validation:** Risk register contains all critical assets with assigned owners.

**Step 3: Select and Implement Controls**

Map risks to ISO 27002 controls:

```bash
python scripts/compliance_checker.py --standard iso27002 --gap-analysis --output control_gaps.md
```

Control categories:
- Organizational (policies, roles, responsibilities)
- People (screening, awareness, training)
- Physical (perimeters, equipment, media)
- Technological (access, crypto, network, application)

**Validation:** Statement of Applicability (SoA) documents all controls with justification.

**Step 4: Establish Monitoring**

Define security metrics:
- Incident count and severity trends
- Control effectiveness scores
- Training completion rates
- Audit findings closure rate

**Validation:** Dashboard shows real-time compliance status.

### Workflow 2: Security Risk Assessment

**Step 1: Asset Identification**

Create asset inventory:

| Asset Type | Examples | Classification |
|------------|----------|----------------|
| Information | Patient records, source code | Confidential |
| Software | EHR system, APIs | Critical |
| Hardware | Servers, medical devices | High |
| Services | Cloud hosting, backup | High |
| People | Admin accounts, developers | Varies |

**Validation:** All assets have assigned owners and classifications.

**Step 2: Threat Analysis**

Identify threats per asset category:

| Asset | Threats | Likelihood |
|-------|---------|------------|
| Patient data | Unauthorized access, breach | High |
| Medical devices | Malware, tampering | Medium |
| Cloud services | Misconfiguration, outage | Medium |
| Credentials | Phishing, brute force | High |

**Validation:** Threat model covers top-10 industry threats.

**Step 3: Vulnerability Assessment**

```bash
python scripts/risk_assessment.py --scope "network-infrastructure" --output vuln_risks.json
```

Document vulnerabilities:
- Technical (unpatched systems, weak configs)
- Process (missing procedures, gaps)
- People (lack of training, insider risk)

**Validation:** Vulnerability scan results mapped to risk register.

**Step 4: Risk Evaluation and Treatment**

Calculate risk: `Risk = Likelihood × Impact`

| Risk Level | Score | Treatment |
|------------|-------|-----------|
| Critical | 20-25 | Immediate action required |
| High | 15-19 | Treatment plan within 30 days |
| Medium | 10-14 | Treatment plan within 90 days |
| Low | 5-9 | Accept or monitor |
| Minimal | 1-4 | Accept |

**Validation:** All high/critical risks have approved treatment plans.

### Workflow 3: Incident Response

**Step 1: Detection and Reporting**

Incident categories:
- Security breach (unauthorized access)
- Malware infection
- Data leakage
- System compromise
- Policy violation

**Validation:** Incident logged within 15 minutes of detection.

**Step 2: Triage and Classification**

| Severity | Criteria | Response Time |
|----------|----------|---------------|
| Critical | Data breach, system down | Immediate |
| High | Active threat, significant risk | 1 hour |
| Medium | Contained threat, limited impact | 4 hours |
| Low | Minor violation, no impact | 24 hours |

**Validation:** Severity assigned and escalation triggered if needed.

**Step 3: Containment and Eradication**

Immediate actions:
1. Isolate affected systems
2. Preserve evidence
3. Block threat vectors
4. Remove malicious artifacts

**Validation:** Containment confirmed, no ongoing compromise.

**Step 4: Recovery and Lessons Learned**

Post-incident activities:
1. Restore systems from clean backups
2. Verify integrity before reconnection
3. Document timeline and actions
4. Conduct post-incident review
5. Update controls and procedures

**Validation:** Post-incident report completed within 5 business days.

---

## Reference Guides

### When to Use Each Reference

**references/iso27001-controls.md**
- Control selection for SoA
- Implementation guidance
- Evidence requirements
- Audit preparation

**references/risk-assessment-guide.md**
- Risk methodology selection
- Asset classification criteria
- Threat modeling approaches
- Risk calculation methods

**references/incident-response.md**
- Response procedures
- Escalation matrices
- Communication templates
- Recovery checklists

---

## Validation Checkpoints

### ISMS Implementation Validation

| Phase | Checkpoint | Evidence Required |
|-------|------------|-------------------|
| Scope | Scope approved | Signed scope document |
| Risk | Register complete | Risk register with owners |
| Controls | SoA approved | Statement of Applicability |
| Operation | Metrics active | Dashboard screenshots |
| Audit | Internal audit done | Audit report |

### Certification Readiness

Before Stage 1 audit:
- [ ] ISMS scope documented and approved
- [ ] Information security policy published
- [ ] Risk assessment completed
- [ ] Statement of Applicability finalized
- [ ] Internal audit conducted
- [ ] Management review completed
- [ ] Nonconformities addressed

Before Stage 2 audit:
- [ ] Controls implemented and operational
- [ ] Evidence of effectiveness available
- [ ] Staff trained and aware
- [ ] Incidents logged and managed
- [ ] Metrics collected for 3+ months

### Compliance Verification

Run periodic checks:

```bash
# Monthly compliance check
python scripts/compliance_checker.py --standard iso27001 --output monthly_$(date +%Y%m).md

# Quarterly gap analysis
python scripts/compliance_checker.py --standard iso27001 --gap-analysis --output quarterly_gaps.md
```

---

## Worked Example: Healthcare Risk Assessment

**Scenario:** Assess security risks for a patient data management system.

### Step 1: Define Assets

```bash
python scripts/risk_assessment.py --scope "patient-data-system" --template healthcare
```

**Asset inventory output:**

| Asset ID | Asset | Type | Owner | Classification |
|----------|-------|------|-------|----------------|
| A001 | Patient database | Information | DBA Team | Confidential |
| A002 | EHR application | Software | App Team | Critical |
| A003 | Database server | Hardware | Infra Team | High |
| A004 | Admin credentials | Access | Security | Critical |

### Step 2: Identify Risks

**Risk register output:**

| Risk ID | Asset | Threat | Vulnerability | L | I | Score |
|---------|-------|--------|---------------|---|---|-------|
| R001 | A001 | Data breach | Weak encryption | 3 | 5 | 15 |
| R002 | A002 | SQL injection | Input validation | 4 | 4 | 16 |
| R003 | A004 | Credential theft | No MFA | 4 | 5 | 20 |

### Step 3: Determine Treatment

| Risk | Treatment | Control | Timeline |
|------|-----------|---------|----------|
| R001 | Mitigate | Implement AES-256 encryption | 30 days |
| R002 | Mitigate | Add input validation, WAF | 14 days |
| R003 | Mitigate | Enforce MFA for all admins | 7 days |

### Step 4: Verify Implementation

```bash
python scripts/compliance_checker.py --controls-file implemented_controls.csv
```

**Verification output:**

```
Control Implementation Status
=============================
Cryptography (A.8.24): IMPLEMENTED
  - AES-256 at rest: YES
  - TLS 1.3 in transit: YES

Access Control (A.8.5): IMPLEMENTED
  - MFA enabled: YES
  - Admin accounts: 100% coverage

Application Security (A.8.26): PARTIAL
  - Input validation: YES
  - WAF deployed: PENDING

Overall Compliance: 87%
```
