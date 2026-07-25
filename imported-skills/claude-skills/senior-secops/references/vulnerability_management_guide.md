# Vulnerability Management Guide

Complete workflow for vulnerability identification, assessment, prioritization, and remediation.

---

## Table of Contents

- [Vulnerability Lifecycle](#vulnerability-lifecycle)
- [CVE Triage Process](#cve-triage-process)
- [CVSS Scoring](#cvss-scoring)
- [Remediation Workflows](#remediation-workflows)
- [Dependency Scanning](#dependency-scanning)
- [Security Incident Response](#security-incident-response)

---

## Vulnerability Lifecycle

### Overview

```
┌─────────────┐    ┌─────────────┐    ┌─────────────┐    ┌─────────────┐
│  DISCOVER   │ →  │   ASSESS    │ →  │ PRIORITIZE  │ →  │  REMEDIATE  │
│             │    │             │    │             │    │             │
│ - Scanning  │    │ - CVSS      │    │ - Risk      │    │ - Patch     │
│ - Reports   │    │ - Context   │    │ - Business  │    │ - Mitigate  │
│ - Audits    │    │ - Impact    │    │ - SLA       │    │ - Accept    │
└─────────────┘    └─────────────┘    └─────────────┘    └─────────────┘
                                                                │
                                                                ▼
                                                        ┌─────────────┐
                                                        │   VERIFY    │
                                                        │             │
                                                        │ - Retest    │
                                                        │ - Close     │
                                                        └─────────────┘
```

### State Definitions

| State | Description | Owner |
|-------|-------------|-------|
| New | Vulnerability discovered, not yet triaged | Security Team |
| Triaging | Under assessment for severity and impact | Security Team |
| Assigned | Assigned to development team for fix | Dev Team |
| In Progress | Fix being developed | Dev Team |
| In Review | Fix in code review | Dev Team |
| Testing | Fix being tested | QA Team |
| Deployed | Fix deployed to production | DevOps Team |
| Verified | Fix confirmed effective | Security Team |
| Closed | Vulnerability resolved | Security Team |
| Accepted Risk | Risk accepted with justification | CISO |

---

## CVE Triage Process

### Step 1: Initial Assessment

```python
def triage_cve(cve_id: str, affected_systems: list) -> dict:
    """
    Perform initial triage of a CVE.

    Returns triage assessment with severity and recommended actions.
    """
    # Fetch CVE details from NVD
    cve_data = fetch_nvd_data(cve_id)

    assessment = {
        'cve_id': cve_id,
        'published': cve_data['published'],
        'base_cvss': cve_data['cvss_v3']['base_score'],
        'vector': cve_data['cvss_v3']['vector_string'],
        'description': cve_data['description'],
        'affected_systems': [],
        'exploitability': check_exploitability(cve_id),
        'recommendation': None
    }

    # Check which systems are actually affected
    for system in affected_systems:
        if is_system_vulnerable(system, cve_data):
            assessment['affected_systems'].append({
                'name': system.name,
                'version': system.version,
                'exposure': assess_exposure(system)
            })

    # Determine recommendation
    assessment['recommendation'] = determine_action(assessment)

    return assessment
```

### Step 2: Severity Classification

| CVSS Score | Severity | Response SLA |
|------------|----------|--------------|
| 9.0 - 10.0 | Critical | 24 hours |
| 7.0 - 8.9 | High | 7 days |
| 4.0 - 6.9 | Medium | 30 days |
| 0.1 - 3.9 | Low | 90 days |
| 0.0 | None | Informational |

### Step 3: Context Analysis

```markdown
## CVE Context Checklist

### Exposure Assessment
- [ ] Is the vulnerable component internet-facing?
- [ ] Is the vulnerable component in a DMZ?
- [ ] Does the component process sensitive data?
- [ ] Are there compensating controls in place?

### Exploitability Assessment
- [ ] Is there a public exploit available?
- [ ] Is exploitation being observed in the wild?
- [ ] What privileges are required to exploit?
- [ ] Does exploit require user interaction?

### Business Impact
- [ ] What business processes depend on affected systems?
- [ ] What is the potential data exposure?
- [ ] What are regulatory implications?
- [ ] What is the reputational risk?
```

### Step 4: Triage Decision Matrix

| Exposure | Exploitability | Business Impact | Priority |
|----------|----------------|-----------------|----------|
| Internet | Active Exploit | High | P0 - Immediate |
| Internet | PoC Available | High | P1 - Critical |
| Internet | Theoretical | Medium | P2 - High |
| Internal | Active Exploit | High | P1 - Critical |
| Internal | PoC Available | Medium | P2 - High |
| Internal | Theoretical | Low | P3 - Medium |
| Isolated | Any | Low | P4 - Low |

---

## CVSS Scoring

### CVSS v3.1 Vector Components

```
CVSS:3.1/AV:N/AC:L/PR:N/UI:N/S:U/C:H/I:H/A:H
        │     │    │    │    │   │   │   │
        │     │    │    │    │   │   │   └── Availability Impact (H/L/N)
        │     │    │    │    │   │   └────── Integrity Impact (H/L/N)
        │     │    │    │    │   └────────── Confidentiality Impact (H/L/N)
        │     │    │    │    └────────────── Scope (C/U)
        │     │    │    └─────────────────── User Interaction (R/N)
        │     │    └──────────────────────── Privileges Required (H/L/N)
        │     └───────────────────────────── Attack Complexity (H/L)
        └─────────────────────────────────── Attack Vector (N/A/L/P)
```

### Environmental Score Adjustments

```python
def calculate_environmental_score(base_cvss: float, environment: dict) -> float:
    """
    Adjust CVSS base score based on environmental factors.

    Args:
        base_cvss: Base CVSS score from NVD
        environment: Dictionary with environmental modifiers

    Returns:
        Adjusted CVSS score for this environment
    """
    # Confidentiality Requirement (CR)
    cr_modifier = {
        'high': 1.5,
        'medium': 1.0,
        'low': 0.5
    }.get(environment.get('confidentiality_requirement', 'medium'))

    # Integrity Requirement (IR)
    ir_modifier = {
        'high': 1.5,
        'medium': 1.0,
        'low': 0.5
    }.get(environment.get('integrity_requirement', 'medium'))

    # Availability Requirement (AR)
    ar_modifier = {
        'high': 1.5,
        'medium': 1.0,
        'low': 0.5
    }.get(environment.get('availability_requirement', 'medium'))

    # Modified Attack Vector (reduce if not internet-facing)
    if not environment.get('internet_facing', True):
        base_cvss = max(0, base_cvss - 1.5)

    # Compensating controls reduce score
    if environment.get('waf_protected', False):
        base_cvss = max(0, base_cvss - 0.5)

    if environment.get('network_segmented', False):
        base_cvss = max(0, base_cvss - 0.5)

    return round(min(10.0, base_cvss), 1)
```

---

## Remediation Workflows

### Workflow 1: Emergency Patch (P0/Critical)

```
Timeline: 24 hours
Stakeholders: Security, DevOps, Engineering Lead, CISO

Hour 0-2: ASSESS
├── Confirm vulnerability affects production
├── Identify all affected systems
├── Assess active exploitation
└── Notify stakeholders

Hour 2-8: MITIGATE
├── Apply temporary mitigations (WAF rules, network blocks)
├── Enable enhanced monitoring
├── Prepare rollback plan
└── Begin patch development/testing

Hour 8-20: REMEDIATE
├── Test patch in staging
├── Security team validates fix
├── Change approval (emergency CAB)
└── Deploy to production (rolling)

Hour 20-24: VERIFY
├── Confirm vulnerability resolved
├── Monitor for issues
├── Update vulnerability tracker
└── Post-incident review scheduled
```

### Workflow 2: Standard Patch (P1-P2)

```python
# Remediation ticket template
REMEDIATION_TICKET = """
## Vulnerability Remediation

**CVE:** {cve_id}
**Severity:** {severity}
**CVSS:** {cvss_score}
**SLA:** {sla_date}

### Affected Components
{affected_components}

### Root Cause
{root_cause}

### Remediation Steps
1. Update {package} from {current_version} to {fixed_version}
2. Run security regression tests
3. Deploy to staging for validation
4. Security team approval required before production

### Testing Requirements
- [ ] Unit tests pass
- [ ] Integration tests pass
- [ ] Security scan shows vulnerability resolved
- [ ] No new vulnerabilities introduced

### Rollback Plan
{rollback_steps}

### Acceptance Criteria
- Vulnerability scan shows CVE resolved
- No functional regression
- Performance baseline maintained
"""
```

### Workflow 3: Risk Acceptance

```markdown
## Risk Acceptance Request

**Vulnerability:** CVE-XXXX-XXXXX
**Affected System:** [System Name]
**Requested By:** [Name]
**Date:** [Date]

### Business Justification
[Explain why the vulnerability cannot be remediated]

### Compensating Controls
- [ ] Control 1: [Description]
- [ ] Control 2: [Description]
- [ ] Control 3: [Description]

### Residual Risk Assessment
- **Likelihood:** [High/Medium/Low]
- **Impact:** [High/Medium/Low]
- **Residual Risk:** [Critical/High/Medium/Low]

### Review Schedule
- Next review date: [Date]
- Review frequency: [Monthly/Quarterly]

### Approvals
- [ ] Security Team Lead
- [ ] Engineering Manager
- [ ] CISO
- [ ] Business Owner
```

---

## Dependency Scanning

### Automated Scanning Pipeline

```yaml
# .github/workflows/security-scan.yml
name: Security Scan

on:
  push:
    branches: [main, develop]
  pull_request:
    branches: [main]
  schedule:
    - cron: '0 6 * * *'  # Daily at 6 AM

jobs:
  dependency-scan:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Run Snyk vulnerability scan
        uses: snyk/actions/node@master
        env:
          SNYK_TOKEN: ${{ secrets.SNYK_TOKEN }}
        with:
          args: --severity-threshold=high

      - name: Run npm audit
        run: npm audit --audit-level=high

      - name: Run Trivy filesystem scan
        uses: aquasecurity/trivy-action@master
        with:
          scan-type: 'fs'
          scan-ref: '.'
          severity: 'CRITICAL,HIGH'
          exit-code: '1'

  sast-scan:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Run Semgrep
        uses: returntocorp/semgrep-action@v1
        with:
          config: >-
            p/security-audit
            p/secrets
            p/owasp-top-ten
```

### Manual Dependency Review

```bash
# Node.js - Check for vulnerabilities
npm audit
npm audit --json > audit-report.json

# Python - Check for vulnerabilities
pip-audit
safety check -r requirements.txt

# Go - Check for vulnerabilities
govulncheck ./...

# Container images
trivy image myapp:latest
grype myapp:latest
```

### Dependency Update Strategy

| Update Type | Automation | Review Required |
|-------------|------------|-----------------|
| Security patch (same minor) | Auto-merge | No |
| Minor version | Auto-PR | Yes |
| Major version | Manual PR | Yes + Testing |
| Breaking change | Manual | Yes + Migration plan |

---

## Security Incident Response

### Incident Severity Levels

| Level | Description | Response Time | Escalation |
|-------|-------------|---------------|------------|
| SEV-1 | Active breach, data exfiltration | Immediate | CISO, Legal, Exec |
| SEV-2 | Confirmed intrusion, no data loss | 1 hour | Security Lead, Engineering |
| SEV-3 | Suspicious activity, potential breach | 4 hours | Security Team |
| SEV-4 | Policy violation, no immediate risk | 24 hours | Security Team |

### Incident Response Checklist

```markdown
## Incident Response Checklist

### 1. DETECT & IDENTIFY (0-15 min)
- [ ] Alert received and acknowledged
- [ ] Initial severity assessment
- [ ] Incident commander assigned
- [ ] Communication channel established

### 2. CONTAIN (15-60 min)
- [ ] Affected systems identified
- [ ] Network isolation if needed
- [ ] Credentials rotated if compromised
- [ ] Preserve evidence (logs, memory dumps)

### 3. ERADICATE (1-4 hours)
- [ ] Root cause identified
- [ ] Malware/backdoors removed
- [ ] Vulnerabilities patched
- [ ] Systems hardened

### 4. RECOVER (4-24 hours)
- [ ] Systems restored from clean backup
- [ ] Services brought back online
- [ ] Enhanced monitoring enabled
- [ ] User access restored

### 5. POST-INCIDENT (24-72 hours)
- [ ] Incident timeline documented
- [ ] Root cause analysis complete
- [ ] Lessons learned documented
- [ ] Preventive measures implemented
- [ ] Report to stakeholders
```

---

## Quick Reference

### Vulnerability Response SLAs

| Severity | Detection to Triage | Triage to Remediation |
|----------|--------------------|-----------------------|
| Critical | 4 hours | 24 hours |
| High | 24 hours | 7 days |
| Medium | 3 days | 30 days |
| Low | 7 days | 90 days |

### Common Vulnerability Databases

| Database | URL | Use Case |
|----------|-----|----------|
| NVD | nvd.nist.gov | CVE details, CVSS |
| MITRE CVE | cve.mitre.org | CVE registry |
| OSV | osv.dev | Open source vulns |
| GitHub Advisory | github.com/advisories | Package vulns |
| Snyk DB | snyk.io/vuln | Package vulns |

### Remediation Priority Formula

```
Priority Score = (CVSS × Exposure × Business_Impact) / Compensating_Controls

Where:
- CVSS: 0-10 (from NVD)
- Exposure: 1.0 (internal) to 2.0 (internet-facing)
- Business_Impact: 1.0 (low) to 2.0 (critical)
- Compensating_Controls: 1.0 (none) to 0.5 (multiple controls)
```
