# Risk Assessment Methodology Guide

Comprehensive guidance for conducting information security risk assessments per ISO 27001 Clause 6.1.2.

---

## Table of Contents

- [Risk Assessment Process](#risk-assessment-process)
- [Asset Identification](#asset-identification)
- [Threat Analysis](#threat-analysis)
- [Vulnerability Assessment](#vulnerability-assessment)
- [Risk Calculation](#risk-calculation)
- [Risk Treatment](#risk-treatment)
- [Templates and Tools](#templates-and-tools)

---

## Risk Assessment Process

### ISO 27001 Requirements (Clause 6.1.2)

The organization shall:
1. Define risk assessment process
2. Establish risk criteria (acceptance, assessment)
3. Identify information security risks
4. Analyze and evaluate risks
5. Ensure repeatable and consistent results

### Process Overview

```
1. Context → 2. Asset ID → 3. Threat ID → 4. Vuln ID → 5. Risk Calc → 6. Treatment
     ↑                                                                      |
     └──────────────────── Review & Update ←───────────────────────────────┘
```

---

## Asset Identification

### Asset Categories

| Category | Examples | Typical Classification |
|----------|----------|----------------------|
| Information | Patient records, source code, contracts | Confidential-Critical |
| Software | EHR systems, databases, custom apps | High-Critical |
| Hardware | Servers, medical devices, network gear | High |
| Services | Cloud hosting, backup, email | High |
| People | Admin accounts, key personnel | Critical |
| Intangibles | Reputation, intellectual property | High |

### Classification Scheme

| Level | Definition | Impact if Compromised |
|-------|------------|----------------------|
| Critical | Business-critical, regulated data | Severe - regulatory fines, safety risk |
| High | Important business data | Significant - major disruption |
| Medium | Internal business data | Moderate - operational impact |
| Low | Non-sensitive data | Minor - limited impact |
| Public | Intended for public release | Minimal - no impact |

### Asset Inventory Template

| ID | Asset Name | Type | Owner | Location | Classification | Value |
|----|------------|------|-------|----------|----------------|-------|
| A001 | Patient DB | Information | DBA Lead | AWS RDS | Critical | $5M |
| A002 | EHR App | Software | App Team | AWS ECS | Critical | $2M |
| A003 | Admin Creds | Access | Security | Vault | Critical | N/A |

---

## Threat Analysis

### Healthcare Threat Landscape

| Threat | Likelihood | Target Assets | Motivation |
|--------|------------|---------------|------------|
| Ransomware | High | All systems | Financial |
| Data breach | High | Patient data | Financial/Competitive |
| Phishing | Very High | User accounts | Access |
| Insider threat | Medium | Sensitive data | Various |
| DDoS | Medium | Public services | Disruption |
| Supply chain | Medium | Third-party systems | Access |

### Threat Modeling Approaches

**STRIDE Model:**
- **S**poofing identity
- **T**ampering with data
- **R**epudiation
- **I**nformation disclosure
- **D**enial of service
- **E**levation of privilege

**Threat Actor Categories:**

| Actor | Capability | Motivation | Typical Targets |
|-------|-----------|------------|-----------------|
| Nation-state | Very High | Espionage, disruption | Critical infrastructure |
| Organized crime | High | Financial gain | Healthcare, finance |
| Hacktivists | Medium | Ideology | Public-facing systems |
| Insiders | Varies | Financial, revenge | Sensitive data |
| Script kiddies | Low | Notoriety | Unpatched systems |

---

## Vulnerability Assessment

### Vulnerability Categories

| Category | Examples | Detection Method |
|----------|----------|------------------|
| Technical | Unpatched software, weak configs | Vulnerability scans |
| Process | Missing procedures, gaps | Process audits |
| People | Lack of training, social engineering | Phishing tests |
| Physical | Inadequate access controls | Physical audits |

### Vulnerability Scoring (CVSS Alignment)

| Score Range | Severity | Example |
|-------------|----------|---------|
| 9.0-10.0 | Critical | RCE without authentication |
| 7.0-8.9 | High | Authentication bypass |
| 4.0-6.9 | Medium | Information disclosure |
| 0.1-3.9 | Low | Minor configuration issue |

### Vulnerability Sources

1. **Automated Scans:** Nessus, Qualys, OpenVAS
2. **Penetration Testing:** Annual third-party tests
3. **Code Analysis:** SAST/DAST tools
4. **Configuration Audits:** CIS benchmarks
5. **Threat Intelligence:** CVE feeds, vendor advisories

---

## Risk Calculation

### Risk Formula

```
Risk = Likelihood × Impact
```

### Likelihood Scale (1-5)

| Score | Likelihood | Definition |
|-------|-----------|------------|
| 5 | Almost Certain | Expected to occur multiple times per year |
| 4 | Likely | Expected to occur at least once per year |
| 3 | Possible | Could occur within 2-3 years |
| 2 | Unlikely | Could occur within 5 years |
| 1 | Rare | Unlikely to occur |

### Impact Scale (1-5)

| Score | Impact | Financial | Operational | Reputational |
|-------|--------|-----------|-------------|--------------|
| 5 | Catastrophic | >$10M | Total shutdown | International news |
| 4 | Major | $1M-$10M | Major disruption | National news |
| 3 | Moderate | $100K-$1M | Significant impact | Local news |
| 2 | Minor | $10K-$100K | Minor disruption | Complaints |
| 1 | Negligible | <$10K | Minimal impact | Internal only |

### Risk Matrix

|     | Impact 1 | Impact 2 | Impact 3 | Impact 4 | Impact 5 |
|-----|----------|----------|----------|----------|----------|
| **L5** | 5 (Low) | 10 (Med) | 15 (High) | 20 (Crit) | 25 (Crit) |
| **L4** | 4 (Low) | 8 (Med) | 12 (Med) | 16 (High) | 20 (Crit) |
| **L3** | 3 (Min) | 6 (Low) | 9 (Med) | 12 (Med) | 15 (High) |
| **L2** | 2 (Min) | 4 (Low) | 6 (Low) | 8 (Med) | 10 (Med) |
| **L1** | 1 (Min) | 2 (Min) | 3 (Min) | 4 (Low) | 5 (Low) |

### Risk Levels

| Level | Score Range | Action Required |
|-------|-------------|-----------------|
| Critical | 20-25 | Immediate action, escalate to management |
| High | 15-19 | Treatment plan within 30 days |
| Medium | 10-14 | Treatment plan within 90 days |
| Low | 5-9 | Accept or implement low-cost controls |
| Minimal | 1-4 | Accept risk, document decision |

---

## Risk Treatment

### Treatment Options (ISO 27001)

| Option | Description | When to Use |
|--------|-------------|-------------|
| Modify | Implement controls to reduce risk | Most risks |
| Avoid | Eliminate the risk source | Unacceptable risks |
| Share | Transfer via insurance/outsourcing | High financial impact |
| Retain | Accept the risk | Low risks, cost-prohibitive controls |

### Control Selection Criteria

1. **Effectiveness:** Reduces likelihood or impact
2. **Cost:** Implementation and maintenance costs
3. **Feasibility:** Technical and operational viability
4. **Compliance:** Meets regulatory requirements
5. **Integration:** Works with existing controls

### Residual Risk

After implementing controls:

```
Residual Risk = Inherent Risk × (1 - Control Effectiveness)
```

| Control Effectiveness | Residual Risk Factor |
|----------------------|---------------------|
| 90%+ | Very Low (0.1×) |
| 70-89% | Low (0.2-0.3×) |
| 50-69% | Moderate (0.4-0.5×) |
| <50% | Limited reduction |

---

## Templates and Tools

### Risk Register Template

| Risk ID | Asset | Threat | Vulnerability | L | I | Inherent | Control | Residual | Owner | Status |
|---------|-------|--------|---------------|---|---|----------|---------|----------|-------|--------|
| R001 | Patient DB | Data breach | Weak encryption | 4 | 5 | 20 | AES-256 | 8 | DBA | Open |
| R002 | Admin access | Credential theft | No MFA | 5 | 5 | 25 | MFA | 5 | Security | Closed |

### Risk Assessment Report Sections

1. **Executive Summary**
   - Key findings
   - Critical/high risks count
   - Overall risk posture

2. **Methodology**
   - Assessment scope
   - Criteria used
   - Limitations

3. **Asset Summary**
   - Asset inventory
   - Classification distribution

4. **Risk Findings**
   - Risk register
   - Heat map visualization
   - Trend analysis

5. **Recommendations**
   - Priority treatments
   - Timeline and resources
   - Residual risk projection

6. **Appendices**
   - Detailed asset list
   - Threat catalog
   - Control mapping
