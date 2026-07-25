---
name: "isms-audit-expert"
description: Information Security Management System (ISMS) audit expert for ISO 27001 compliance verification, security control assessment, and certification support. Use when the user mentions ISO 27001, ISMS audit, Annex A controls, Statement of Applicability (SOA), gap analysis, nonconformity management, internal audit, surveillance audit, or security certification preparation. Helps review control implementation evidence, document audit findings, classify nonconformities, generate risk-based audit plans, map controls to Annex A requirements, prepare Stage 1 and Stage 2 audit documentation, and support corrective action workflows.
triggers:
  - ISMS audit
  - ISO 27001 audit
  - security audit
  - internal audit ISO 27001
  - security control assessment
  - certification audit
  - surveillance audit
  - audit finding
  - nonconformity
---

# ISMS Audit Expert

Internal and external ISMS audit management for ISO 27001 compliance verification, security control assessment, and certification support.

## Table of Contents

- [Audit Program Management](#audit-program-management)
- [Audit Execution](#audit-execution)
- [Control Assessment](#control-assessment)
- [Finding Management](#finding-management)
- [Certification Support](#certification-support)
- [Tools](#tools)
- [References](#references)

---

## Audit Program Management

### Risk-Based Audit Schedule

| Risk Level | Audit Frequency | Examples |
|------------|-----------------|----------|
| Critical | Quarterly | Privileged access, vulnerability management, logging |
| High | Semi-annual | Access control, incident response, encryption |
| Medium | Annual | Policies, awareness training, physical security |
| Low | Annual | Documentation, asset inventory |

### Annual Audit Planning Workflow

1. Review previous audit findings and risk assessment results
2. Identify high-risk controls and recent security incidents
3. Determine audit scope based on ISMS boundaries
4. Assign auditors ensuring independence from audited areas
5. Create audit schedule with resource allocation
6. Obtain management approval for audit plan
7. **Validation:** Audit plan covers all Annex A controls within certification cycle

### Auditor Competency Requirements

- ISO 27001 Lead Auditor certification (preferred)
- No operational responsibility for audited processes
- Understanding of technical security controls
- Knowledge of applicable regulations (GDPR, HIPAA)

---

## Audit Execution

### Pre-Audit Preparation

1. Review ISMS documentation (policies, SoA, risk assessment)
2. Analyze previous audit reports and open findings
3. Prepare audit plan with interview schedule
4. Notify auditees of audit scope and timing
5. Prepare checklists for controls in scope
6. **Validation:** All documentation received and reviewed before opening meeting

### Audit Conduct Steps

1. **Opening Meeting**
   - Confirm audit scope and objectives
   - Introduce audit team and methodology
   - Agree on communication channels and logistics

2. **Evidence Collection**
   - Interview control owners and operators
   - Review documentation and records
   - Observe processes in operation
   - Inspect technical configurations

3. **Control Verification**
   - Test control design (does it address the risk?)
   - Test control operation (is it working as intended?)
   - Sample transactions and records
   - Document all evidence collected

4. **Closing Meeting**
   - Present preliminary findings
   - Clarify any factual inaccuracies
   - Agree on finding classification
   - Confirm corrective action timelines

5. **Validation:** All controls in scope assessed with documented evidence

---

## Control Assessment

### Control Testing Approach

1. Identify control objective from ISO 27002
2. Determine testing method (inquiry, observation, inspection, re-performance)
3. Define sample size based on population and risk
4. Execute test and document results
5. Evaluate control effectiveness
6. **Validation:** Evidence supports conclusion about control status

For detailed technical verification procedures by Annex A control, see [security-control-testing.md](references/security-control-testing.md).

---

## Finding Management

### Finding Classification

| Severity | Definition | Response Time |
|----------|------------|---------------|
| Major Nonconformity | Control failure creating significant risk | 30 days |
| Minor Nonconformity | Isolated deviation with limited impact | 90 days |
| Observation | Improvement opportunity | Next audit cycle |

### Finding Documentation Template

```
Finding ID: ISMS-[YEAR]-[NUMBER]
Control Reference: A.X.X - [Control Name]
Severity: [Major/Minor/Observation]

Evidence:
- [Specific evidence observed]
- [Records reviewed]
- [Interview statements]

Risk Impact:
- [Potential consequences if not addressed]

Root Cause:
- [Why the nonconformity occurred]

Recommendation:
- [Specific corrective action steps]
```

### Corrective Action Workflow

1. Auditee acknowledges finding and severity
2. Root cause analysis completed within 10 days
3. Corrective action plan submitted with target dates
4. Actions implemented by responsible parties
5. Auditor verifies effectiveness of corrections
6. Finding closed with evidence of resolution
7. **Validation:** Root cause addressed, recurrence prevented

---

## Certification Support

### Stage 1 Audit Preparation

Ensure documentation is complete:
- [ ] ISMS scope statement
- [ ] Information security policy (management signed)
- [ ] Statement of Applicability
- [ ] Risk assessment methodology and results
- [ ] Risk treatment plan
- [ ] Internal audit results (past 12 months)
- [ ] Management review minutes

### Stage 2 Audit Preparation

Verify operational readiness:
- [ ] All Stage 1 findings addressed
- [ ] ISMS operational for minimum 3 months
- [ ] Evidence of control implementation
- [ ] Security awareness training records
- [ ] Incident response evidence (if applicable)
- [ ] Access review documentation

### Surveillance Audit Cycle

| Period | Focus |
|--------|-------|
| Year 1, Q2 | High-risk controls, Stage 2 findings follow-up |
| Year 1, Q4 | Continual improvement, control sample |
| Year 2, Q2 | Full surveillance |
| Year 2, Q4 | Re-certification preparation |

**Validation:** No major nonconformities at surveillance audits.

---

## Tools

### scripts/

| Script | Purpose | Usage |
|--------|---------|-------|
| `isms_audit_scheduler.py` | Generate risk-based audit plans | `python scripts/isms_audit_scheduler.py --year 2025 --format markdown` |

### Audit Planning Example

```bash
# Generate annual audit plan
python scripts/isms_audit_scheduler.py --year 2025 --output audit_plan.json

# With custom control risk ratings
python scripts/isms_audit_scheduler.py --controls controls.csv --format markdown
```

---

## References

| File | Content |
|------|---------|
| [iso27001-audit-methodology.md](references/iso27001-audit-methodology.md) | Audit program structure, pre-audit phase, certification support |
| [security-control-testing.md](references/security-control-testing.md) | Technical verification procedures for ISO 27002 controls |
| [cloud-security-audit.md](references/cloud-security-audit.md) | Cloud provider assessment, configuration security, IAM review |

---

## Audit Performance Metrics

| KPI | Target | Measurement |
|-----|--------|-------------|
| Audit plan completion | 100% | Audits completed vs. planned |
| Finding closure rate | >90% within SLA | Closed on time vs. total |
| Major nonconformities | 0 at certification | Count per certification cycle |
| Audit effectiveness | Incidents prevented | Security improvements implemented |
