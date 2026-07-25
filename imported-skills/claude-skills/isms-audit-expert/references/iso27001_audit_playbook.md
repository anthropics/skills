# ISO/IEC 27001:2022 Internal Audit Playbook

This reference answers exactly one decision: **how do we prepare for and conduct an ISO 27001 internal audit (Clause 9.2) that produces actionable findings without burning the auditee team?**

Pair with `scripts/isms_audit_scheduler.py` (this skill) for cadence + auditor independence and with `compliance-os/scripts/audit_simulator.py` for mock-audit preparation.

## When to Use This Playbook

- Annual Clause 9.2 internal audit programme
- Pre-stage-1 certification readiness check
- Surveillance audit preparation (year 2 / year 3 of cert cycle)
- Post-incident audit (e.g., breach triggers ad-hoc ISMS audit)
- Onboarding a new business unit into existing ISMS scope

## The 7-Phase Audit Workflow

```
[ Plan ] -> [ Prepare ] -> [ Open ] -> [ Field ] -> [ Close ] -> [ Report ] -> [ Track ]
```

### Phase 1 — Plan (1-2 weeks pre-audit)

- Confirm scope: which Annex A controls, which business units, which clauses
- Confirm auditor independence (no self-audit; rotate across teams)
- Pull prior-year findings + open nonconformities for follow-up
- Define sampling approach (stratified by risk; not random)
- Communicate dates to auditees ≥ 2 weeks in advance

**Outputs:** audit plan (1 page), auditor assignments, document-request list

### Phase 2 — Prepare (1 week pre-audit)

- Auditee assembles document evidence in advance
- Auditor reviews documents BEFORE fieldwork (do not waste interview time reading docs)
- Pre-fieldwork checklist: are documents under version control? Are records signed? Are dates within retention?
- Auditor runs `audit_simulator.py` to mentally rehearse finding scenarios

**Outputs:** prepared document folder, auditor mental model of likely findings

### Phase 3 — Open (30 min, day 1)

- Opening meeting with auditee leadership + key contributors
- State scope, criteria (which Annex A controls), timeline, communication plan
- Set expectations: this is a check on the system, not on individuals
- Confirm safe-to-fail discipline — finding ≠ punishment

**Outputs:** opening minutes; auditee buy-in

### Phase 4 — Field (2-5 days for medium scope)

The core. For each scoped control:

1. **Interview the control owner** — open question, sample drill-down, walk-through
2. **Inspect the record(s)** — pull samples from logs / tickets / records, not curated demos
3. **Cross-reference** — does the record match the procedure? Does management oversight exist?
4. **Document the finding** on the spot — control + observation + evidence + severity

Interview pattern (per ISO 19011 Clause 6):
- "Walk me through how this control is implemented day-to-day."
- "Show me a specific example from the last 30 days."
- "What happens if [edge case]?"
- "Where is this documented?"

**Outputs:** finding worksheets (one per control); severity ratings

### Phase 5 — Close (1-2 hours, last day)

- Closing meeting with auditee team
- Walk through preliminary findings (no surprises in the written report)
- Allow auditee to provide additional evidence for borderline findings
- Confirm corrective action ownership before the report is written
- Agree on draft-report timeline (typically 1-2 weeks)

**Outputs:** closing minutes; preliminary finding agreement

### Phase 6 — Report (1-2 weeks post-fieldwork)

Per ISO 19011 Clause 6.5, the audit report must include:

- Audit objectives, scope, criteria, dates
- Audit team and auditees
- Summary of findings by severity
- Per-finding: control + observation + evidence + severity + corrective action recommendation
- Conclusion: ISMS adequacy + effectiveness verdict
- Distribution list

**Severity grades** (Clause 9.2 compatible):

| Grade | Definition | Treatment |
|---|---|---|
| **Critical (Major NC)** | Absence of, or systemic failure to implement, a required ISMS process | Blocks stage 1 certification; 30-day plan + closure required before progress |
| **Major** | Material gap in a required control | Corrective action plan within 30 days |
| **Minor** | Localized gap; control works overall | Corrective action within 90 days |
| **Observation / OFI** | Improvement opportunity; no nonconformity | Optional; recommendation only |

Healthy distribution: ≥ 40% observation, ≤ 15% critical.

**Outputs:** signed audit report; corrective action assignments

### Phase 7 — Track (ongoing)

- Open findings tracked through existing CAPA system (Clause 10.2)
- Verify closure of each finding via evidence + re-test (do not accept self-attestation)
- Update risk register for residual risks identified
- Feed unresolved findings into next audit cycle + management review (Clause 9.3)

**Outputs:** closed findings + verification evidence; updates to risk register and management review inputs

## Annex A Scope Prioritization (for fieldwork)

ISO 27001:2022 Annex A has 93 controls grouped into 4 themes (A.5 organizational, A.6 people, A.7 physical, A.8 technological). Audit fieldwork should NOT attempt all 93 in one audit — use the 3-year rolling cycle.

**High-priority controls (audit annually):**

| Control | Why prioritize annually |
|---|---|
| A.5.1 — Policies for information security | Foundation; audit changes |
| A.5.9-10 — Inventory of assets + acceptable use | Drives everything else |
| A.5.15 — Access control | Highest-leakage area |
| A.5.19-21 — Supplier management | Most-cited finding area |
| A.5.24-27 — Incident management + Article 33 GDPR alignment | High-stakes |
| A.5.34 — Privacy & PII | GDPR overlap; expand if EU data |
| A.6.3 — Awareness, education, training | Always sampled |
| A.6.7 — Remote working | Pandemic legacy; high audit value |
| A.6.8 — Information security event reporting | Connects to incident management |
| A.8.2-3 — Privileged access; Information access restriction | Pair with A.5.15 |
| A.8.7 — Protection against malware | Always cited |
| A.8.15-16 — Logging + Monitoring | Pair with A.5.24-27 |
| A.8.32 — Change management | High-leakage; pair with vulnerability/patch mgmt |

**Lower-priority controls (audit on rolling 3-year cycle):**

A.5.2 / A.5.3 / A.5.4 / A.5.6 / A.5.7 / A.5.8 / A.5.11 / A.5.13 / A.5.14 / A.5.16 / A.5.17 / A.5.18 / A.5.22 / A.5.23 / A.5.28 / A.5.29 / A.5.30 / A.5.31 / A.5.32 / A.5.33 / A.5.35 / A.5.36 / A.5.37 / A.6.1 / A.6.2 / A.6.4 / A.6.5 / A.6.6 / A.7 (all physical) / A.8.1 / A.8.4 / A.8.5 / A.8.6 / A.8.8 / A.8.9 / A.8.10 / A.8.11 / A.8.12 / A.8.13 / A.8.14 / A.8.17 / A.8.18 / A.8.19 / A.8.20 / A.8.21 / A.8.22 / A.8.23 / A.8.24 / A.8.25-31 (SDLC controls)

## Common Stage 1 / Stage 2 Findings (the patterns)

Based on practitioner reports of common ISO 27001:2022 findings:

1. **Risk register exists but treatment plans are generic.** "Apply A.7.3" without specific implementation.
2. **Asset inventory missing cloud / SaaS / AI tools.** Engineers stopped registering as they multiplied.
3. **Privileged access reviewed annually instead of quarterly.** Find orphaned accounts.
4. **Supplier reviews unsigned or undated.** Procurement collected them; nobody reviewed.
5. **Incident records lack documented post-incident review within 30 days.**
6. **Change advisory board exists but rubber-stamps.** No rejected changes in last 6 months.
7. **Internal audit programme doesn't cover all clauses + applicable controls over 3-year cycle.**
8. **Management review missing required Article 9.3 inputs** (KPI trends, audit findings, risk changes).
9. **Vulnerability management without defined SLAs by severity.**
10. **BCP/DRP exists but never tested.**

## Cross-Framework Reuse

This ISO 27001 audit pattern is the foundation for:

- **SOC 2** — ~75% control overlap; same evidence with TSC-specific formatting (`soc2_audit_playbook.md`)
- **ISO 42001** — Clauses 4-10 reuse ~60%; Annex A overlap on data + supplier; AI-specific Annex A.5/A.6/A.9 net-new
- **GDPR** — Article 32 organizational measures reuse heavily (`gdpr_audit_playbook.md`)
- **NIST CSF profiles** — common control vocabulary

Pair with `compliance-os/references/multi_framework_audit_playbook.md` for orchestrating audits across multiple frameworks.

## When This Reference Doesn't Help

- **Specific Annex A control text.** See ISO 27001:2022 + ISO 27002:2022 (implementation guidance).
- **Sectoral overlays.** Financial (NYDFS), healthcare (HIPAA), critical infra (NIS2) — sector-specific.
- **External certification audit detail.** This is the **internal** audit playbook; external (stage 1 / stage 2) audits are conducted by accredited bodies and follow ISO 17021.

---

**Source authorities (non-exhaustive):**

- **ISO/IEC 27001:2022** — the standard (Clause 9.2 internal audit + Annex A 93 controls)
- **ISO/IEC 27002:2022** — Information security controls (implementation guidance for Annex A)
- **ISO/IEC 19011:2018** — Guidelines for auditing management systems
- **ISO/IEC 17021-1:2015** — Conformity assessment requirements for bodies providing audit and certification (the external-audit standard; informs internal-audit expectations)
- **IIA International Professional Practices Framework** — Standards 1000-2600 (internal audit attribute + performance)
- **NIST SP 800-53A Rev 5** — Assessing Security and Privacy Controls (assessment procedures per control)
- **ISACA CISA Review Manual** (27th ed., 2024) — IS audit methodology
- **ASQ Certified Quality Auditor (CQA) Body of Knowledge** — quality audit methodology
- **Industry retrospectives** — common findings from accredited certification bodies (BSI, DNV, Bureau Veritas published case studies)
- **The Open Group** — Open FAIR for risk-based audit prioritization
