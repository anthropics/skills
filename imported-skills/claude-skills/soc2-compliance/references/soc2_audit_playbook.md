# SOC 2 Type II Audit Playbook

This reference answers exactly one decision: **how do we prepare for and operate the SOC 2 Type II examination cycle — the 6-12 month observation period that produces the bound SOC 2 report?**

Pair with this skill's Python tools (`control_matrix_builder.py`, `evidence_tracker.py`, `gap_analyzer.py`) and `compliance-os/scripts/audit_simulator.py` for mock-audit preparation.

## Key Difference from ISO Audits

SOC 2 is an **AICPA attestation**, not an ISO certification. Implications:

- Performed by a licensed CPA firm (not a certification body)
- Type I: design effectiveness at a point in time (snapshot)
- Type II: operating effectiveness over a period (typically 6-12 months) — the report enterprise buyers actually want
- Output: bound report distributed under NDA, not a public certificate
- Renewed annually (continuous Type II reports rather than 3-year cert cycle)
- **The customer (your buyer) cares about the report's "no exceptions" verdict on the Trust Services Criteria**

SOC 2 is heavily about **evidence sampling over the observation period** — your control must operate consistently for the full period, not just on audit day.

## When to Use This Playbook

- Type I readiness (point-in-time snapshot before first Type II)
- Type II readiness (annual; observation period typically 6-12 months)
- Pre-bid response to enterprise procurement asking for "SOC 2 Type II"
- Audit firm scoping discussion
- Quarterly internal pre-audit during Type II observation period
- New control implementation during observation period (timing impacts report)

## The Five Trust Services Criteria (TSC)

SOC 2 uses the 2017 TSC as updated in 2022. Always-included is Security; the other 4 are elective based on customer requirements:

| TSC | Always required? | What it covers |
|---|---|---|
| **Security (Common Criteria CC1-CC9)** | YES — always | Common criteria across all TSC categories |
| **Availability (A1)** | Optional | System available for operation + use as committed |
| **Processing Integrity (PI1)** | Optional | System processing complete + valid + accurate + timely + authorized |
| **Confidentiality (C1)** | Optional | Information designated as confidential is protected |
| **Privacy (P1-P8)** | Optional | Personal information collected + used + retained + disclosed per privacy notice |

**Common scoping:**
- Pure infrastructure SaaS: Security + Availability + Confidentiality
- SaaS handling consumer data: + Privacy
- SaaS processing financial / sensitive data: + Processing Integrity
- B2B SaaS with no consumer data: typically Security + Availability + Confidentiality

## The Type II Workflow (12-month cycle)

```
[ Month 0: Type I if needed ] -> [ Month 1-2: Pre-observation prep ]
                                            |
                                            v
[ Month 3-9: Observation period (audit firm samples evidence) ]
                                            |
                                            v
[ Month 10: Field testing + walkthroughs ] -> [ Month 11: Report draft + management response ]
                                            |
                                            v
[ Month 12: Final report issued ]
```

### Pre-Observation Phase (Months 1-2)

Critical setup work. Audit firm walks through:

- Scoping decisions (which TSC, which systems, which entities)
- Description of system per AICPA AT-C 205 — narrative + boundaries + components
- Mapping each in-scope control to TSC criteria
- Defining sampling approach + frequency

**Tip:** if you're implementing new controls during this phase, do so BEFORE the observation period starts. New controls mid-observation create gaps in the "operated consistently" assertion.

### Observation Period (Months 3-9)

The audit firm samples evidence from this period. You operate normally; evidence is captured and preserved.

**Critical disciplines:**

1. **Don't change controls mid-period** without documented change management
2. **Don't skip controls** even for one cycle (quarterly access review skipped one quarter = a likely exception in the report)
3. **Capture evidence in real-time** — not assembled retrospectively at audit time
4. **Document every exception** — exceptions are not death sentences if management remediation is documented

### Field Testing (Month 10)

The audit firm pulls samples:

- For each control, pulls samples from the observation period
- Typically sample size: 30-40 samples for high-population controls (logs, tickets); 100% for low-population controls (annual training, quarterly reviews)
- Walkthrough interviews for design verification
- Tests of operating effectiveness for Type II assertion

### Report (Months 11-12)

The SOC 2 Type II report contains:

- **Section 1:** Auditor's opinion (the page the customer reads first)
- **Section 2:** Management assertion
- **Section 3:** System description
- **Section 4:** Trust services criteria + controls + test results + exceptions

A "clean" opinion = unmodified opinion = no exceptions material to overall conclusion. Customer expects clean. Even one or two exceptions trigger customer questions.

## Most Common SOC 2 Type II Exceptions

Based on practitioner reports of common Type II exceptions:

1. **Quarterly access review not completed for one quarter during observation period**
2. **Vulnerability scan results not remediated within stated SLA on N of M samples**
3. **Background check evidence missing for one or two employees hired during period**
4. **Annual training not 100% complete by stated deadline** (someone always misses)
5. **Change ticket without complete documentation** (testing evidence or approval missing)
6. **Logging gap detected (e.g., 3 hours of missing logs on one date)**
7. **Encryption configuration not validated** for one or two new resources spun up during period
8. **Vendor security review not refreshed** during observation period for one or two critical vendors
9. **Incident response not documented within stated SLA** for one or two minor incidents
10. **Customer notification delayed past committed timeline** for one event

**Strategy:** even one exception is OK if remediated and documented. The auditor cares about whether the exception is material — meaning the control "operates" in aggregate.

## Type II vs Type I Discipline Delta

| Aspect | Type I | Type II |
|---|---|---|
| Evidence required | Point-in-time | Continuous over observation period |
| Sampling | Limited | Statistically meaningful samples per control |
| Cost | Lower (months 1-3) | Higher (months 1-12) |
| Customer trust | Limited | Strong |
| Renewal | Build-once | Annual recurring |

Most enterprise customers will not accept Type I beyond first year. Type I is a stepping-stone, not a steady state.

## ISO 27001 ↔ SOC 2 Reuse

The highest-leverage cross-framework pair. ~75% of ISO 27001:2022 Annex A controls map to SOC 2 TSC. Pattern:

- If you have mature ISO 27001 → adding SOC 2 takes ~3 months incremental work
- If you have mature SOC 2 → adding ISO 27001 takes ~3-6 months (ISO requires additional management-system formality: scope statement, internal audit programme, formal management review)

Same controls; different formatting. See `compliance-os/references/cross_framework_overlap.md` for the merged-control catalogue.

## Privacy TSC + GDPR Overlap

If Privacy (P-series) is in scope:

- P1.1 (Notice) ↔ GDPR Articles 13-14
- P2.1 (Choice + consent) ↔ GDPR Article 7 + 8
- P3.1 (Collection) ↔ GDPR Article 5 minimization
- P4 (Use, retention, disposal) ↔ GDPR Article 5(1)(c)-(e)
- P5 (Access) ↔ GDPR Article 15
- P6.1 (Disclosure) ↔ GDPR Article 13/14 + DPA agreements
- P7 (Quality) ↔ GDPR Article 5(1)(d)
- P8 (Monitoring + enforcement) ↔ GDPR Article 24 (accountability)

If both apply, build evidence to GDPR specification (which is more prescriptive) and report against SOC 2 TSC.

## Cross-Framework Reuse

SOC 2 audit work supports:

- **ISO 27001** — primary cross-walk (~75% control reuse)
- **PCI DSS** — overlap on access control, encryption, logging, vulnerability mgmt
- **HITRUST** — overlap on security controls
- **NIST CSF** — common control vocabulary

Pair with `compliance-os/references/multi_framework_audit_playbook.md`.

## When This Reference Doesn't Help

- **SOC 1 (financial reporting controls)** — different scope; engage financial-audit-focused firm
- **SOC 3 (general use report)** — different distribution rules; less common
- **HITRUST CSF certification** — separate framework
- **Vendor risk vs SOC 2 report consumption** — different perspective; downstream activity

---

**Source authorities (non-exhaustive):**

- **AICPA AT-C 105 + AT-C 205** — Attestation engagement standards
- **AICPA AU-C 240** — Auditor's responsibilities relating to fraud (conceptually applied)
- **AICPA Trust Services Criteria (2017 + 2022 update)** — TSC text
- **AICPA SOC 2 Reporting Guide** (continuously updated)
- **ISACA CISA Review Manual** — IS audit methodology overlap
- **PCAOB standards** — for audit-firm methodology context
- **NIST SP 800-53A Rev 5** — for assessment procedure precedent
- **ISO/IEC 27001:2022 + Annex A** — the primary cross-walk standard
- **Industry retrospectives** — published reports from major audit firms (Big 4 + Schellman + Coalfire + A-LIGN) on common SOC 2 exceptions
- **The Open Group + IIA** — internal audit methodology informing pre-engagement work
