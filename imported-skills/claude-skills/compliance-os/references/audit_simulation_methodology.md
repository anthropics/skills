# Audit Simulation Methodology — ISO 19011 + IIA IPPF + AICPA AT-C

This reference answers exactly one decision: **what does a realistic internal audit look like, and how do we generate a mock audit that prepares the team without breaking trust?**

Pair with `scripts/audit_simulator.py` for the deterministic mock audit generator.

## Why Simulate Audits?

External certification audits are high-stakes events. A team that has never been audited internally before its first stage 2 ISO certification audit will struggle even if every artefact is in place — interview cadence, document-pull SLAs, walk-through pacing are operational muscles built only by practice.

Mock audits provide:

- Operational practice (auditees experience the rhythm of an interview)
- Auditor-side practice (internal auditors practice their methodology before high-stakes certification audits)
- Discovery of gaps before they become findings
- Calibration of effort (how long does evidence assembly actually take?)
- Cross-training (auditors from one team learn another team's controls)

## Audit Standards That Govern Simulation

**ISO/IEC 19011:2018** — Guidelines for auditing management systems. Defines:

- Audit principles: integrity, fair presentation, due professional care, confidentiality, independence, evidence-based approach, risk-based approach
- Auditor competence (Clause 7)
- Audit process: initiating → preparing → conducting → reporting (Clauses 5–6)

**IIA International Professional Practices Framework (IPPF)** — internal-audit-specific:

- IPPF Standards 1000-1322 — Attribute Standards (purpose, independence, proficiency, due professional care, quality assurance)
- IPPF Standards 2000-2600 — Performance Standards (engagement planning through monitoring)
- Severity grading approach (rated finding scale)

**AICPA AT-C 105 + AU-C 240** — SOC 2 audit context: trust services criteria + auditor's responsibility framework.

## The Mock Audit Workflow

Compliance OS `audit_simulator.py` deterministically generates one stage of a mock audit. The full simulation lifecycle:

```
1. SCOPE       → define framework + controls in scope + auditee team
2. PREPARE     → audit_simulator.py outputs: findings + interview questions + document-review requests
3. CONDUCT     → simulated interview + document review (1-2 hours per control)
4. REPORT      → finding write-up + severity classification + corrective action assignment
5. CLOSE       → corrective action tracking through CAPA
```

## Finding Severity Distribution (the IIA expectation)

A healthy compliance program produces audits with this distribution:

| Severity | Healthy proportion | What it indicates |
|---|---|---|
| **Critical (major nonconformity)** | ≤ 15% | Blocks certification; requires major corrective action |
| **Major** | 15–25% | Important gaps requiring 30-day corrective action plans |
| **Minor** | 20–30% | Operational gaps requiring corrective action timeline |
| **Observation / OFI** | ≥ 40% | Improvement opportunities; no required action |

**Why this shape?** If 80% of findings are critical, either the audit was destructive (auditee not given fair chance to demonstrate compliance) or the program is genuinely failing. If 80% of findings are observations, the audit was too superficial. The compliance OS audit simulator enforces this shape by deterministic severity rotation.

A first audit (year 1) will skew higher to critical/major; a mature program (year 3+) skews to observations.

## Number of Findings Per Audit

ISO 19011 Clause 6 typical audit depth:

- Small scope (5 controls, 1 day): 5–10 findings
- Medium scope (10–15 controls, 3–5 days): 10–20 findings
- Full system audit (all clauses, 1–2 weeks): 25–50 findings

The simulator targets 8–15 findings per audit (medium scope) as the default.

## Interview Question Quality

Auditor questions follow the **walk-through pattern**:

1. **Open** — "Walk me through how this control is implemented day-to-day."
2. **Sample** — "Show me a specific example from the last 30 days."
3. **Drill** — "What happens if [edge case]?"
4. **Verify** — "Where is this documented?"

Each control gets 3–5 questions following this pattern. The simulator's `interview_questions()` function provides theme-specific questions per the IIA performance standards.

## Document-Review Requests

Per ISO 19011, the auditor reviews:

- The procedure (the "what should happen")
- The records (the "what actually happened")
- The evidence of management oversight (the "did anyone check?")

A document-review request typically asks for all three. The simulator's `document_requests()` function generates the request list per theme.

## Auditor Independence Test

Clause 9.2 of ISO management-system standards requires auditor independence. The simulator does NOT enforce auditor assignment (that's `aims_audit_scheduler.py` for ISO 42001 or `isms_audit_scheduler.py` for ISO 27001) but the workflow assumes an independent auditor.

**Independence rules:**
- Auditor cannot audit their own work
- Auditor reports to a different chain of command than the auditee
- For small organizations, rotating auditors between teams + occasional external auditor satisfies independence

## Finding Categories (the taxonomy)

The simulator uses 5 finding themes mapped to common control families:

| Theme | Maps to control families |
|---|---|
| `access_control` | ISO 27001 A.5.15 / A.8.2 / A.8.3; SOC 2 CC6.1-6.3; ISO 42001 A.4.4 |
| `logging_monitoring` | ISO 27001 A.8.15 / A.8.16; SOC 2 CC7.1-7.2; ISO 42001 A.9.3 / A.9.4 |
| `change_management` | ISO 27001 A.8.32; SOC 2 CC8.1; ISO 42001 A.6.2.5 |
| `supplier_mgmt` | ISO 27001 A.5.19-A.5.22; SOC 2 CC9.2; ISO 42001 A.10.2; GDPR Art. 28 |
| `incident_response` | ISO 27001 A.5.24-27, A.6.8; SOC 2 CC7.3-7.5; ISO 42001 A.8.4; EU AI Act Art. 73; GDPR Art. 33-34 |

This taxonomy covers the highest-leverage controls across the 9 supported frameworks. Adding new themes is a matter of extending `FINDING_TEMPLATES` + `CONTROL_TO_THEME` mappings.

## Anti-Patterns in Audit Simulation

1. **Auditing for trapping vs auditing for evidence.** Mock audits aim to surface gaps, not embarrass the auditee. If team morale drops after the mock, the audit was structured wrong.
2. **Skipping the "obvious" controls.** Critical findings often hide in mundane controls (e.g., terminated employee with retained access). Simulator deliberately includes prosaic theme rotation.
3. **No prior-year follow-up.** The simulator's `prior_year_findings_open` parameter forces the first finding to be a follow-up. Real audits always follow up on prior open findings (ISO 19011 Clause 6.3).
4. **One severity-skewed audit.** Distribution rule guards against this; if all findings are critical or all are observations, recalibrate the audit scope or methodology.

## When This Reference Doesn't Help

- **Specific industry-vertical audit requirements.** Use sectoral skills (financial, healthcare).
- **Auditor competence + certification.** See ISACA CISA, IRCA Lead Auditor courses.
- **Audit report-writing detail.** See ISO 19011 Clause 6.5 + IIA performance standards 2410–2440.

---

**Source authorities (non-exhaustive):**

- **ISO/IEC 19011:2018** — Guidelines for auditing management systems (the canonical methodology)
- **IIA International Professional Practices Framework (IPPF)** — Attribute Standards 1000-1322 + Performance Standards 2000-2600
- **AICPA AT-C 105** — Trust Services Criteria attestation engagement
- **AICPA AU-C 240** — Auditor's responsibilities relating to fraud (financial audit, conceptually applied)
- **ISACA CISA Review Manual** (27th ed., 2024) — IS audit practitioner methodology
- **ASQ Certified Quality Auditor (CQA) Body of Knowledge** — quality audit methodology
- **NIST SP 800-53A Rev 5** — Assessing Security and Privacy Controls (assessment procedures for each control)
- **ISO/IEC 17021-1:2015** — Conformity assessment requirements for bodies providing audit and certification
- **IRCA (International Register of Certificated Auditors)** — Lead auditor certification programme materials
- **The Open Group** — Open FAIR (Factor Analysis of Information Risk) for risk-based audit prioritization
