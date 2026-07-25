# Multi-Framework Audit Playbook — Orchestrating Audits Across N Frameworks

This reference answers exactly one decision: **when 2+ frameworks operate simultaneously, how do we run audits in coordinated cycles with minimal duplication?**

Pair with `scripts/audit_simulator.py` (multi-framework mock audits) + the per-framework audit playbooks (`isms-audit-expert/references/iso27001_audit_playbook.md`, `qms-audit-expert/references/iso13485_audit_playbook.md`, `gdpr-dsgvo-expert/references/gdpr_audit_playbook.md`, `soc2-compliance/references/soc2_audit_playbook.md`).

## The Multi-Framework Audit Problem

Mature multi-framework programs face four orchestration challenges:

1. **Audit calendar conflicts** — surveillance audits stacking in same week, insufficient auditor capacity
2. **Auditor independence across frameworks** — same internal auditor pulled to audit own work in a different framework
3. **Evidence freshness mismatch** — Audit A wants Q3 data; Audit B (3 months later) wants same control's Q3+Q4 data
4. **Finding cross-impact** — a critical finding in ISO 27001 audit triggers compensating questions in SOC 2 audit

This playbook describes the integrated audit programme (IAP) pattern that solves these.

## The Integrated Audit Programme

```
                    Annual Compliance Calendar
                              |
        ┌─────────────────────┼─────────────────────┐
        |                     |                     |
   Q1: ISO 27001         Q2: ISO 42001        Q3: ISO 13485
   internal audit        internal audit       internal audit
   (auditor pool A)      (auditor pool B)     (auditor pool A)
                              |
                    Q4: Integrated Management
                    Review (Clause 9.3 across
                    all frameworks)
                              |
                    External surveillance audits
                    scheduled by certification body
```

The IAP coordinates:

- **Single audit programme document** covering all applicable frameworks
- **Single auditor pool** with skill-based + independence-based assignment
- **Single evidence pool** (per `evidence_pool_generator.py`) so audits cite shared evidence
- **Single management review** (per Annex SL) covering all frameworks' Clause 9.3 inputs

## The 12-Month Calendar Pattern

A typical mid-stage AI SaaS running ISO 27001 + SOC 2 + ISO 42001 + GDPR + EU AI Act:

| Quarter | Activity | Frameworks audited internally |
|---|---|---|
| **Q1** | ISO 27001 internal audit + SOC 2 Type II observation begins | 27001 + SOC 2 |
| **Q2** | ISO 42001 internal audit + EU AI Act readiness checkpoint | 42001 + AI Act |
| **Q3** | GDPR annual review + SOC 2 mid-period checkpoint | GDPR + SOC 2 |
| **Q4** | Integrated management review + SOC 2 Type II field + cert body surveillance audits | all |

External audits (certification body + SOC 2 audit firm) typically:

- Q1: ISO 27001 surveillance audit (timed to follow Q1 internal audit)
- Q3: SOC 2 Type II field testing (timed for Q4 report)
- Q4: ISO 42001 surveillance audit (timed to follow Q2 + Q4 internal audits)

## Auditor Independence Across Frameworks

ISO management-system standards (Clause 9.2 across 27001 / 42001 / 13485) all require auditor independence: nobody audits their own work. With multiple frameworks running, independence must be tracked **across** frameworks, not just within.

**Pattern:** maintain an auditor competence + independence matrix:

| Auditor | Owns (cannot audit) | Competent to audit |
|---|---|---|
| Alice | 27001 A.5.15 (access control); 42001 A.4.4 | 27001 except A.5.15; 42001 except A.4.4; all GDPR; all SOC 2 |
| Bob | 42001 A.6 (lifecycle); 13485 7.3 (design) | 27001; GDPR; SOC 2 |
| Carol (external) | (none — independent contractor) | All frameworks |
| Dave | 27001 A.5.19 (suppliers); GDPR Article 28 | 27001 except A.5.19; 42001; SOC 2; 13485 |

Use `aims_audit_scheduler.py` (ISO 42001) + per-framework scheduler patterns to enforce independence.

## Cross-Framework Finding Impact

A finding in one framework's audit often affects another. Pattern:

- **ISO 27001 A.5.15 finding** → likely SOC 2 CC6.1 finding (same evidence)
- **ISO 27001 A.5.19-21 finding** → likely SOC 2 CC9.2 finding + GDPR Article 28 finding
- **ISO 42001 Annex A.7.6 finding** → likely GDPR Article 35 DPIA finding
- **ISO 13485 Clause 7.3 finding** → likely EU MDR Annex II finding
- **GDPR Article 33 breach** → triggers ISO 27001 A.5.24 audit + EU AI Act Article 73 review

**Discipline:** when a finding is issued, the issuing auditor flags cross-framework impact in the finding worksheet. The compliance officer reviews and triggers corresponding follow-up across frameworks.

## Shared Evidence Discipline

Per `evidence_management.md`, the evidence pool has unified artefacts. Audit work cites these artefacts, not framework-specific copies.

**Anti-pattern:**

```
ISO 27001 audit asks for: "ISO 27001 access review records Q3"
SOC 2 audit asks for:    "SOC 2 access review records Q3"
Team produces TWO documents from same Okta export.
```

**Pattern:**

```
Both audits cite: "ev.access_review_quarterly Q3 2026" (single artefact)
Audit reports reference the shared artefact ID + framework-control mapping.
```

The audit report shows the auditor consulted the same evidence; framework-specific formatting happens in report assembly.

## Integrated Management Review (Clause 9.3 Across Frameworks)

Each management-system standard (27001, 42001, 13485, etc.) requires its own management review with prescribed inputs + outputs. Running 4 separate management reviews per year is unsustainable.

**Per Annex SL** (the high-level structure shared across ISO management-system standards), a single integrated management review can satisfy all of them if inputs cover every framework's prescribed list. Required inputs across the 5 most-common frameworks:

| Input | 27001 | 42001 | 13485 | 14001 | 9001 |
|---|---|---|---|---|---|
| Audit results | ✅ | ✅ | ✅ | ✅ | ✅ |
| Feedback from interested parties | ✅ | ✅ | ✅ | ✅ | ✅ |
| Risk + opportunity changes | ✅ | ✅ | ✅ | ✅ | ✅ |
| Performance of processes | ✅ | ✅ | ✅ | ✅ | ✅ |
| Nonconformities + CAPA | ✅ | ✅ | ✅ | ✅ | ✅ |
| Improvement opportunities | ✅ | ✅ | ✅ | ✅ | ✅ |
| AI-specific (drift, incidents, lifecycle) | — | ✅ | — | — | — |
| Customer feedback + complaints | — | ✅ | ✅ | — | ✅ |
| Resource needs | ✅ | ✅ | ✅ | ✅ | ✅ |

Outputs are similarly aligned: decisions on improvement, resource changes, scope adjustments, policy changes.

**Cadence:** annual minimum; quarterly preferred for mature multi-framework programs.

## Pre-Audit Readiness Checklist (per framework)

Universal pre-audit readiness (apply to each framework's internal audit):

- [ ] Scope confirmed (clauses + controls + business units in scope)
- [ ] Auditor independence verified (no self-audit; competence covers scope)
- [ ] Prior-year findings open list pulled + status reviewed
- [ ] Document evidence assembled in advance (auditor reads pre-fieldwork)
- [ ] Auditee leadership briefed; team availability confirmed
- [ ] Mock audit run via `audit_simulator.py` to surface likely findings
- [ ] Cross-framework impact considered (which findings might cascade)
- [ ] Audit plan circulated 2 weeks ahead

## Post-Audit Disciplines

- Findings logged in unified CAPA system (not framework-siloed)
- Corrective action owner named; due date agreed
- Cross-framework impact flagged in finding worksheet
- Closure verified by evidence + re-test (not self-attestation)
- Trend analysis monthly: aging CAPAs > 30 days, repeat findings across frameworks
- Inputs prepared for next management review

## When This Reference Doesn't Help

- **Single-framework deep audit detail.** See per-framework playbooks.
- **External certification body audit process.** Different from internal; see ISO 17021.
- **External SOC 2 audit firm engagement.** Different from internal; see `soc2_audit_playbook.md`.
- **Sectoral regulatory enforcement.** Out of scope; engage outside counsel.

---

**Source authorities (non-exhaustive):**

- **ISO/IEC 19011:2018** — Guidelines for auditing management systems
- **IIA International Professional Practices Framework (IPPF)** — Performance Standards 2000-2600
- **AICPA AT-C 105** — Attestation engagement standard (SOC 2)
- **ISO/IEC 27001:2022 Clause 9.2** — Internal audit programme
- **ISO/IEC 42001:2023 Clause 9.2** — Internal audit programme (AI management system)
- **ISO 13485:2016 Clause 8.2.4** — Internal audit (medical devices)
- **Regulation (EU) 2016/679 Article 24** — Accountability (GDPR — operational discipline for audit prep)
- **ISO 17021-1:2015** — Conformity assessment requirements (governs external certification audits; informs internal practice)
- **Annex SL of the ISO/IEC Directives** (2024) — high-level structure enabling integrated management systems
- **NIST SP 800-53A Rev 5** — Assessing Security and Privacy Controls (multi-framework assessment procedures)
- **The Institute of Internal Auditors** — practical guides on integrated audit programme design
