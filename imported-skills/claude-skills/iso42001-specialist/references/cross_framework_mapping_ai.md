# ISO/IEC 42001 ↔ EU AI Act ↔ NIST AI RMF ↔ ISO 23894 ↔ ISO 38507 ↔ ISO 27001 — Cross-Framework Mapping

This reference answers exactly one decision: **for each ISO 42001 obligation, which other frameworks already cover it, and what evidence can I reuse?**

The point of cross-framework mapping is to avoid duplicate work. A control implemented for ISO 27001 frequently satisfies an Annex A control of ISO 42001 with minor AI-specific overlay. The `compliance-os` orchestrator's `cross_framework_mapper.py` consumes this mapping.

## High-Level Framework Comparison

| Framework | Type | Binding? | AI scope | Maturity |
|---|---|---|---|---|
| **ISO/IEC 42001:2023** | Management system standard | Voluntary; certifiable | AI Management System (AIMS) | Published 2023; certifications starting 2024 |
| **EU AI Act (Reg. 2024/1689)** | Product safety regulation | Binding in EU | Risk-based: prohibited → high-risk → limited-risk → minimal-risk | In force Aug 2024; phased obligations through 2027 |
| **NIST AI RMF 1.0** | Risk management framework | Voluntary (US) | Govern / Map / Measure / Manage functions | Released Jan 2023; mature playbook |
| **ISO/IEC 23894:2023** | Risk management methodology | Reference standard | AI risk process; informs 42001 Clause 6.1 | Published 2023 |
| **ISO/IEC 38507:2022** | Governance standard | Reference standard | Board-level AI governance | Published 2022 |
| **ISO/IEC 27001:2022** | Management system standard | Voluntary; certifiable | Information security | Mature; widely certified |

## Clause-to-Framework Mapping (ISO 42001 lens)

### Clause 4 — Context

| ISO 42001 | EU AI Act | NIST AI RMF | ISO 27001 | Notes |
|---|---|---|---|---|
| 4.1 External context | Art. 1 (scope); Recitals on risk-based approach | GOVERN 1.1 | 4.1 | Extend 27001 context with AI regulatory landscape |
| 4.2 Interested parties | Art. 27 (FRIA stakeholders for high-risk) | GOVERN 5 | 4.2 | Add AI-affected populations |
| 4.3 Scope | Article 6 + Annex III define what's in scope as "high-risk" | MAP 1.1 | 4.3 | Distinct artifacts; AIMS scope ≠ EU AI Act applicability scope |
| 4.4 AIMS processes | n/a | n/a | 4.4 | Integration map |

### Clause 5 — Leadership

| ISO 42001 | EU AI Act | NIST AI RMF | ISO 27001 / ISO 38507 |
|---|---|---|---|
| 5.1 Top-mgmt commitment | Art. 26 (deployer obligations); Art. 16 (provider obligations) | GOVERN 1 | 27001 5.1; 38507 Clauses 5–6 (governance principles) |
| 5.2 AI policy | Art. 17 (QMS for high-risk); Art. 95 (codes of conduct) | GOVERN 1.1 | 27001 5.2 — extend with AI commitments |
| 5.3 Roles & authorities | Art. 26 (deployer obligations); Art. 16 + 22 (authorized representative) | GOVERN 2.1 | 27001 5.3 |

### Clause 6 — Planning (the densest mapping)

| ISO 42001 | EU AI Act | NIST AI RMF | ISO 23894 |
|---|---|---|---|
| 6.1.2 AI risk assessment | Art. 9 (risk management system for high-risk) | MAP 5.1; MAP 5.2 | Clauses 6–7 (entire process) |
| 6.1.3 AI risk treatment | Art. 9(2)(c–d) (risk management measures) | MANAGE 1.1 | Clauses 8 (treatment selection) |
| 6.1.4 Impact assessment | Art. 27 (Fundamental Rights Impact Assessment for high-risk public-sector deployers) | MAP 2.3; MAP 5.1 | Clause 5.3 (scope definition) |
| 6.2 AI objectives | Art. 9(2)(a) (objectives of risk management) | GOVERN 1.5; MEASURE 1 | Clause 5.2 |

### Clause 7 — Support

| ISO 42001 | EU AI Act | NIST AI RMF | ISO 27001 |
|---|---|---|---|
| 7.1 Resources | Art. 17(1)(c) (technical resources for QMS) | GOVERN 3 | A.6.1 |
| 7.2 Competence | Art. 14 (human oversight competence); Art. 26(2) (deployer competence) | GOVERN 3.1 | A.6.3 |
| 7.3 Awareness | Art. 14 | GOVERN 5.1 | A.6.3 |
| 7.4 Communication | Art. 50 (transparency obligations); Art. 86 (right to explanation) | GOVERN 5.2 | A.7.4 |
| 7.5 Documented info | Art. 11 + 12 (technical documentation); Art. 19 (record-keeping) | GOVERN 1.4 | 27001 7.5 |

### Clause 8 — Operation

| ISO 42001 | EU AI Act | NIST AI RMF | Notes |
|---|---|---|---|
| 8.1 Operational planning | Art. 17 (QMS) | MANAGE 2 | |
| 8.2 Impact assessment process | Art. 27 (FRIA process) | MAP 2 | |
| 8.3 AI system lifecycle | Art. 9 (full lifecycle); Art. 72 (post-market monitoring) | MAP 3; MEASURE 3; MANAGE 4 | Densest overlap |
| 8.4 Third-party / customer | Art. 25 (responsibilities along the AI value chain) | GOVERN 6 | |

### Clause 9 — Performance

| ISO 42001 | EU AI Act | NIST AI RMF | ISO 27001 |
|---|---|---|---|
| 9.1 Monitoring | Art. 72 (post-market monitoring system) | MEASURE 2; MEASURE 4 | 9.1 |
| 9.2 Internal audit | Art. 17(1)(j) (internal audit as part of QMS) | GOVERN 4 | 9.2 |
| 9.3 Management review | n/a explicit; implied in Art. 17 | GOVERN 1 | 9.3 |

### Clause 10 — Improvement

| ISO 42001 | EU AI Act | NIST AI RMF | ISO 27001 |
|---|---|---|---|
| 10.1 Continual improvement | Art. 9(2)(c) (iterative risk reduction) | MANAGE 4.3 | 10.1 |
| 10.2 Nonconformity & CAPA | Art. 73 (incident reporting); Art. 79 (corrective actions) | MANAGE 4.2 | 10.2 |

## Annex A Control → Framework Mapping (subset of highest-value mappings)

| ISO 42001 Annex A | EU AI Act | NIST AI RMF | ISO 27001 | Mapping confidence |
|---|---|---|---|---|
| A.2.2 AI policy | Art. 95 (codes of conduct) | GOVERN 1.1 | A.5.1 (info-sec policy) | HIGH |
| A.5.2 Impact assessment | Art. 27 FRIA | MAP 2.3 | n/a | MEDIUM (FRIA narrower) |
| A.6.2.4 V&V | Art. 15 (accuracy, robustness, cybersecurity); Art. 17(1)(h) | MEASURE 2 | n/a | HIGH |
| A.7.2 Data management | Art. 10 (data governance) | MAP 2.3; MEASURE 2.6 | A.5.10 | HIGH |
| A.7.3 Data quality | Art. 10(3) (relevance, representativeness, error-free, complete) | MEASURE 2.6 | n/a | HIGH |
| A.7.4 Data provenance | Art. 10(2)(d) (data origin) | MAP 2.3 | n/a | HIGH |
| A.7.6 Data privacy | Art. 10(5) (special categories); GDPR Articles 5, 6, 9 | MANAGE 2.1 | A.5.34 | HIGH |
| A.8.2 System docs | Art. 11 + Annex IV (technical documentation) | GOVERN 1.4 | A.5.37 | HIGH |
| A.8.3 User information | Art. 13 (instructions for use); Art. 50 (transparency) | GOVERN 5.2 | n/a | HIGH |
| A.8.4 Incident communication | Art. 73 (incident reporting to authorities) | MANAGE 4.2 | A.6.8 (reporting) | HIGH |
| A.9.3 Monitoring | Art. 72 (post-market monitoring) | MEASURE 2; MEASURE 4 | A.8.15 (logging) | HIGH |
| A.9.4 Logging | Art. 12 (record-keeping); Art. 19 | MEASURE 4 | A.8.15 | HIGH |
| A.10.2 Supplier relationships | Art. 25 (responsibilities along the AI value chain) | GOVERN 6 | A.5.19, A.5.20, A.5.21 | HIGH |

**Mapping confidence legend:**
- **HIGH** — direct overlap; same evidence can satisfy both
- **MEDIUM** — partial overlap; existing evidence with AI overlay
- **LOW** — concept overlap; mostly new artifact required

## Practical Reuse Pattern

If you operate ISO 27001 (mature) + are adopting ISO 42001:

1. **Reuse policies (~60%):** Extend info-sec policy with AI commitments (5.2 + A.2.2)
2. **Reuse procedures (~50%):** Document control, internal audit, management review, CAPA
3. **Reuse risk machinery (~70%):** Same severity matrix, same treatment workflow, same residual-risk acceptance flow — just add AI-specific risks and Annex A control mapping
4. **Reuse supplier mgmt (~80%):** Add AI-specific contract clauses to existing supplier procedure
5. **New artifacts (~40%):** Model cards / datasheets (A.6.2.7, A.7.4), impact assessments per Annex A.5, lifecycle procedure (A.6), drift monitoring (A.9.3), V&V procedure (A.6.2.4)

If you also operate ISO 13485 (medical device QMS):

- Reuse: design controls (7.3) for A.6 lifecycle; risk management (ISO 14971) overlays cleanly onto A.5 + 6.1; post-market surveillance maps directly to A.9.3 monitoring
- Add: AI-specific failure modes to ISO 14971 hazard analysis

## When This Reference Doesn't Help

- **EU AI Act conformity assessment routing.** See `compliance-team-eu-ai-act/scripts/conformity_assessment_planner.py`.
- **NIST AI RMF deep-dive.** See NIST AI RMF Playbook (NIST.AI.100-1.pdf) and Generative AI Profile (NIST.AI.600-1).
- **Multi-framework audit simulation.** See `compliance-os/scripts/audit_simulator.py`.

---

**Source authorities (non-exhaustive):**

- **ISO/IEC 42001:2023** — Annex A normative controls
- **Regulation (EU) 2024/1689** — Artificial Intelligence Act — full Articles (the binding regulation)
- **NIST AI Risk Management Framework 1.0** (Jan 2023, NIST AI 100-1) + AI RMF Playbook
- **ISO/IEC 23894:2023** — AI risk management process
- **ISO/IEC 38507:2022** — Governance implications of AI
- **ISO/IEC 27001:2022** + Annex A controls (the most cross-walked partner standard)
- **EDPB Opinion 28/2024** — Guidelines on processing of personal data in AI models
- **European Commission AI Act Guidelines** (continuously updated): Guidelines on prohibited practices (Feb 2025), Guidelines on definition of AI system (Feb 2025), FRIA template guidance
- **BSI** — *Cross-walking ISO 42001 and EU AI Act* (white paper, 2024)
- **IAPP EU AI Act Tracker** (continuously updated) — practitioner reference for Article applicability
