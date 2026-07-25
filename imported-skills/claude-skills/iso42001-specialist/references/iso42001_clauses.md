# ISO/IEC 42001:2023 — Clauses 4-10 Walkthrough

This reference answers exactly one decision: **for each clause of ISO 42001, what audit evidence does the certification body expect, and which existing ISMS/QMS artifact can I reuse?**

Pair with `scripts/aims_gap_analyzer.py` for automated coverage scoring.

## Annex SL High-Level Structure

ISO/IEC 42001:2023 follows the Annex SL structure shared by ISO 9001, 14001, 27001, 13485, 45001, and other management-system standards. This is deliberate: certification bodies, internal auditors, and quality teams can apply existing competencies to AIMS audits with low ramp-up cost.

**Practical implication:** if your organization already operates ISO 27001 + ISO 13485, ~60% of Clauses 4–10 artefacts (scope statements, policies, document control, internal audit programme, management review) can be **extended** to cover AI scope rather than recreated. The gap analysis is mostly Annex A (AI-specific operational controls), not Clauses 4–10.

## Clause 4 — Context of the Organization

| Sub-clause | Requirement | Audit evidence | Common gap |
|---|---|---|---|
| **4.1** | External & internal issues affecting AIMS | Documented context analysis (PESTLE or equivalent); reviewed at management review | Treating AI regulatory landscape as static; missing EU AI Act, US state laws, sector-specific AI rules |
| **4.2** | Needs & expectations of interested parties | Stakeholder matrix: customers, regulators, employees, data subjects, model providers, AI-affected populations | Omitting "AI-affected populations" (people who never interact with the system but are subject to its decisions) |
| **4.3** | AIMS scope statement | Documented scope: which AI systems, which lifecycle phases, which organizational units, which exclusions | Scope omits third-party AI services (SaaS features powered by vendor models); excludes "experimental" systems that are in fact in production |
| **4.4** | AIMS processes & interactions | Process map showing how AIMS processes connect to existing QMS/ISMS processes | Treating AIMS as parallel system instead of integrated extension of existing management systems |

**Reusable from ISO 27001 / 13485:** scope statement template, stakeholder matrix template, process map.

## Clause 5 — Leadership

| Sub-clause | Requirement | Audit evidence | Common gap |
|---|---|---|---|
| **5.1** | Top-management commitment | Documented evidence: AI in board agenda, resource allocation, KPIs | "AI ethics" reduced to marketing copy with no operating commitment |
| **5.2** | AI policy | Signed AI policy committing to lawful use, beneficial purpose, human oversight, continual improvement | Policy doesn't mention human oversight (Annex A.9 requirement); missing commitment to continual improvement |
| **5.3** | Organizational roles, responsibilities, authorities | RACI matrix for AIMS roles; named AIMS owner; AI ethics review board (if applicable) | No named AIMS owner; CISO assumed to "cover AI" without explicit assignment |

**Critical:** Clause 5.2 has a higher evidence bar than ISO 27001/13485 because the AI policy must address fairness, transparency, and human oversight — concepts absent from older management systems. Cannot be satisfied by extending existing policies; needs net-new content.

## Clause 6 — Planning

| Sub-clause | Requirement | Audit evidence | Common gap |
|---|---|---|---|
| **6.1.2** | AI risk assessment | Risk register per ISO 23894 methodology; covers full AI lifecycle | Risk identification at deployment only, missing data + model + decommission phases |
| **6.1.3** | AI risk treatment | Treatment plan linking each risk to Annex A controls; residual-risk acceptance documented | Treatment plan exists but is generic ("apply A.7.3") without specific implementation |
| **6.1.4** | AI system impact assessment | Documented impact assessment per Annex A.5.2 for high-impact systems | Confusing impact assessment (Clause 6.1.4) with risk assessment (Clause 6.1.2) |
| **6.2** | AI objectives | Measurable AI objectives aligned to AI policy; reviewed in management review | Objectives are aspirational ("ethical AI") without measurable targets |

**Run** `ai_risk_register_builder.py` to operationalize 6.1.2 + 6.1.3.

## Clause 7 — Support

| Sub-clause | Requirement | Audit evidence | Common gap |
|---|---|---|---|
| **7.1** | Resources for AIMS | Budget; tooling; compute resources documented | Compute resources for ML training treated as one-off project cost, not ongoing AIMS resource |
| **7.2** | Competence | Defined competence requirements per role (ML eng, AI risk, data steward); training records | Competence requirements undefined for ML engineers; assumes "they have degrees" |
| **7.3** | Awareness | AI awareness training across all employees with AI-system access | Training is engineer-only; product, marketing, customer success bypass |
| **7.4** | Communication | Documented internal + external communications procedure for AI | No procedure for communicating AI incidents to users (Annex A.8.4 link) |
| **7.5** | Documented information | Version-controlled AIMS documentation | Model cards exist but are not under document control; can be edited without approval |

## Clause 8 — Operation

| Sub-clause | Requirement | Audit evidence | Common gap |
|---|---|---|---|
| **8.1** | Operational planning & control | Operational procedures for each AI lifecycle phase | Operations procedures don't define phase transitions (when does "development" become "production"?) |
| **8.2** | Impact assessment process | Operational procedure for triggering impact assessment; gate before launch | Impact assessment treated as one-time launch artifact, not re-triggered on material change |
| **8.3** | AI system lifecycle process | Documented lifecycle covering: design → data → model → V&V → deployment → operation → decommission | Lifecycle skips "decommission"; no procedure for sunsetting AI systems |
| **8.4** | Third-party / customer relationships | Supplier and customer relationship procedures; AI-specific clauses in contracts | Standard vendor contracts not updated for AI-specific obligations (data use, model retraining, drift) |

## Clause 9 — Performance Evaluation

| Sub-clause | Requirement | Audit evidence | Common gap |
|---|---|---|---|
| **9.1** | Monitoring, measurement, analysis & evaluation | Defined metrics for AI performance, fairness, drift; monitoring records | Drift monitoring in code but no defined acceptable drift threshold; no escalation path |
| **9.2** | Internal audit programme | 12-month audit plan; auditor independence documented; findings tracked | No formal AIMS audit programme; audits happen ad hoc; auditors audit own work |
| **9.3** | Management review | Documented management review at planned intervals with required inputs/outputs | Management review inputs missing AI-specific items (drift, incidents, risk-register changes) |

**Run** `aims_audit_scheduler.py` to generate the 9.2 plan with independence checks.

## Clause 10 — Improvement

| Sub-clause | Requirement | Audit evidence | Common gap |
|---|---|---|---|
| **10.1** | Continual improvement | Evidence of AIMS improvement over time (KPIs trending, control maturity rising) | "Continual improvement" treated as audit closure activity, not ongoing |
| **10.2** | Nonconformity & corrective action | CAPA records for AIMS nonconformities; root cause analysis documented | AIMS CAPA loop separate from existing 13485/9001 CAPA loop — duplicated effort, divergent procedures |

**Reusable from ISO 13485 / 9001:** the entire CAPA machinery. Add AI-specific root-cause categories (data quality, model drift, prompt injection, etc.) to the existing taxonomy.

## When This Reference Doesn't Help

- **Specific AI risk identification.** See `aims_controls_annex_a.md` and ISO/IEC 23894:2023.
- **EU AI Act conformity assessment.** Different standard. See `compliance-team-eu-ai-act`.
- **Model cards, datasheets, evaluation methodology.** Tactical artefacts; reference NIST AI RMF playbook + papers like Mitchell et al. (2019).

---

**Source authorities (non-exhaustive):**

- **ISO/IEC 42001:2023** — Information technology — Artificial intelligence — Management system (the standard itself; published 2023-12-18 by ISO/IEC JTC 1/SC 42)
- **ISO/IEC 23894:2023** — AI risk management process (the methodology referenced by Clause 6.1.2)
- **ISO/IEC 38507:2022** — Governance implications of AI for organizations (board-level governance lens referenced by Clause 5)
- **ISO/IEC 22989:2022** — AI concepts and terminology (definitions used throughout)
- **Annex SL** in the ISO/IEC Directives Part 1 (2024) — the high-level structure shared by ISO management-system standards
- **BSI AI Management System (AIMS) Implementation Guide** (BSI, 2024) — practitioner walkthrough
- **AAMI CR34971:2023** — AI guidance for medical devices (cross-walks 42001 to medical device QMS)
- **ISACA** — *Auditing Artificial Intelligence* (2nd ed., 2024) — internal-audit-oriented checklist with ISO 42001 mapping
