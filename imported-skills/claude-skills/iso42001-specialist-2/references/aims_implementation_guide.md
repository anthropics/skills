# ISO/IEC 42001 — AIMS Implementation Guide (3-Year Maturity Model)

This reference answers exactly one decision: **what's the rollout sequence — what do we build in year 1 vs year 2 vs year 3, and how do we avoid recreating ISO 27001/13485 machinery?**

Pair with `scripts/aims_audit_scheduler.py` to operationalize the year-by-year audit cycle.

## The 3-Year Cycle

ISO management-system certifications follow a 3-year cycle:

| Year | Audit type | What happens |
|---|---|---|
| **Year 1** | Stage 1 (documentation review) + Stage 2 (implementation audit) → initial certification | Establish the AIMS; close major nonconformities; pass certification |
| **Year 2** | Surveillance audit (selective scope) | Demonstrate continual improvement; close minor nonconformities from year 1 |
| **Year 3** | Surveillance audit (selective scope) + recertification preparation | Full system review; prepare for year 4 recertification |
| **Year 4** | Recertification audit (full scope) | Renew certificate |

The internal audit programme (Clause 9.2) must cover every clause + every applicable Annex A control at least once per 3-year cycle. The plan must show this rolling coverage.

## Year 1 — Establish (focus: artifacts that auditors must see)

**Goal:** every clause and every applicable Annex A control has at least a documented procedure and one round of records.

### Q1: Foundations

- AI policy (Clause 5.2 + A.2.2) — board-signed
- AIMS scope statement (Clause 4.3) — names every AI system including third-party
- Roles & responsibilities (Clause 5.3 + A.3.2) — RACI with named AIMS owner
- Stakeholder & context analysis (Clause 4.1–4.2)

### Q2: Risk & impact

- AI risk register (Clause 6.1.2 + A.5) — run `ai_risk_register_builder.py`
- Risk treatment plan (Clause 6.1.3) — every high/critical risk linked to ≥ 1 Annex A control
- Impact assessment procedure (Clause 6.1.4 + A.5.3)
- AI objectives (Clause 6.2) — measurable targets

### Q3: Operations

- AI system lifecycle procedure (Clause 8.3 + A.6) — design through decommission
- Data management procedures (A.7) — data quality, provenance, preparation
- Monitoring plan per system (A.9.3)
- Third-party AI contract template (A.10.2)

### Q4: Performance

- Internal audit programme (Clause 9.2) — run `aims_audit_scheduler.py`
- Management review procedure (Clause 9.3) — inputs include AI-specific items
- CAPA integration with existing 13485/9001 CAPA loop (Clause 10.2)
- Stage 1 audit readiness check — run `aims_gap_analyzer.py`

**Year 1 success criteria:** stage 1 audit passes with 0 critical and ≤ 1 major nonconformity.

## Year 2 — Certify and operate

**Goal:** close year-1 minor nonconformities; demonstrate the system is operating, not just documented.

### Focus shifts to records (evidence the procedures are followed)

- Monthly drift monitoring records (A.9.3)
- Quarterly impact assessment reviews (A.5)
- Half-yearly third-party AI supplier reviews (A.10.2)
- Annual management review (Clause 9.3) with documented AI-specific inputs:
  - Risk register changes
  - Open nonconformities
  - Drift events outside threshold
  - Incidents per A.8.4
  - Performance trends vs objectives (Clause 6.2)

**Year 2 success criteria:** surveillance audit passes; year-1 nonconformities closed; ≥ 80% of risk-register treatments fully implemented.

## Year 3 — Continually improve

**Goal:** demonstrate continual improvement (Clause 10.1) and prepare for recertification.

- Annual update to risk register based on new AI systems, regulation changes, incidents
- Re-baseline objectives (Clause 6.2) against year-1 + year-2 performance
- Audit the audit programme itself (meta-audit; common surveillance finding)
- Demonstrate at least one improvement initiative closed with measurable result

**Year 3 success criteria:** surveillance audit passes; recertification scope confirmed; trend evidence supports continual improvement claim.

## Integration With Existing ISMS (ISO 27001) and QMS (ISO 13485 / 9001)

The mistake most organizations make: building the AIMS as a parallel management system. **Don't.** ISO 42001 is intentionally Annex SL aligned to allow integration. Common integration patterns:

| Existing artifact | Extend for AIMS by adding |
|---|---|
| ISMS scope statement | List of AI systems within ISMS scope |
| Information security policy | AI-specific commitments (fairness, human oversight) |
| Risk register (27001) | AI risks tagged distinctly; same severity matrix; same treatment workflow |
| Document control procedure | Add model cards + datasheets + impact assessments to controlled documents |
| Internal audit programme | Add AI clause + Annex A controls to rotation |
| Management review | Add AI inputs (drift, incidents, risk-register changes) |
| CAPA procedure | Add AI-specific root-cause categories (data quality, model drift, prompt injection) |
| Supplier management | Add AI-specific contract clauses |
| Incident response | Add AI incidents (bias surfaced, drift exceeded, model misuse) |

**Reuse rule of thumb:** if you already operate ISO 27001 + ISO 13485 maturely, ~60% of AIMS Clauses 4–10 effort is rewriting existing artifacts to include AI scope. The remaining ~40% is Annex A operational controls (risk register details, lifecycle, V&V, monitoring, model cards) which are genuinely new.

## Sequence If Starting From Zero (No Prior Management System)

If your organization is starting AIMS without prior ISO certification:

1. **Add ISO 27001 first.** Most AIMS Clauses 4–10 evidence is satisfied by ISO 27001 evidence with AI scope appended. Doing 42001 alone is harder.
2. **Or start with NIST AI RMF.** NIST AI RMF is voluntary and US-centric but maps cleanly to 42001 Annex A. Mature on RMF for 12–18 months, then layer the management-system formality of 42001 on top.
3. **Avoid: building AIMS in isolation.** You'll recreate document control, CAPA, management review, and internal audit infrastructure that ISO 27001/13485 already standardize.

## Cost & Effort Benchmarks (informal, practitioner-reported)

| Org type | Year 1 effort (FTE-months) | Notes |
|---|---|---|
| Mature 27001 + 13485 org adding AIMS | 4–6 | Mostly Annex A overlay |
| Mature 27001 org adding AIMS (no 13485) | 8–12 | Add lifecycle procedures (A.6) net-new |
| Greenfield (no prior management system) | 24–36 | Do 27001 first, then 42001 |

Certification body fees: ~$15k–$35k for initial certification audit (stage 1 + stage 2 for a typical mid-size SaaS); ~$8k–$15k per surveillance year.

## Common Year-1 Pitfalls

1. **Treating "AI ethics" as the policy.** A poetic policy doesn't pass; auditor wants concrete commitments and a way to verify them.
2. **Risk register with no control mapping.** Register identifies risks but doesn't show which Annex A control treats each — Clause 6.1.3 fails.
3. **Lifecycle procedure that skips decommission.** Auditor will ask, "How do you safely retire an AI system?" If silence, A.6 fails.
4. **No drift threshold defined.** Monitoring "we watch it" doesn't pass; needs metric + threshold + escalation owner.
5. **Third-party AI excluded.** "Our vendors' AI features aren't ours" is wrong if you embed them in your service.
6. **No competence requirement for ML engineers.** Clause 7.2 wants documented competence requirements per role; "they have PhDs" isn't a documented requirement.

## When This Reference Doesn't Help

- **Specific Annex A control implementation.** See `aims_controls_annex_a.md`.
- **Risk identification methodology.** See ISO/IEC 23894:2023.
- **EU AI Act overlap.** See `cross_framework_mapping_ai.md` and `compliance-team-eu-ai-act/`.

---

**Source authorities (non-exhaustive):**

- **ISO/IEC 42001:2023** — the standard itself
- **ISO/IEC 23894:2023** — AI risk management process
- **ISO/IEC 38507:2022** — Governance implications of AI for organizations
- **ISO/IEC 27001:2022** — Information security management (reuse template for 60% of AIMS Clauses 4–10)
- **ISO/IEC 13485:2016** — Medical device QMS (reuse template for CAPA, document control)
- **NIST AI RMF 1.0** (Jan 2023) + AI RMF Playbook + Generative AI Profile (NIST AI 600-1, 2024)
- **BSI** — *Information technology — Artificial intelligence — Implementation guidance for ISO/IEC 42001* (2024 white paper)
- **ISACA** — *Auditing Artificial Intelligence* (2nd ed., 2024) — implementation pitfalls catalogue
- **IAPP** — AI Governance Center materials (continuously updated) — practitioner community knowledge base
