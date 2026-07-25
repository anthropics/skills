---
name: "iso42001-specialist"
description: "ISO/IEC 42001:2023 AI Management System (AIMS) specialist for compliance teams running internal audits. Three decisions: (1) Where are the gaps against Clauses 4-10 and what do we close first? (2) What goes in the AI risk register and which Annex A controls treat each risk? (3) What's the 12-month internal audit plan that satisfies Clause 9.2? Use when preparing for certification, scoping internal audit cycles, or onboarding AI systems into an existing ISMS (27001) / QMS (13485) program. NOT an executive AI strategy skill (see chief-ai-officer-advisor). NOT EU AI Act compliance (see compliance-team-eu-ai-act)."
license: MIT
metadata:
  version: 1.0.0
  author: Alireza Rezvani
  category: ra-qm-team
  domain: ai-management-system-compliance
  updated: 2026-05-13
  python-tools: aims_gap_analyzer.py, ai_risk_register_builder.py, aims_audit_scheduler.py
  frameworks: iso-42001, iso-23894, iso-38507, nist-ai-rmf, eu-ai-act-mapping
---

# ISO/IEC 42001 AI Management System Specialist

Internal-audit-grade operating skill for ISO/IEC 42001:2023. **Three decisions, no executive AI strategy:**

1. **Where are the AIMS gaps against Clauses 4–10?** — coverage scoring per clause + remediation priority
2. **What's the AI risk register, and which controls treat each risk?** — Annex A.2–A.10 control mapping per ISO 23894 risk method
3. **What's the Clause 9.2 internal audit plan?** — 12-month schedule with scope, frequency, auditor independence checks

This skill is **NOT a chief-ai-officer-advisor replacement**. CAIO decides whether to build/buy a model and what business risk to accept. This skill operates the management-system discipline that captures those decisions in audit-ready evidence.

This skill is **NOT an EU AI Act compliance skill**. ISO 42001 is a voluntary management-system standard; EU AI Act is binding product-safety regulation. They overlap (a high-risk AI system per Article 6(2) of the AI Act typically requires the QMS in Article 17, which ISO 42001 can satisfy in part) but the artefacts differ. See `compliance-team-eu-ai-act` for Article-level conformity assessment.

This skill is **NOT a substitute for ISO 23894 + 38507**. 42001 is the management system; 23894 is the AI risk methodology that feeds Clause 6.1; 38507 is the governance lens. The `ai_risk_register_builder.py` tool implements the 23894 process; treat the references as the methodology bridge.

## Keywords

ISO 42001, ISO/IEC 42001:2023, AI Management System, AIMS, AI governance, AI risk management, ISO 23894, AI risk assessment, ISO 38507, AI compliance, AI audit, internal audit AI, Annex A controls, AI risk register, AI policy, AI impact assessment, conformity declaration, AI lifecycle, AI risk treatment, NIST AI RMF, NIST AI Risk Management Framework, ISACA AI audit, BSI AIC4, AI assurance, responsible AI, AI ethics governance, AI system inventory, third-party AI risk, AI vendor management, AI change management, AI incident management

## Quick Start

```bash
# Decision A: AIMS gap analysis against Clauses 4-10
python scripts/aims_gap_analyzer.py                           # embedded sample (mid-stage AI SaaS)
python scripts/aims_gap_analyzer.py path/to/aims_evidence.json

# Decision B: AI risk register + Annex A control mapping
python scripts/ai_risk_register_builder.py                    # embedded 7-risk sample
python scripts/ai_risk_register_builder.py path/to/risks.json

# Decision C: Clause 9.2 internal audit 12-month plan
python scripts/aims_audit_scheduler.py                        # embedded 4-domain sample
python scripts/aims_audit_scheduler.py path/to/scope.json
```

## Key Questions (ask these first)

- **Does the AIMS scope statement (Clause 4.3) name every AI system, including embedded models and third-party AI services?** If "AI features added by our SaaS vendors" is not in scope, the AIMS is incomplete.
- **Does the AI policy (Clause 5.2) commit to lawful use AND beneficial purpose AND human oversight AND continual improvement?** Missing any of the four = nonconformity at certification.
- **Has the AI risk assessment (Clause 6.1.2) been re-run since the last material model change?** Concept drift is not a one-time event.
- **Who signs the AI impact assessment for high-impact systems (Annex A.5.4)?** If no signed accountability, the control is missing.
- **What's the internal audit cadence (Clause 9.2)?** ISO management-system standards expect ≥ once per 3-year cycle per clause; mature programs do annual.
- **Is there a documented procedure for AI incidents (Annex A.9.3)?** Untreated post-deployment monitoring is the #1 nonconformity in early adopters.

## Core Responsibilities

### 1. AIMS Gap Analysis (Clauses 4–10)

**The framework:** ISO 42001 follows the Annex SL high-level structure shared with ISO 9001 / 27001 / 13485. Clauses 4–10 are the management-system requirements; Annex A controls A.1–A.10 are the AI-specific operational controls.

| Clause | What it requires | Common gap |
|---|---|---|
| **4. Context** | AI scope, interested parties, external context | Scope omits third-party AI services |
| **5. Leadership** | AI policy, roles, accountability | Policy treats "AI ethics" as marketing copy, not commitment |
| **6. Planning** | AI risk + impact assessment, objectives | Risk register doesn't link to controls |
| **7. Support** | Resources, competence, awareness, documented info | Competence requirements undefined for ML engineers |
| **8. Operation** | Operational planning, AI system lifecycle | Lifecycle stages not mapped to Annex A controls |
| **9. Performance** | Monitoring, internal audit, management review | Drift monitoring exists in code but not in management review inputs |
| **10. Improvement** | Nonconformity, corrective action, continual improvement | CAPA loop separate from existing 13485/9001 CAPA — duplication |

**Run** `aims_gap_analyzer.py` with an evidence inventory JSON to score each clause (full / partial / missing) and get a prioritized remediation list.

See `references/iso42001_clauses.md` for the full clause-by-clause walkthrough with audit evidence expectations.

### 2. AI Risk Register + Annex A Control Mapping

**The framework:** Clause 6.1.2 requires AI risk assessment; Clause 6.1.3 requires risk treatment. Annex A provides 38 controls organized into 10 control categories (A.2–A.10). The risk register must show each identified risk linked to ≥ 1 control that treats it.

**Annex A control categories (the 10):**

| ID | Category | Example controls |
|---|---|---|
| **A.2** | AI policy | A.2.2 AI policy, A.2.3 alignment with other policies |
| **A.3** | Internal organization | A.3.2 AI roles & responsibilities, A.3.3 reporting concerns |
| **A.4** | Resources for AI systems | A.4.2 data resources, A.4.3 tooling, A.4.4 human resources |
| **A.5** | Assessing impacts | A.5.2 AI system impact assessment, A.5.4 documentation of impact assessment |
| **A.6** | AI system lifecycle | A.6.2.2 objectives, A.6.2.3 lifecycle phases, A.6.2.4 verification & validation |
| **A.7** | Data for AI systems | A.7.2 data management, A.7.3 data quality, A.7.4 data provenance, A.7.5 data preparation |
| **A.8** | Information for interested parties | A.8.2 system documentation, A.8.3 user information, A.8.4 communication of incidents |
| **A.9** | Use of AI systems | A.9.2 intended use, A.9.3 monitoring of operation, A.9.4 logging of system events |
| **A.10** | Third-party & customer relationships | A.10.2 supplier relationships, A.10.3 customer relationships |

ISO/IEC 23894:2023 provides the AI-specific risk-management process (the methodology); 42001 Annex A provides the controls. The risk register is the bridge.

**Run** `ai_risk_register_builder.py` with an identified-risks JSON to produce a structured register with mapped controls + residual-risk verdict per ISO 23894 risk-treatment options.

See `references/aims_controls_annex_a.md` for the full 38-control catalogue with audit evidence per control.

### 3. Clause 9.2 Internal Audit Plan

**The framework:** Clause 9.2 requires "internal audits at planned intervals to provide information on whether the AIMS conforms to the organization's requirements and is effectively implemented and maintained." That's the management-system requirement; the **how often** and **how deep** are organizational choices.

**Mature-program defaults:**

- Cover every clause + every applicable Annex A control over a 3-year cycle (rolling)
- Annual full-system audit covering Clauses 4, 5, 9, 10 (the "always relevant" clauses)
- Quarterly or semi-annual deep dives on Clauses 6, 7, 8 by domain (per AI system or per lifecycle phase)
- Auditor independence: nobody audits their own work; A.6 lifecycle owner cannot audit Clause 8 operation

**Run** `aims_audit_scheduler.py` with a scope JSON (AI systems in scope, prior-year findings, certification cycle phase) to produce a 12-month plan with auditor assignments and independence checks.

See `references/aims_implementation_guide.md` for the maturity model and rollout sequencing (year 1 establish, year 2 certify, year 3+ continual improvement).

## Workflows

### Workflow 1: AIMS Gap Closure for Certification (4–8 weeks)
**Goal:** Identify gaps; prioritize remediation; close before stage 1 certification audit.

```bash
# 1. Inventory current AIMS evidence (policies, procedures, records)
python scripts/aims_gap_analyzer.py aims_evidence.json
# 2. Review gap matrix; group by clause
# 3. For each gap, identify owner + due date (target: close before stage 1)
# 4. Cross-check against ISO 27001 / 13485 existing artifacts — many can be reused
# 5. Cross-check against EU AI Act obligations (use compliance-team-eu-ai-act)
# 6. Output: prioritized remediation plan with owners + dates
```

### Workflow 2: AI Risk Register Build (1–2 weeks)
**Goal:** Construct the Clause 6.1.2 risk register with full Annex A control coverage.

```bash
# 1. Run ISO 23894 risk identification across AI lifecycle (data, model, deployment, decommission)
# 2. Capture each risk with: source, event, consequence, likelihood, impact
python scripts/ai_risk_register_builder.py risks.json
# 3. For each high/critical risk, confirm ≥ 1 Annex A control is selected as treatment
# 4. Document residual risk acceptance with management signoff
# 5. Cross-check with cs-caio-advisor on executive risk acceptance for "tolerate" decisions
# 6. Log via management review (Clause 9.3)
```

### Workflow 3: Annual Internal Audit Plan (1 day)
**Goal:** Produce the 12-month Clause 9.2 plan with auditor independence.

```bash
# 1. Pull last year's audit findings and certification cycle status (year 1/2/3)
python scripts/aims_audit_scheduler.py audit_scope.json
# 2. Confirm auditor independence per assignment
# 3. Confirm coverage hits every clause and every applicable Annex A control over rolling 3 years
# 4. Submit plan for management review approval (Clause 9.3 input)
```

### Workflow 4: Cross-Framework Reuse Mapping (per system onboarded)
**Goal:** When adding a new AI system, map ISO 42001 evidence against existing 27001 + 13485 evidence to avoid duplication.

1. Pull existing ISO 27001 Annex A controls + ISO 13485 procedures relevant to the system
2. For each ISO 42001 Annex A control, identify whether an existing artifact already satisfies it (e.g., 27001 A.8.16 monitoring activities can extend to AI system monitoring)
3. Add the AI-specific overlay only where the existing control doesn't cover it
4. Document mapping in the AIMS scope statement (Clause 4.3)

## Output Standards

```
**Bottom Line:** [one sentence — gap severity + the one thing to close first]
**The Decision:** [one of: gap-closure | risk-treatment | audit-scope]
**The Evidence:** [clause numbers + control IDs from the tool, not adjectives]
**How to Act:** [3 concrete next steps with owners + dates]
**Your Decision:** [the call only the compliance officer or CAIO can make — risk acceptance, scope expansion, certification readiness]
```

## Adjacent Skills

- `ra-qm-team/skills/information-security-manager-iso27001/` — ISO 27001 ISMS implementation (many controls reusable for AIMS A.7 data controls)
- `ra-qm-team/skills/quality-manager-qms-iso13485/` — ISO 13485 QMS (provides CAPA + management-review machinery the AIMS reuses)
- `ra-qm-team/skills/gdpr-dsgvo-expert/` — GDPR DPIA process (input to AIMS A.5 impact assessment for personal-data systems)
- `ra-qm-team/skills/isms-audit-expert/` — ISO 27001 internal audit pattern (the audit scheduler mirrors this for AIMS)
- `ra-qm-team/skills/soc2-compliance/` — SOC 2 trust services (reusable controls for AIMS A.10 third-party relationships)
- `ra-qm-team/compliance-team-eu-ai-act/` — EU AI Act Article-level compliance (binding regulation companion to voluntary 42001)
- `compliance-os/` — Meta-orchestrator for multi-framework programs (run AIMS as one framework among 9)
- `c-level-advisor/chief-ai-officer-advisor/` — Executive AI strategy (build-vs-buy, cost economics — different audience)

## References

- [iso42001_clauses.md](references/iso42001_clauses.md) — Clauses 4–10 walkthrough with audit evidence expectations, common gaps, and reusable artifacts from ISO 27001/13485
- [aims_controls_annex_a.md](references/aims_controls_annex_a.md) — All 38 Annex A controls (A.2–A.10) with implementation guidance, audit evidence, and severity of failure
- [aims_implementation_guide.md](references/aims_implementation_guide.md) — 3-year maturity model (establish → certify → continually improve), rollout sequencing, integration with existing ISMS/QMS programs
- [cross_framework_mapping_ai.md](references/cross_framework_mapping_ai.md) — ISO 42001 ↔ EU AI Act ↔ NIST AI RMF ↔ ISO 23894 ↔ ISO 38507 ↔ ISO 27001 control-level mapping with mapping-confidence ratings

---

**Version:** 1.0.0
**Status:** Production Ready
