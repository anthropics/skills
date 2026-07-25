---
name: "eu-ai-act-specialist"
description: "EU AI Act (Regulation (EU) 2024/1689) operational compliance for compliance teams. Three Article-level decisions: (1) What's the risk tier of this AI system — prohibited (Art. 5), high-risk (Art. 6 + Annex III), limited-risk (Art. 50), or minimal-risk? (2) For high-risk systems, what's the Article 43 conformity assessment route (Module A internal control vs Module H full QMS + notified body) and what goes in the Annex IV technical documentation? (3) Per organizational role (provider / deployer / importer / distributor / authorized representative), what are the active obligations and deadlines? Use during AI system intake review, when planning conformity assessment, or when scoping deployer obligations. Cites Articles + Annexes for every output. NOT executive AI strategy (see chief-ai-officer-advisor). NOT a legal substitute."
license: MIT
metadata:
  version: 1.0.0
  author: Alireza Rezvani
  category: ra-qm-team
  domain: eu-ai-act-compliance
  updated: 2026-05-13
  python-tools: ai_system_risk_classifier.py, conformity_assessment_planner.py, ai_act_obligation_tracker.py
  frameworks: eu-ai-act, gdpr-overlap, iso-42001-mapping, nist-ai-rmf-mapping
---

# EU AI Act Compliance Specialist

Article-cited operational skill for Regulation (EU) 2024/1689. **Three decisions, no executive AI strategy:**

1. **What tier is this AI system?** — prohibited (Article 5) / high-risk (Article 6 + Annex III) / limited-risk transparency (Article 50) / minimal-risk
2. **For high-risk systems, what's the conformity assessment route + documentation pack?** — Article 43 Module A vs Module H + Annex IV technical documentation
3. **Per organizational role, what are the obligations?** — provider / deployer / importer / distributor / authorized representative matrix per Article 16, 22, 25, 26

This skill is **NOT chief-ai-officer-advisor**. CAIO decides whether to ship the AI feature at all and accepts business risk. This skill operates the conformity work that turns "we'll ship it" into Article-compliant artefacts.

This skill is **NOT a legal substitute**. The Act is binding regulation. For novel cases (Is this a GPAI model? Does Article 6(2) carve-out apply? Is fine-tuning a foundation model "substantial modification"?), engage qualified outside counsel. The skill cites Articles + Annexes and uses Commission/EDPB published interpretation but does not provide binding legal opinion.

This skill is **NOT GDPR**. Many AI systems also trigger GDPR (training data, output processing). See `ra-qm-team/skills/gdpr-dsgvo-expert/` for DPIA + lawful basis work. The Acts interact (Recital 10, Article 10 for high-risk training data).

## Keywords

EU AI Act, EU AI Regulation, Regulation 2024/1689, AI Act, AI regulation Europe, high-risk AI, prohibited AI, Article 5 AI Act, Article 6 AI Act, Article 9 AI Act, Article 50 AI Act, Annex III, Annex IV, conformity assessment, CE marking AI, notified body AI, Module A, Module H, technical documentation AI, post-market monitoring AI, fundamental rights impact assessment, FRIA, GPAI, general-purpose AI model, systemic risk GPAI, AI Office, ENISA AI, EDPB AI, AI Act timeline, AI Act penalties, EU AI Act provider, EU AI Act deployer, EU AI Act importer, EU AI Act distributor, EU AI Act fines, AI literacy

## Quick Start

```bash
# Decision A: Classify an AI system per the Act
python scripts/ai_system_risk_classifier.py                       # embedded 5-system sample
python scripts/ai_system_risk_classifier.py path/to/systems.json

# Decision B: Conformity assessment plan for a high-risk system
python scripts/conformity_assessment_planner.py                   # embedded high-risk sample
python scripts/conformity_assessment_planner.py path/to/system.json

# Decision C: Obligation tracker per organizational role
python scripts/ai_act_obligation_tracker.py                       # embedded sample (provider + deployer)
python scripts/ai_act_obligation_tracker.py path/to/roles.json
```

## Key Questions (ask these first)

- **Does this AI system fall under Article 5 (prohibited practices)?** Social scoring, emotion recognition in workplace/education, manipulative subliminal techniques, real-time remote biometric identification in public — any of these are flat-out prohibited.
- **Does it fall under Annex III (high-risk categories)?** 8 categories: biometrics, critical infrastructure, education, employment, essential services, law enforcement, migration, justice. Triggering Annex III triggers Article 6(2) — unless the Article 6(3) carve-outs apply.
- **What organizational role does the company play?** Provider (placed on market), deployer (uses under own authority), importer (places third-country system on EU market), distributor (makes available in supply chain). Many companies are BOTH provider AND deployer simultaneously.
- **Is this a general-purpose AI model?** GPAI has its own track (Articles 51–55) with stricter rules above 10²⁵ FLOPs training compute (Article 51 systemic risk).
- **For high-risk: have we run Article 9 risk management AND Article 27 FRIA?** Article 9 is the lifecycle risk management; Article 27 is the Fundamental Rights Impact Assessment for public-sector deployers + essential services.
- **What's the conformity assessment Module per Article 43?** Module A (internal control, possible for most Annex III systems) vs Module H (full QMS + notified body, required for biometrics + sometimes others).

## Core Responsibilities

### 1. AI System Risk Classification

**The framework:** The Act takes a risk-based approach (Recital 26). Each AI system falls into exactly one of four tiers:

| Tier | Source | Examples | Obligations |
|---|---|---|---|
| **Prohibited** | Article 5 | Social scoring; emotion recognition in workplace/education; subliminal manipulation; real-time public biometrics by law enforcement (with narrow exceptions) | Cannot be placed on market or used (penalties up to EUR 35M / 7% turnover) |
| **High-risk** | Article 6 + Annex III; Article 6(1) + Annex I | CV-screening, credit scoring, biometric categorisation, safety components of regulated products | Articles 8–17 (provider) + Article 26 (deployer); conformity assessment; CE marking |
| **Limited-risk (transparency)** | Article 50 | Chatbots, deepfakes, emotion recognition outside Article 5 contexts | Transparency disclosures to natural persons |
| **Minimal-risk** | Default | Spam filters, video-game AI, inventory forecasters | None under the Act (voluntary codes of conduct, Article 95) |

**Critical carve-outs (Article 6(3)):** an Annex III system is NOT high-risk if it (a) performs a narrow procedural task, (b) improves the result of previously completed human activity, (c) detects decision-making patterns without replacing human assessment, (d) performs a preparatory task. Caveat: profiling of natural persons is always Annex III high-risk regardless of carve-outs.

**Run** `ai_system_risk_classifier.py` with system characteristics. The tool checks Article 5 prohibitions first, then Annex III categories, then Article 6(3) carve-outs, then Article 50 transparency, then minimal-risk default.

See `references/eu_ai_act_titles.md` for the full Article-by-Article walkthrough.

### 2. Conformity Assessment + Annex IV Technical Documentation

**The framework (Article 43 + Annex VI/VII):** for high-risk AI systems, the provider must demonstrate conformity before placing on market. Two routes:

- **Module A — Internal control** (Annex VI): provider self-assesses against the requirements. Applies to most Annex III systems where the provider has implemented harmonised standards.
- **Module H — Full quality management system + technical documentation** (Annex VII): notified body involvement. Required for biometrics systems (Article 43(1)).

**Required artifacts per Annex IV — Technical Documentation:**

1. General description of the AI system (intended purpose, identification, version)
2. Detailed description of system elements (architecture, training data, validation procedures)
3. Information about monitoring, functioning and control
4. Description of risk management system (Article 9)
5. Description of changes after placing on market
6. List of harmonised standards applied (or alternative)
7. EU declaration of conformity (Article 47)
8. Description of the post-market monitoring system (Article 72)

**Run** `conformity_assessment_planner.py` to select the Module and produce the Annex IV checklist for a given high-risk system.

See `references/high_risk_systems_annex_iii.md` for which systems require which conformity route.

### 3. Per-Role Obligation Tracker

**The framework (Articles 16, 22, 23, 24, 25, 26):** the Act distinguishes provider obligations (most) from downstream-actor obligations (deployer, importer, distributor, authorized representative). A single company can play multiple roles simultaneously.

| Role | Primary Articles | Key obligations |
|---|---|---|
| **Provider** (Article 3(3)) | 8–17, 47, 49, 72 | Conformity assessment; CE marking; risk management; data governance; technical documentation; post-market monitoring; serious incident reporting (Article 73) |
| **Deployer** (Article 3(4)) | 26 | Use according to instructions; human oversight; input data quality; record-keeping (Article 19); inform workers (Article 26(7)); FRIA if public-sector/essential-services (Article 27) |
| **Importer** (Article 3(6)) | 23 | Verify conformity; affixed CE marking; technical documentation availability |
| **Distributor** (Article 3(7)) | 24 | Verify CE marking + documentation before making available |
| **Authorized representative** (Article 22) | 22 | Non-EU providers must appoint one; representative liable for provider obligations |

**Important:** under Article 25, a deployer who substantially modifies a high-risk AI system, or places it on the market under their own name, becomes a **provider** and inherits provider obligations.

**Run** `ai_act_obligation_tracker.py` with the roles JSON to produce a deadline-sorted obligation matrix.

See `references/gpai_obligations.md` for the separate GPAI Articles 51–55 track.

## Workflows

### Workflow 1: AI System Intake Review (per system, ~2 hours)
**Goal:** classify, identify obligations, scope the conformity work.

```bash
# 1. Document system characteristics: purpose, users, data, autonomy, deployment context
# 2. Run classifier
python scripts/ai_system_risk_classifier.py systems.json
# 3. If high-risk: run planner
python scripts/conformity_assessment_planner.py system.json
# 4. Identify org roles played (provider / deployer / both)
python scripts/ai_act_obligation_tracker.py roles.json
# 5. Cross-check with GDPR DPIA (gdpr-dsgvo-expert) if personal data
# 6. Cross-check with ISO 42001 AIMS evidence (compliance-team-iso42001)
# 7. Output: classification memo + conformity plan + obligation list
```

### Workflow 2: Annex IV Technical Documentation Build (per high-risk system, 2–4 weeks)
**Goal:** assemble the Annex IV pack before conformity assessment.

```bash
# 1. Run conformity assessment planner to get the checklist
python scripts/conformity_assessment_planner.py system.json
# 2. Assemble: system description, architecture, training data, validation, risk management
# 3. Reference ISO 42001 evidence where it satisfies Annex IV items
# 4. Reference ISO 27001 evidence for security controls
# 5. Run Article 9 risk management lifecycle
# 6. Sign EU declaration of conformity (Article 47) AFTER assessment passes
# 7. Affix CE marking (Article 48)
# 8. Register in EU database (Article 71) — high-risk Annex III systems
```

### Workflow 3: Pre-Deployment Obligation Audit (per system, before launch)
**Goal:** confirm all active obligations are in place before EU placement.

```bash
# 1. Confirm classification still correct (re-run classifier if system changed)
# 2. Confirm conformity assessment completed (if high-risk)
# 3. Confirm transparency requirements (Article 50) — for chatbots, deepfakes, emotion detection
# 4. Confirm post-market monitoring system (Article 72) is live
# 5. Confirm serious-incident reporting procedure (Article 73) is documented
# 6. For deployers: FRIA done (Article 27, if applicable); workers informed (Article 26(7))
# 7. For GPAI: Articles 51-55 obligations met if applicable
```

### Workflow 4: Annual Compliance Refresh (per organization, yearly)
**Goal:** re-verify classifications + obligations as the Act phases in.

1. List all AI systems on or planned for EU market
2. Run classifier for each — Article 5 prohibited list may expand via delegated acts
3. Run obligation tracker — deadlines shift as Title III phases in (2025 → 2026 → 2027)
4. For each high-risk system: verify post-market monitoring data flow + serious incident reporting capacity
5. Update Annex IV technical documentation per Article 11 ongoing requirement
6. Pair with ISO 42001 management review (Clause 9.3) if both operate

## Output Standards

```
**Bottom Line:** [one sentence — classification + most-significant obligation]
**Article Citation:** [Article + paragraph number; do not paraphrase without cite]
**The Decision:** [one of: classify | conformity-route | obligation-scope]
**The Evidence:** [Article + Annex references; classification confidence]
**How to Act:** [3 concrete next steps with owner + deadline aligned to phasing]
**Your Decision:** [the call for compliance officer or legal counsel — risk-class disputes, novel cases, GPAI threshold determinations]
```

## Adjacent Skills

- `ra-qm-team/skills/gdpr-dsgvo-expert/` — GDPR DPIA + lawful basis (most AI systems also trigger GDPR)
- `ra-qm-team/compliance-team-iso42001/` — ISO 42001 AIMS (voluntary management system that satisfies parts of Article 17 QMS for providers)
- `ra-qm-team/skills/information-security-manager-iso27001/` — ISO 27001 for cybersecurity requirements (Article 15)
- `ra-qm-team/skills/risk-management-specialist/` — ISO 14971 risk management (referenced for safety-component AI under Article 6(1))
- `ra-qm-team/skills/mdr-745-specialist/` — MDR 2017/745 (medical-device AI overlap)
- `compliance-os/` — Meta-orchestrator for multi-framework programs
- `c-level-advisor/chief-ai-officer-advisor/` — Executive AI strategy

## References

- [eu_ai_act_titles.md](references/eu_ai_act_titles.md) — Titles I–XII Article-by-Article walkthrough with deployer/provider/importer/distributor obligation breakdown
- [high_risk_systems_annex_iii.md](references/high_risk_systems_annex_iii.md) — Annex III 8 categories detailed + Article 6(2)–(3) interaction + carve-out test
- [gpai_obligations.md](references/gpai_obligations.md) — Articles 51–55 GPAI track + systemic-risk threshold + transparency rules + Code of Practice status
- [cross_framework_mapping_ai_act.md](references/cross_framework_mapping_ai_act.md) — AI Act ↔ ISO 42001 ↔ NIST AI RMF ↔ GDPR control-level mapping

---

**Version:** 1.0.0
**Status:** Production Ready
