---
name: "ai-act-readiness"
description: "/cs:ai-act-readiness <system> — EU AI Act 6-question forcing interrogation. Use during AI-system intake, before EU deployment, or during annual compliance refresh as Article 113 obligations phase in (2025-02-02 / 2025-08-02 / 2026-08-02 / 2027-08-02)."
---

# /cs:ai-act-readiness — EU AI Act Forcing Questions

**Command:** `/cs:ai-act-readiness <system>`

The EU AI Act compliance operator pressure-tests any AI system before EU deployment. Six Article-cited questions before any EU placement, conformity assessment, or annual compliance refresh.

## When to Run

- During AI-system intake review (per new system or material change)
- Before placing an AI system on the EU market
- Before signing the EU declaration of conformity (Article 47)
- During annual compliance refresh (Article 113 phasing brings new obligations)
- When the organization's role changes (deployer becomes provider via Article 25(1) substantial modification)
- When training compute approaches 10^25 FLOPs (Article 51 systemic-risk threshold)

## The Six EU AI Act Questions

### 1. Article 5: Is this a prohibited AI practice?
**Penalty: up to 35M EUR or 7% worldwide turnover.**
- 8 categories: subliminal manipulation, exploitation of vulnerabilities, social scoring, predictive policing, untargeted facial scraping, emotion recognition in workplace/education, biometric categorisation by sensitive attributes, real-time public biometric ID by law enforcement
- Run `ai_system_risk_classifier.py`
- If yes → STOP. Cannot place on EU market. No exceptions outside Article 5(2) carve-outs.

### 2. Article 6 + Annex III: Is this high-risk?
**Annex III triggers high-risk; Article 6(3) carve-out conditional.**
- 8 categories: biometrics, critical infrastructure, education, employment, essential services, law enforcement, migration, justice
- Carve-out applies only if Article 6(3)(a)-(d) AND no profiling of natural persons
- Profiling overrides carve-out (Article 6(3) last sentence)
- Run `ai_system_risk_classifier.py`

### 3. Article 43: For high-risk, Module A or Module H?
**Biometrics → Module H (notified body) by default; others → Module A if harmonised standards applied.**
- Run `conformity_assessment_planner.py`
- Module A (Annex VI): internal control with presumption of conformity if Article 40 harmonised standards applied
- Module H (Annex VII): full QMS + notified body for biometrics or where standards lacking
- Annex IV technical documentation: 8 items required before placing on market

### 4. Article 25: What role does the company play?
**Provider obligations are heaviest; substantial modification turns deployer into provider.**
- Provider (Article 3(3)): placed on market; full Title III + Article 73 reporting
- Deployer (Article 3(4)): Article 26 obligations + Article 27 FRIA if public sector
- Importer (Article 3(6)): Article 23 verification of conformity
- Distributor (Article 3(7)): Article 24 CE marking verification
- Authorized representative (Article 22): non-EU providers must appoint
- Run `ai_act_obligation_tracker.py`

### 5. Article 50: Are transparency obligations satisfied?
**In force 2 Aug 2025.**
- Article 50(1): disclose AI interaction to natural persons (chatbots, virtual agents)
- Article 50(2): mark synthetic content as AI-generated
- Article 50(3): disclose emotion recognition / biometric categorisation (outside Article 5 prohibitions)
- Article 50(4): disclose deepfakes (image, audio, video) as AI-generated

### 6. Articles 51-55: Is this a GPAI? Does it have systemic risk?
**GPAI has parallel track; systemic risk above 10^25 FLOPs.**
- Article 3(63): general-purpose AI model definition
- Article 51: systemic-risk presumption (≥ 10^25 FLOPs training compute) or Commission designation
- Article 53: all GPAI providers — Annex XI technical docs, Annex XII downstream info, copyright policy, training-data summary
- Article 55: systemic-risk GPAI additional obligations — model evaluations, adversarial testing, incident reporting, cybersecurity
- Article 54: non-EU GPAI providers must appoint authorized representative

## Workflow

```bash
# 1. Risk classification
python ra-qm-team/skills/eu-ai-act-specialist/scripts/ai_system_risk_classifier.py systems.json

# 2. If high-risk: conformity assessment
python ra-qm-team/skills/eu-ai-act-specialist/scripts/conformity_assessment_planner.py system.json

# 3. Per-role obligation matrix
python ra-qm-team/skills/eu-ai-act-specialist/scripts/ai_act_obligation_tracker.py roles.json

# 4. Cross-framework reuse (ISO 42001 etc.)
python ../../skills/compliance-os/scripts/cross_framework_mapper.py program.json
```

## Output Format

```markdown
# EU AI Act Readiness: <system>
**Date:** YYYY-MM-DD
**Article Citations:** Every verdict below cites the specific Article.

## The Decision Being Made
[classify | conformity-route | obligation-scope | annual-refresh]

## Risk Classification
- Tier: prohibited | high_risk | limited_risk | minimal_risk
- Citation: Article X(Y) + Annex Z if applicable
- Rationale: <Article-cited rationale>
- GPAI: yes/no
- Systemic-risk GPAI: yes/no (per Article 51 10^25 FLOPs threshold)

## Conformity Assessment (if high-risk)
- Module: A | A_with_caveats | H | sectoral
- Citation: Article 43 + Annex VI/VII
- Notified body required: yes | no | optional
- Annex IV pack status: complete | in-progress | not-started

## Obligation Matrix
- Total obligations: N
- By deadline phase: 2025-02-02=A, 2025-08-02=B, 2026-08-02=C, 2027-08-02=D
- Highest-priority unmet obligation: <Article + description>

## Transparency (Article 50)
- 50(1) interaction disclosure: yes | no
- 50(2) synthetic content marking: yes | no | NA
- 50(3) emotion recognition disclosure: yes | no | NA
- 50(4) deepfake disclosure: yes | no | NA

## Cross-Framework Reuse
- ISO 42001 evidence applicable to Article 17 QMS: yes/no
- ISO 27001 evidence applicable to Article 15 cybersecurity: yes/no
- GDPR DPIA usable for Article 27 FRIA: yes/no

## Verdict
🟢 READY-FOR-EU | 🟡 GAPS-IDENTIFIED | 🔴 NOT-READY | 🚫 PROHIBITED

## Top 3 Actions
[3 concrete next steps with owner + Article-tied deadline]

## Legal Review Required
[Article-level ambiguities flagged for outside counsel: novel cases, GPAI threshold disputes, Article 5 boundary cases, Article 25 substantial-modification questions]
```

## Routing

- `/cs:compliance-readiness` — for multi-framework view (combine with ISO 42001 + GDPR)
- `/cs:aims-audit` — for ISO 42001 deep-dive
- `/cs:caio-review` — for executive AI strategy decisions
- `/cs:gc-review` — for novel-case legal review (GPAI threshold, Article 5 boundary, substantial-modification)
- `/cs:decide` — to log the verdict
- `/cs:freeze 30` — on EU launch commitments (regulatory exposure)

## Related

- Agent: [`cs-ai-act-compliance`](../../agents/cs-ai-act-compliance.md)
- Skill: [`eu-ai-act-specialist`](../../../ra-qm-team/skills/eu-ai-act-specialist/SKILL.md)
- Adjacent: `../../skills/compliance-os/`, `../aims-audit/`, `../compliance-readiness/`, `../../../ra-qm-team/skills/gdpr-dsgvo-expert/`

---

**Version:** 1.0.0
