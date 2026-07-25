# EU AI Act ↔ ISO 42001 ↔ NIST AI RMF ↔ GDPR — Cross-Framework Mapping

This reference answers exactly one decision: **for each EU AI Act obligation, what existing framework evidence can I reuse?**

The point: minimize duplicate work. EU AI Act compliance for high-risk systems requires significant artefacts (Annex IV technical documentation, Article 9 risk management, Article 17 QMS, Article 72 post-market monitoring). Most of these can be satisfied — partly or fully — by evidence from existing ISO 42001 / ISO 27001 / GDPR programs.

## Framework Reuse Cheat Sheet

| EU AI Act requirement | Best reuse source | Reuse confidence |
|---|---|---|
| Article 9 Risk management system | ISO 42001 Clause 6.1 + ISO 23894 process | HIGH |
| Article 10 Data governance | ISO 42001 Annex A.7 + GDPR Art. 5 + Records of Processing (Art. 30) | HIGH |
| Article 11 Technical documentation (Annex IV) | ISO 42001 documented information (Clause 7.5) + Annex A.6.2.7 model cards | HIGH |
| Article 12 Logging | ISO 27001 A.8.15 + ISO 42001 A.9.4 | HIGH |
| Article 13 Instructions for use | ISO 42001 A.8.3 user information | HIGH |
| Article 14 Human oversight | ISO 42001 A.9 use of AI systems | MEDIUM (AI Act more prescriptive) |
| Article 15 Accuracy, robustness, cybersecurity | ISO 27001 (cybersecurity) + ISO 42001 A.6.2.4 V&V + NIST AI RMF MEASURE 2 | HIGH |
| Article 16 Provider obligations | ISO 42001 Clauses 5–6 leadership + responsibilities | MEDIUM |
| Article 17 Quality management system | ISO 42001 entire AIMS satisfies this in large part | HIGH (subject to Article 17(1) item-by-item check) |
| Article 26 Deployer obligations | ISO 42001 Annex A.9 + own operating discipline | MEDIUM |
| Article 27 FRIA (public sector) | ISO 42001 A.5 impact assessment + GDPR DPIA — both inputs | MEDIUM |
| Article 50 Transparency | New artifacts (Article 50 specific) — limited reuse | LOW |
| Article 72 Post-market monitoring | ISO 42001 A.9.3 monitoring + ISO 13485 PMS pattern | HIGH |
| Article 73 Serious-incident reporting | ISO 27001 A.6.8 information security event reporting + GDPR Art. 33 breach notification — extend | MEDIUM |

## Article-by-Article Detailed Mapping

### Article 9 — Risk Management System

**EU AI Act requirement:** establish, implement, document, maintain a risk management system across the AI lifecycle.

**Best reuse:**
- ISO/IEC 42001 Clause 6.1 + Annex A.5: provides the management-system framing
- ISO/IEC 23894:2023: provides the AI-specific risk methodology
- NIST AI RMF "MAP" + "MANAGE" functions: provides operational guidance

**Gap to fill:**
- Article 9(2)(c) requires "iterative" application across full lifecycle — operational discipline, not just artifact
- Article 9(5) requires testing of high-risk systems in real-world conditions or in test environments

### Article 10 — Data Governance

**EU AI Act requirement:** training, validation, test datasets meet quality criteria including:
- Article 10(3): "relevant, sufficiently representative, free of errors, complete"
- Article 10(2)(d): documentation of data origin and provenance
- Article 10(5): processing of special categories permissible if strictly necessary for bias detection

**Best reuse:**
- ISO 42001 Annex A.7.2 data management + A.7.3 data quality + A.7.4 data provenance + A.7.5 data preparation: direct overlap
- GDPR Article 5 (data minimisation), Article 6 (lawful basis), Article 30 (records of processing): for personal data
- ISO 8000 + DAMA-DMBOK 2: data-quality framework

**Gap to fill:**
- Article 10(5) bias-detection-specific processing of special categories — explicit DPIA + ISO 23894 risk treatment combination

### Article 11 — Technical Documentation (Annex IV)

**EU AI Act requirement:** maintain technical documentation per Annex IV (8 items).

**Best reuse per Annex IV item:**

| Annex IV item | Reuse source |
|---|---|
| 1. General description | ISO 42001 SKILL scope statement; ISO 27001 system documentation |
| 2. System elements (architecture, training data, validation, human oversight) | ISO 42001 Annex A.6 + A.7 + model card pattern (Mitchell 2019) |
| 3. Monitoring, functioning, control | ISO 42001 Annex A.9 + ISO 27001 A.8.15 logging |
| 4. Risk management | ISO 42001 Clause 6.1 + Annex A.5 |
| 5. Changes after market | ISO 27001 A.8.32 change management + ISO 42001 A.6.2.5 |
| 6. Harmonised standards applied | Standards register |
| 7. EU declaration of conformity | New artifact (signed at end) |
| 8. Post-market monitoring | ISO 42001 A.9.3 + ISO 13485 PMS pattern |

### Article 14 — Human Oversight

**EU AI Act requirement:** design + enable effective human oversight by natural persons to prevent/minimise risks. Including:
- Article 14(4)(a-e): oversight personnel must understand capabilities/limitations, remain aware of automation bias, correctly interpret output, decide not to use the output, intervene/halt operation

**Best reuse:**
- ISO 42001 Annex A.9.2 intended use + A.9 use of AI systems: partial coverage
- ISO 42001 Clause 7.2 competence (define competence for oversight personnel)
- Workplace operating discipline (procedure for halting + escalating)

**Gap to fill:**
- Article 14 is more prescriptive than ISO 42001 — requires explicit design for the 5 oversight capabilities. Build the design artefact net-new.

### Article 17 — Quality Management System

**EU AI Act requirement:** providers shall put in place QMS ensuring compliance. Article 17(1)(a)–(m) lists 13 items the QMS must include.

**Best reuse:**
- ISO 42001 AIMS: satisfies most Article 17(1) items
- ISO 9001 / ISO 13485 (if already operated): satisfies the "general QMS" framing
- Map each Article 17(1) item against ISO 42001 evidence to identify any remaining gap

**Article 17(1) item-by-item mapping to ISO 42001:**

| Article 17(1) item | ISO 42001 reference |
|---|---|
| (a) Compliance strategy | Clause 5.2 AI policy |
| (b) Techniques for design/development/QA | Annex A.6 lifecycle |
| (c) Examination, testing, validation procedures | Annex A.6.2.4 V&V |
| (d) Technical specs + standards applied | Clause 7.5 documented information |
| (e) Data management procedures | Annex A.7 |
| (f) Risk management system | Clause 6.1 + Annex A.5 |
| (g) Post-market monitoring | Annex A.9.3 |
| (h) Reporting of serious incidents | Annex A.8.4 |
| (i) Communication w/ authorities, notified bodies, suppliers | Annex A.10 + Clause 7.4 |
| (j) Internal record-keeping system | Clause 7.5 + Annex A.9.4 logging |
| (k) Resource management including supply security | Annex A.4 |
| (l) Accountability framework | Annex A.3 |
| (m) Internal audit + management review | Clause 9.2 + 9.3 |

This is the closest framework alignment in the entire mapping — ISO 42001 is essentially the AI-specific operating model for Article 17.

### Article 26 — Deployer Obligations

**EU AI Act requirement:** use AI per provider's instructions, assign human oversight, ensure input data quality, monitor + cease use if Article 79 risk, retain logs ≥ 6 months, inform workers.

**Best reuse:**
- ISO 42001 Annex A.9 use of AI systems: partial
- Existing operational procedures (HR notification for workforce-impacting AI)

**Gap to fill:** Article 26 is operationally specific; build deployer-procedure net-new with reuse cross-references.

### Article 50 — Transparency

**EU AI Act requirement:** disclose AI interaction; mark synthetic content; disclose emotion/biometric categorisation; disclose deepfakes.

**Best reuse:** none direct. New UX/disclosure artefacts required.

**Cross-reference:** ISO 42001 Annex A.8 information for interested parties (overlap on framing only).

### Article 72 — Post-Market Monitoring

**EU AI Act requirement:** establish + document post-market monitoring system collecting, documenting, analysing data on performance throughout lifetime.

**Best reuse:**
- ISO 42001 Annex A.9.3 monitoring: direct overlap
- ISO 13485 post-market surveillance pattern (for medical-device AI providers): proven operational template
- NIST AI RMF MEASURE 4 + MANAGE 4: methodology

### Article 73 — Serious-Incident Reporting

**EU AI Act requirement:** report serious incidents (Article 3(49)) to market surveillance authority — 15 days general, 2 days for critical infrastructure.

**Best reuse:**
- ISO 27001 A.6.8 information security event reporting: process framework
- GDPR Article 33 personal data breach notification: 72-hour pattern
- ISO 13485 vigilance reporting (medical devices)

**Gap to fill:** Article 73 has its own serious-incident definition + report content; align reporting template with the regulation specifically.

## NIST AI RMF ↔ EU AI Act Cross-Walk

NIST AI RMF is voluntary US guidance but maps cleanly to EU AI Act provisions:

| NIST AI RMF function | EU AI Act articles satisfied (partial) |
|---|---|
| GOVERN | Articles 16, 17, 26 (broad governance) |
| MAP | Articles 9 (risk identification), 10 (data) |
| MEASURE | Articles 15 (accuracy/robustness/cybersecurity), 9 (risk evaluation) |
| MANAGE | Articles 9 (risk treatment), 26 (deployer monitoring) |

A mature NIST AI RMF program covers ~70% of EU AI Act high-risk system obligations operationally.

## GDPR ↔ EU AI Act Interaction

The two regulations interact heavily. Recital 10 + Article 10 of the AI Act + EDPB Opinion 28/2024 (Dec 2024) establish:

1. **AI Act does not modify GDPR.** GDPR continues to apply in full to personal data processing in AI systems.
2. **Article 10(5) AI Act** permits processing of special categories of personal data strictly necessary for bias detection — but only with safeguards (e.g., effective anonymisation after use).
3. **DPIA + FRIA overlap (Article 27 AI Act).** Both can be integrated into a single impact-assessment artefact for public-sector deployers of high-risk AI systems.
4. **Right to explanation (Article 86 AI Act + Article 22 GDPR).** Article 86 strengthens individual rights for high-risk AI decisions.

## When This Reference Doesn't Help

- **ISO 42001 deep-dive.** See `compliance-team-iso42001/`.
- **Single-framework audit simulation.** See `compliance-os/scripts/audit_simulator.py`.
- **Specific NIST AI RMF Playbook entries.** Refer to NIST AI 100-1 directly.

---

**Source authorities (non-exhaustive):**

- **Regulation (EU) 2024/1689** — the AI Act
- **ISO/IEC 42001:2023** — AI Management System
- **ISO/IEC 23894:2023** — AI risk management process
- **ISO/IEC 27001:2022** — Information security management
- **NIST AI Risk Management Framework 1.0** (Jan 2023) + Generative AI Profile (NIST AI 600-1, July 2024)
- **General Data Protection Regulation (EU) 2016/679** — GDPR
- **EDPB Opinion 28/2024** — AI models and personal data (December 2024)
- **EDPS** — interpretive opinions on AI Act ↔ GDPR interaction
- **European Commission** — Article 17 implementing guidance (continuously updated)
- **BSI** — Cross-walking ISO 42001 and EU AI Act (white paper 2024)
- **IAPP** — EU AI Act Tracker + AI Governance Center materials
