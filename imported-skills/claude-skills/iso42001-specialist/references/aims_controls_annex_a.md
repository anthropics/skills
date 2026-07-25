# ISO/IEC 42001 Annex A — 38 Controls Catalogue

This reference answers exactly one decision: **for each Annex A control, what does implementation look like, what evidence does the auditor want, and what's the severity if it's missing?**

Pair with `scripts/ai_risk_register_builder.py` to map risks to controls.

## Structure of Annex A

ISO/IEC 42001 Annex A is a *normative* annex containing reference controls. The standard requires (per Clause 6.1.3) that the organization compare its determined controls to Annex A to verify no necessary controls have been omitted. Unlike ISO 27001 where Annex A is presumed-applicable, ISO 42001 Annex A controls are applied based on risk — if a control doesn't apply (e.g., A.10 third-party AI when you use no third-party AI), document the exclusion with justification.

**The 10 control categories (A.1 is the structural intro; A.2–A.10 are the operational controls):**

| ID | Category | Control count | Maps to clause |
|---|---|---|---|
| A.2 | Policies related to AI | 2 | 5.2 |
| A.3 | Internal organization | 2 | 5.3 |
| A.4 | Resources for AI systems | 3 | 7.1 |
| A.5 | Assessing impacts of AI systems | 3 | 6.1.4, 8.2 |
| A.6 | AI system lifecycle | 8 | 8.3 |
| A.7 | Data for AI systems | 5 | 8.3 |
| A.8 | Information for interested parties | 4 | 7.4, 9.1 |
| A.9 | Use of AI systems | 4 | 8.3, 9.1 |
| A.10 | Third-party & customer relationships | 5 | 8.4 |

Total: **38 controls** across 9 operational categories.

## A.2 — Policies (severity if missing: CRITICAL)

| Control | Title | What auditor wants | Reusable from |
|---|---|---|---|
| **A.2.2** | AI policy | Signed AI policy meeting Clause 5.2 requirements | ISO 27001 A.5.1 (information security policy) — extend |
| **A.2.3** | Alignment of AI policy with other policies | Mapping showing AI policy doesn't contradict info-sec, privacy, quality, code-of-conduct policies | New artifact; document the cross-references |

## A.3 — Internal Organization (severity: MAJOR)

| Control | Title | What auditor wants | Reusable from |
|---|---|---|---|
| **A.3.2** | AI roles & responsibilities | RACI matrix; named AIMS owner | ISO 27001 A.5.2; extend to AI |
| **A.3.3** | Reporting of concerns | Whistleblower / concerns procedure for AI-specific issues (bias, harm, misuse) | Existing whistleblower; AI-extend |

## A.4 — Resources (severity: MAJOR)

| Control | Title | What auditor wants | Reusable from |
|---|---|---|---|
| **A.4.2** | Resources — data | Data inventory; provenance; quality assessment | ISO 27001 A.5.9 inventory of assets — extend |
| **A.4.3** | Resources — tooling | Inventory of ML tooling; license & dependency tracking | Existing software-asset management |
| **A.4.4** | Resources — human resources | Competence requirements + training records (Clause 7.2) | ISO 27001 A.6.3 awareness; ISO 13485 6.2 competence |

## A.5 — Impact Assessment (severity: CRITICAL)

| Control | Title | What auditor wants | Reusable from |
|---|---|---|---|
| **A.5.2** | AI system impact assessment | Documented impact assessment for each AI system; covers individuals, groups, society | GDPR DPIA — partial; AI scope wider (third-party harm, environmental, societal) |
| **A.5.3** | Process for impact assessment | Documented procedure with triggers (launch, material change, complaint) | New procedure |
| **A.5.4** | Documentation of impact assessment | Signed impact assessment record with management approval for high-impact systems | New artifact |

## A.6 — AI System Lifecycle (severity: CRITICAL)

| Control | Title | What auditor wants | Reusable from |
|---|---|---|---|
| **A.6.1.2** | Objectives for AI system development | Stated AI-system objectives aligned to AI policy + use intent | New artifact (per system) |
| **A.6.1.3** | Processes for management of the AI system lifecycle | Procedure covering design → data → model → V&V → deployment → operation → decommission | New procedure |
| **A.6.2.2** | AI system objectives & requirements | Documented requirements traceable to objectives | ISO 13485 7.3 design & development — extend |
| **A.6.2.3** | Documentation of AI system design & development | Design records (architecture, datasets, model card) under document control | ISO 13485 7.3 — extend |
| **A.6.2.4** | Verification & validation of AI system | Test plan + evaluation results; defined acceptance criteria | New artifact per system; reference NIST AI RMF "Measure" function |
| **A.6.2.5** | Deployment of AI system | Deployment checklist; environment hand-off; rollback plan | ISO 27001 A.8.32 change management — extend |
| **A.6.2.6** | Operation & monitoring of AI system | Monitoring plan with thresholds + escalation | New per system |
| **A.6.2.7** | Technical documentation of AI system | Model card or system card per Mitchell et al. (2019) / Gebru et al. (2021) | New artifact |

## A.7 — Data for AI Systems (severity: CRITICAL)

| Control | Title | What auditor wants | Reusable from |
|---|---|---|---|
| **A.7.2** | Data management | Data lifecycle procedure (acquisition → use → retention → deletion) | GDPR Art. 5 data minimisation; ISO 27001 A.5.10 acceptable use |
| **A.7.3** | Data quality | Defined data-quality dimensions; measured; reported | New; reference DAMA-DMBOK 2 / ISO 8000 |
| **A.7.4** | Data provenance | Documented data lineage; consent / legitimate basis recorded | GDPR records of processing (Art. 30) — extend |
| **A.7.5** | Data preparation | Documented preprocessing procedure | New artifact per system |
| **A.7.6** | Data privacy considerations | Privacy review per data category | GDPR DPIA — extend |

## A.8 — Information for Interested Parties (severity: MAJOR)

| Control | Title | What auditor wants | Reusable from |
|---|---|---|---|
| **A.8.2** | System documentation | Public-facing documentation per Annex A.6.2.7 | Model card / system card |
| **A.8.3** | User information | UX-level disclosure: this is AI; what it does; its limitations | New; align with EU AI Act Article 50 transparency |
| **A.8.4** | Communication of AI incidents | Incident communication procedure including external notification timing | GDPR Art. 33–34 breach notification — extend |
| **A.8.5** | Information for affected parties | Communication for AI-affected populations (those subject to AI decisions) | New; align with EU AI Act Article 86 redress |

## A.9 — Use of AI Systems (severity: MAJOR)

| Control | Title | What auditor wants | Reusable from |
|---|---|---|---|
| **A.9.2** | Intended use of AI system | Documented intended-use statement per system | New artifact |
| **A.9.3** | Monitoring of operation | Continuous monitoring with defined metrics + thresholds | NIST AI RMF "Measure" — extend |
| **A.9.4** | Logging of AI system events | Tamper-evident logs covering decisions, drift indicators, incidents | ISO 27001 A.8.15 logging — extend |
| **A.9.5** | Use of system after deployment | Procedure for in-use changes (retraining, fine-tuning) with re-evaluation triggers | New procedure |

## A.10 — Third-Party & Customer Relationships (severity: MAJOR)

| Control | Title | What auditor wants | Reusable from |
|---|---|---|---|
| **A.10.2** | Supplier (third-party) relationships | AI-specific contract clauses (training data use, drift notification, sub-processor list) | ISO 27001 A.5.19 supplier relationships — extend |
| **A.10.3** | Customer relationships | Customer-facing AI obligations (transparency, opt-out, redress) | ISO 27001 A.5.20 — extend |
| **A.10.4** | Allocation of responsibilities between organization & third party | RACI for shared AI responsibilities (data labeling, model training, hosting, monitoring) | New artifact (per supplier) |
| **A.10.5** | Confidentiality of AI-related information | NDA scope covers AI-system internals (architecture, training data, weights) | ISO 27001 A.6.6 confidentiality — extend |
| **A.10.6** | Termination of AI service relationships | Procedure for safe AI-vendor exit (data return, model deletion, monitoring transition) | ISO 27001 A.5.20 service-level review — extend |

## How to Read This Catalogue

- **CRITICAL** = nonconformity blocks certification at stage 1
- **MAJOR** = nonconformity requires corrective action plan at stage 2; may delay certification
- **MINOR** = nonconformity recorded; corrective action expected within agreed timeline

**Audit evidence rule:** for every control selected as applicable, the auditor will ask three questions: (1) Where is the documented procedure? (2) Where are the records showing the procedure was followed? (3) Where is the evidence of management review of those records? If any of the three is missing, the control is partially implemented.

## When This Reference Doesn't Help

- **Specific Annex A control text.** This is a summary. The normative text is in ISO/IEC 42001:2023 Annex A — buy the standard.
- **Risk-to-control mapping methodology.** See `aims_implementation_guide.md` and ISO/IEC 23894:2023.
- **EU AI Act control overlap.** See `cross_framework_mapping_ai.md`.

---

**Source authorities (non-exhaustive):**

- **ISO/IEC 42001:2023** — Annex A normative controls (the authoritative source)
- **ISO/IEC 23894:2023** — AI risk management process (drives Annex A selection)
- **ISO/IEC 22989:2022** — AI concepts and terminology
- **NIST AI Risk Management Framework 1.0** (Jan 2023) + AI RMF Playbook — operational guidance mapping cleanly to Annex A
- **BSI AIC4 — Artificial Intelligence Cloud Service Compliance Criteria Catalogue** (2021) — sector-specific overlay for cloud AI providers
- **AAMI CR34971:2023** — Guidance for AI in medical devices
- **Mitchell et al.** — "Model Cards for Model Reporting" (FAT* 2019) — origin of model-card pattern referenced by A.6.2.7
- **Gebru et al.** — "Datasheets for Datasets" (CACM 2021) — datasheet pattern referenced by A.7.4
- **ISACA** — *Auditing Artificial Intelligence* (2nd ed., 2024) — practitioner audit checklist
