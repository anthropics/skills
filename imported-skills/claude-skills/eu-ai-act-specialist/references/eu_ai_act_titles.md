# EU AI Act (Regulation (EU) 2024/1689) — Titles I–XII Walkthrough

This reference answers exactly one decision: **what does each Title of the Act actually require, and which Articles do I cite in compliance artifacts?**

Pair with `scripts/ai_system_risk_classifier.py` to map a system to obligations.

## Structure of the Regulation

The Act has 13 Titles + 13 Annexes. Adopted as Regulation (EU) 2024/1689 (the "AI Act"); published in OJEU L on 12 July 2024; entered into force 1 August 2024 (Article 113).

## Title I — General Provisions (Articles 1–4)

| Article | Topic | Key requirement |
|---|---|---|
| **1** | Subject matter | Establishes harmonised rules for AI systems placed on EU market, used or put into service |
| **2** | Scope | Applies to providers, deployers, importers, distributors, authorized representatives. Extraterritorial: applies to non-EU providers placing systems on EU market. Excludes military / national security / pure scientific research |
| **3** | Definitions | "AI system" (Article 3(1)): a machine-based system designed to operate with varying levels of autonomy that may exhibit adaptiveness after deployment; infers from input how to generate outputs (predictions, content, recommendations, decisions). Per Commission Feb 2025 Guidelines, excludes simple rule-based systems with no adaptiveness |
| **4** | AI literacy | **In force from 2 Feb 2025.** Organizations must ensure staff dealing with AI systems have AI literacy proportionate to their roles |

## Title II — Prohibited AI Practices (Article 5)

**In force from 2 Feb 2025.** Penalty: up to EUR 35M or 7% worldwide annual turnover (Article 99).

8 prohibited categories per Article 5(1):

- **(a)** Subliminal techniques beyond awareness causing harm
- **(b)** Exploitation of vulnerabilities (age, disability, socioeconomic situation)
- **(c)** Social scoring by public authorities causing detrimental treatment
- **(d)** Predictive policing based solely on profiling natural persons (with narrow law-enforcement exceptions per Article 5(2))
- **(e)** Untargeted scraping of facial images for facial recognition databases
- **(f)** Emotion recognition in workplace and educational institutions
- **(g)** Biometric categorisation by sensitive attributes (race, religion, political opinions, sexual orientation, etc.)
- **(h)** Real-time remote biometric identification in publicly accessible spaces for law-enforcement purposes (with narrow Article 5(2)(d)–(h) exceptions)

## Title III — High-Risk AI Systems (Articles 6–49)

The densest part of the regulation. **Title III general high-risk obligations in force 2 Aug 2026; Annex I sectoral 2 Aug 2027.**

### Chapter 1 — Classification (Articles 6–7)

- **Article 6(1)** + Annex I: AI systems that are safety components of products covered by sectoral law (machinery, toys, medical devices, etc.) are high-risk
- **Article 6(2)** + Annex III: AI systems in 8 categories (biometrics, critical infrastructure, education, employment, essential services, law enforcement, migration, justice) are high-risk
- **Article 6(3)**: carve-out — a system in Annex III is NOT high-risk if it performs a narrow procedural task, improves a previously completed human activity, detects decision-making patterns without replacing human assessment, or performs a preparatory task. **Profiling overrides the carve-out** (Article 6(3) last sentence)

See `high_risk_systems_annex_iii.md` for the detailed Annex III walkthrough.

### Chapter 2 — Requirements for High-Risk Systems (Articles 8–17)

| Article | Requirement |
|---|---|
| **8** | Compliance with all Section 2 requirements |
| **9** | Risk management system across full lifecycle |
| **10** | Data governance: training/validation/test datasets quality + bias examination |
| **11** | Technical documentation per Annex IV |
| **12** | Automatic event logging |
| **13** | Transparency + instructions for use to deployers |
| **14** | Human oversight design |
| **15** | Accuracy, robustness, cybersecurity |
| **16** | General provider obligations + named contact person |
| **17** | Quality management system (provider) |

### Chapter 3 — Obligations of Actors (Articles 22–27)

| Article | Topic | Applies to |
|---|---|---|
| **22** | Authorized representative | Non-EU providers must appoint one |
| **23** | Importer obligations | Verify provider conformity assessment before import |
| **24** | Distributor obligations | Verify CE marking before making available |
| **25** | Responsibilities along the value chain | Substantial modification turns deployer into provider |
| **26** | Deployer obligations | Use per instructions; human oversight; input data; logs; transparency |
| **27** | Fundamental Rights Impact Assessment (FRIA) | Public-sector deployers + essential-services deployers of high-risk |

### Chapter 4 — Notified Bodies (Articles 28–39)

Procedures for designating + monitoring notified bodies (involved in Module H conformity assessment per Annex VII).

### Chapter 5 — Standards, Conformity Assessment, Certificates, Registration (Articles 40–49)

| Article | Topic |
|---|---|
| **40** | Harmonised standards — presumption of conformity |
| **41** | Common specifications (where standards lacking) |
| **43** | Conformity assessment procedure (Module A internal control vs Module H notified body) |
| **47** | EU declaration of conformity (provider signs; 10-year retention) |
| **48** | CE marking |
| **49** | Registration in EU database (Article 71) for Annex III systems |

## Title IV — Transparency Obligations (Article 50)

**In force from 2 Aug 2025.**

| Article 50 paragraph | Requirement |
|---|---|
| **50(1)** | Disclose AI interaction (chatbots): natural persons must be informed |
| **50(2)** | Mark synthetic content (machine-readable) as AI-generated |
| **50(3)** | Disclose emotion recognition / biometric categorisation to subjects (outside Article 5 prohibition) |
| **50(4)** | Disclose deepfakes (image/audio/video) — exception for art, satire, security |

## Title V — General-Purpose AI Models (Articles 51–55)

**In force from 2 Aug 2025.** See `gpai_obligations.md` for the detailed walkthrough.

| Article | Topic |
|---|---|
| **51** | Classification of GPAI with systemic risk (training compute ≥ 10²⁵ FLOPs) |
| **52** | Procedure for adding/removing systemic-risk designation |
| **53** | Obligations for ALL GPAI providers (technical docs, transparency to downstream, copyright policy, training data summary) |
| **54** | Authorized representative for non-EU GPAI providers |
| **55** | Additional obligations for systemic-risk GPAI (model evaluations, adversarial testing, incident reporting, cybersecurity) |

## Title VI — Measures in Support of Innovation (Articles 57–63)

| Article | Topic |
|---|---|
| **57** | AI regulatory sandboxes by Member States |
| **58** | Modalities for sandboxes |
| **59** | Further processing of personal data for AI development in sandboxes |
| **60** | Real-world testing of high-risk systems outside sandboxes |
| **62** | SME / start-up specific measures |

## Title VII — Governance (Articles 64–70)

| Article | Body |
|---|---|
| **64** | European Artificial Intelligence Office (the "AI Office") |
| **65** | European AI Board |
| **66** | Member State national competent authorities |
| **67** | Advisory Forum (industry + civil society) |
| **68** | Scientific Panel of independent experts |

## Title VIII — EU Database (Article 71)

EU-wide database of stand-alone high-risk Annex III AI systems. Provider registration before placing on market.

## Title IX — Post-Market Monitoring, Information Sharing, Market Surveillance (Articles 72–84)

| Article | Topic |
|---|---|
| **72** | Provider post-market monitoring system |
| **73** | Serious-incident reporting (provider) — 15 days general; 2 days for critical infrastructure |
| **74** | Market surveillance + AI Office cooperation |
| **75–84** | Market surveillance powers, enforcement, mutual assistance |

## Title X — Codes of Conduct and Guidelines (Articles 95–96)

Voluntary codes of conduct extending Title III principles to non-high-risk systems. Commission may issue guidelines.

## Title XI — Delegated and Implementing Acts (Articles 97–98)

Commission powers to update Annexes (notably Annex III categories) via delegated acts.

## Title XII — Final Provisions (Articles 99–113)

| Article | Topic |
|---|---|
| **99** | Penalties: up to EUR 35M / 7% turnover (Article 5); EUR 15M / 3% (most high-risk); EUR 7.5M / 1% (incorrect info) |
| **102** | Amendments to other regulations (medical devices, etc.) |
| **113** | Entry into force + application phasing |

## Annexes — At a Glance

| Annex | Topic |
|---|---|
| **I** | List of EU sectoral product legislation (machinery, toys, MDR, IVDR, etc.) — Article 6(1) trigger |
| **II** | List of Union harmonisation legislation |
| **III** | High-risk AI systems referred to in Article 6(2) — 8 categories |
| **IV** | Technical documentation referred to in Article 11 (8 items) |
| **V** | EU declaration of conformity (Article 47) |
| **VI** | Conformity assessment Module A — Internal Control |
| **VII** | Conformity assessment Module H — Full Quality Assurance |
| **VIII** | Information to be submitted upon registration in EU database (Article 71) |
| **IX** | Information for testing in real-world conditions (Article 60) |
| **X** | Union legislative acts on large-scale IT systems |
| **XI** | Technical documentation for GPAI providers (Article 53) |
| **XII** | Transparency information for downstream providers (Article 53(1)(b)) |
| **XIII** | Designation of GPAI with systemic risk (Article 51 criteria) |

## When This Reference Doesn't Help

- **Specific Annex III high-risk system classification.** See `high_risk_systems_annex_iii.md`.
- **GPAI obligations detail.** See `gpai_obligations.md`.
- **Cross-walking to ISO 42001 / NIST AI RMF.** See `cross_framework_mapping_ai_act.md`.

---

**Source authorities (non-exhaustive):**

- **Regulation (EU) 2024/1689** — the AI Act (the binding regulation; published in OJEU L on 12 July 2024)
- **European Commission** — Guidelines on the definition of an AI system (Feb 2025)
- **European Commission** — Guidelines on prohibited AI practices (Feb 2025)
- **European Commission Q&A** — AI Act explanatory materials (continuously updated)
- **European Data Protection Board (EDPB)** — Opinion 28/2024 (Dec 2024) on personal-data processing in AI models
- **European Data Protection Supervisor (EDPS)** — AI Act commentary + GDPR-AI Act interaction
- **ENISA** — Multilayer Framework for Good Cybersecurity Practices for AI (Mar 2023)
- **IAPP** — EU AI Act Tracker (continuously updated practitioner reference)
- **CEN-CENELEC JTC 21** — harmonised standards work programme (Article 40 reference)
