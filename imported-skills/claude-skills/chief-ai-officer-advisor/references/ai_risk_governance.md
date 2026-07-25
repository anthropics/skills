# AI Risk & Governance — The Decision: "Is this AI use case high-risk, and how do we govern it?"

This reference answers exactly one decision: **for a specific AI use case, which regulations apply, what risk tier does it fall into, and what governance program is required?**

Pair with `scripts/ai_risk_classifier.py` for automation. **Not legal advice.**

## EU AI Act — The Centerpiece (in force 2026)

The EU AI Act (Regulation (EU) 2024/1689) is the most comprehensive AI regulation globally. It applies to any AI system **placed on the EU market or whose output is used in the EU**, regardless of where the provider is established.

### Risk Tiers (Article 5–7, Annex III)

#### 🔴 Tier 1: Prohibited (Article 5)

Cannot be deployed in EU at any safeguard level:

- **Social scoring** by public authorities causing detrimental treatment (Art. 5(1)(c))
- **Real-time remote biometric identification** by law enforcement in publicly accessible spaces (narrow exceptions for specific serious crimes only) (Art. 5(1)(h))
- **Subliminal manipulation** beyond a person's consciousness to materially distort behavior (Art. 5(1)(a))
- **Exploitation of vulnerabilities** (age, disability, social/economic situation) to materially distort behavior (Art. 5(1)(b))
- **Predictive policing** based solely on profiling (Art. 5(1)(d))
- **Untargeted facial recognition** scraping from internet or CCTV (Art. 5(1)(e))
- **Emotion recognition** in workplace or educational institutions (Art. 5(1)(f))
- **Biometric categorization** to infer race, political opinions, religion, etc. (Art. 5(1)(g))

#### 🟠 Tier 2: High-Risk (Article 6 + Annex III)

Permitted, but heavy obligations:

**Annex III domains:**

1. Biometric identification and categorization
2. Critical infrastructure (water, gas, electricity, traffic management)
3. Education and vocational training (access, assessment, monitoring during exams)
4. Employment, workers management (recruitment selection, promotion, task allocation)
5. Access to essential services (credit scoring, insurance pricing, public benefits, emergency dispatch)
6. Law enforcement (risk assessment, lie detection, evidence reliability, profiling)
7. Migration, asylum, border control (visa/asylum decisions, risk assessment)
8. Administration of justice and democratic processes

**Obligations for high-risk AI (Articles 8–15, 43, 49, 72):**

| Obligation | Article |
|---|---|
| Risk management system throughout lifecycle | Art. 9 |
| Data governance: representative, accurate, complete training data; bias mitigation | Art. 10 |
| Technical documentation per Annex IV | Art. 11 |
| Record-keeping / logging for traceability | Art. 12 |
| Transparency and instructions for use | Art. 13 |
| Human oversight design (override, stop button, monitoring) | Art. 14 |
| Accuracy, robustness, cybersecurity | Art. 15 |
| Quality management system | Art. 17 |
| Conformity assessment (self-assessment for most; Notified Body for biometric) | Art. 43 |
| Registration in EU database before deployment | Art. 49 |
| Post-market monitoring | Art. 72 |
| Serious incident reporting (within 15 days) | Art. 73 |

**Timeline cost:** Conformity assessment typically 3-6 months for self-assessment, 6-12 months when Notified Body involvement required.

#### 🟡 Tier 3: Limited-Risk (Article 50, 52)

Transparency obligations:

- **Chatbots:** users must be informed they are interacting with AI (Art. 50(1))
- **Deepfakes / AI-generated content:** must be marked as AI-generated (Art. 50(2))
- **Emotion recognition / biometric categorization** (outside Annex III): user notice required
- **General-purpose AI models:** model cards documenting capabilities, limitations, training-data summary (Art. 53)

#### 🟢 Tier 4: Minimal-Risk

No specific obligations. Voluntary codes of conduct recommended (e.g., transparency, model cards). Most B2B SaaS internal AI falls here (recommendation systems, spam filters, productivity assistants).

### General-Purpose AI Models (Article 51–55)

If you build a general-purpose AI model (foundation model), additional obligations apply:
- Technical documentation
- Information to downstream providers
- Training-data summary
- Compliance with EU copyright (especially text-and-data-mining opt-outs)

If your model is "systemic risk" (training compute > 10^25 FLOP, currently includes GPT-4, Claude, Gemini, Llama 3.1 405B+):
- Model evaluation
- Systemic risk assessment + mitigation
- Cybersecurity protections
- Serious incident reporting

## NIST AI Risk Management Framework (AI RMF 1.0)

US voluntary framework, increasingly referenced in B2B contracts and federal procurement.

**Four functions:**

1. **GOVERN** — Policy, roles, accountability, oversight
2. **MAP** — Context, impact assessment, stakeholders
3. **MEASURE** — Quantify, monitor, evaluate trustworthiness
4. **MANAGE** — Treat, prioritize, monitor risks

**Trustworthy characteristics:**
- Valid and reliable
- Safe
- Secure and resilient
- Accountable and transparent
- Explainable and interpretable
- Privacy-enhanced
- Fair with harmful bias managed

**Why it matters:** even outside government contracts, NIST AI RMF compliance is increasingly demanded by enterprise customers in security questionnaires (2025–2026 trend).

## US State Patchwork

### NYC Local Law 144 (Automated Employment Decision Tools)

- **Trigger:** AI/algorithmic decision-making in hiring or promotion for NYC-based employees
- **Obligations:** Annual independent bias audit (with EEO-1 categories); candidate notice 10+ business days before use; publication of audit summary on company website
- **Penalty:** $375-$1,500 per violation per day
- **Citation:** NYC Local Law 144 of 2021; 6 RCNY § 5-300

### Colorado AI Act (SB 21-169 and 2024 amendments)

- **Trigger:** High-risk AI in consumer-impacting decisions (employment, credit, insurance, healthcare, housing, government services, legal services)
- **Obligations:** Reasonable care to protect from algorithmic discrimination; annual impact assessment; consumer notice when used; right to appeal; comprehensive risk management policy
- **Effective:** February 2026
- **Citation:** Colorado SB 21-169; CRS § 6-1-1701 et seq.

### Illinois (multiple laws)

- **HB 53 (AI Video Interview Act):** Candidate notice + consent before AI analyzes video interview; explanation of how AI is used; deletion within 30 days of request. (820 ILCS 42/)
- **HB 3773 (AI hiring 2024):** Bans AI use in employment decisions that "tends to" discriminate based on protected class
- **BIPA (740 ILCS 14/):** Written informed consent for biometric capture; statutory damages $1K-$5K per violation; private right of action (massive class action exposure)

### California

- **SB 1001 (B.O.T. Act):** Bot disclosure in commercial transactions and CA elections
- **AB 2013 (2024):** Training-data transparency for generative AI providers
- **AB 1008 (2024):** AI-generated content disclosure in elections
- **CCPA / CPRA:** Right to know about automated decision-making; opt-out rights (CCPA § 1798.140 et seq.)

### Texas (BIPA-equivalent)

- Capture-of-biometric-identifier rules (Texas Business & Commerce Code § 503.001)

### Washington

- My Health My Data Act: consumer health data including AI-inferred health attributes (RCW 19.373)

## Industry-Specific Overlays

### Healthcare

- **FDA AI/ML guidance (2023, updated 2024):** Software as Medical Device (SaMD) classification; Predetermined Change Control Plan for adaptive models; Good Machine Learning Practices (GMLP)
- **Regulatory pathways:** 510(k), De Novo, or PMA depending on risk class
- **EU MDR + IVDR:** Medical-device AI deployed in EU requires CE marking + Notified Body (most cases)
- **HIPAA:** Patient data + AI → BAA + Limited Data Set rules

### Financial Services

- **CFPB Circular 2023-03:** Adverse action notices for AI-driven credit decisions must give specific reasons, not "the algorithm said no"
- **Fed SR 11-7 (model risk management):** Applies if you're a bank; influences vendor expectations
- **NYDFS Reg 23 (cybersecurity):** AI systems in financial services require risk assessment + governance
- **SEC AI rule proposal (2023, ongoing):** Investment adviser conflicts-of-interest disclosure for AI predictive analytics
- **ECOA (15 USC §1691):** Anti-discrimination in credit; applies to AI-driven underwriting

### Insurance

- **NAIC Model Bulletin on AI (2023):** AI governance, risk management, third-party AI oversight; state insurance commissioners are adopting variants
- **NY Insurance Reg 187:** Consumer-facing AI in insurance must not discriminate

### Critical Infrastructure / Defense

- **CISA AI Roadmap (2024):** Guidance for AI in critical infrastructure
- **DoD AI Ethical Principles (2020):** Responsible, equitable, traceable, reliable, governable
- **ITAR / EAR:** Some AI capabilities are export-controlled

## Governance Program Checklist

For any organization with > 1 production AI use case, build a governance program with:

1. **AI inventory** — every model in production, owner, use case, risk tier
2. **Risk classification** — every use case classified under EU AI Act + applicable US laws
3. **Eval sets** — every model has documented success criteria
4. **Monitoring** — drift, bias, performance, incident detection
5. **Incident response** — runbook for AI failures (e.g., hallucination in customer-facing output)
6. **Documentation** — model cards, training-data provenance, decision logs
7. **Human oversight** — escalation paths, override mechanisms
8. **Vendor / third-party AI oversight** — DPAs, model cards from providers, contract clauses for AI use
9. **Bias audits** — annual for high-risk; on-demand otherwise
10. **Compliance updates** — quarterly regulatory horizon scan

## When to Hire an AI Counsel

| Stage | AI legal need |
|---|---|
| Pre-seed / seed | None (general counsel covers basics) |
| Series A | Outside AI counsel ad-hoc for high-risk use cases or EU launch |
| Series B | Fractional AI counsel ($10-20K/mo) if regulated industry or EU customers |
| Series C+ | Full-time AI counsel if regulated industry, government customers, or multi-jurisdiction AI |

**Signs you need AI counsel:**
- About to launch in EU with a high-risk use case
- Enterprise customer is asking for AI governance documentation
- Regulator inquiry received
- Building general-purpose AI model (foundation model)
- AI failure caused customer harm

## When This Reference Doesn't Help

- **Specific contract language for AI vendor agreements.** See `general-counsel-advisor/references/contracts_playbook.md`.
- **GDPR data subject rights for AI.** Overlaps; see GDPR Art. 22 specifically.
- **Tactical bias audit implementation.** See `engineering/self-eval/`.
- **Tactical AI safety techniques (red teaming, adversarial testing).** See `engineering/agent-designer/`.

This reference is about strategic risk classification and governance program design, not tactical implementation.

---

**Source authorities (non-exhaustive):**

- EU AI Act: Regulation (EU) 2024/1689 of the European Parliament and of the Council (12 July 2024)
- NIST AI RMF 1.0: "Artificial Intelligence Risk Management Framework" (January 2023) + AI RMF Playbook
- NYC Local Law 144 of 2021; 6 RCNY § 5-300
- Colorado AI Act, SB 21-169 and 2024 amendments; CRS § 6-1-1701
- Illinois HB 53 (820 ILCS 42/); BIPA (740 ILCS 14/); HB 3773 (2024)
- California SB 1001 (Business & Professions Code § 17940); AB 2013 (2024); CCPA/CPRA
- CFPB Circular 2023-03 (adverse action notices)
- Federal Reserve SR 11-7 (model risk management)
- FDA "Marketing Submission Recommendations for a Predetermined Change Control Plan for AI/ML-Enabled Device Software Functions" (2024)
- NAIC Model Bulletin on the Use of AI by Insurers (2023)
- EDPB Opinion 28/2024 on processing personal data in AI models
- White House Executive Order on Safe, Secure, and Trustworthy AI (EO 14110, 2023) — rescinded 2025; subsequent EOs vary
- "On the Dangers of Stochastic Parrots: Can Language Models Be Too Big? 🦜" Bender, Gebru, et al. (2021)
- "Constitutional AI: Harmlessness from AI Feedback" Bai et al., Anthropic (2022)
