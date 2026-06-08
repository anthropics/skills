# AI Regulations Reference

## EU AI Act (Regulation (EU) 2024/1689)

**Enacted**: Official Journal of the EU, August 1, 2024. The world's first comprehensive AI law.

**Territorial scope**: Applies to:
- Providers placing AI systems on EU market or putting them into service in EU
- Deployers of AI systems in EU
- Providers and deployers of AI systems whose outputs are used in EU
- Importers and distributors of AI systems in EU
- Manufacturers integrating AI into their products for EU market

### Risk Tier Framework

**Tier 1: Unacceptable Risk (PROHIBITED)**
Banned practices effective February 2, 2025:
- Real-time remote biometric identification (RBI) in publicly accessible spaces for law enforcement (limited exceptions)
- Biometric categorization to infer race, political opinions, trade union membership, religious beliefs, sexual orientation, criminal history
- Social scoring systems by public authorities
- AI systems exploiting vulnerabilities (age, disability, social/economic situation) to manipulate behavior
- Subliminal techniques to manipulate behavior in ways that damage persons
- Emotion recognition in workplace and educational institutions (with limited exceptions)
- Untargeted scraping of facial images from internet/CCTV for facial recognition databases
- AI to predict criminal offending based on profiling

**Tier 2: High-Risk AI**
High-risk systems in Annex III (compliance by December 2, 2027):
- Biometric identification and categorization (non-prohibited uses)
- Critical infrastructure management (energy, water, transport, digital infrastructure)
- Educational and vocational training (student assessment, admission, exam monitoring)
- Employment and workers management (recruitment, selection, promotion, performance evaluation, termination)
- Essential private and public services (credit scoring, insurance risk, emergency services)
- Law enforcement (risk assessment, polygraph, crime analytics, evidence evaluation)
- Migration, asylum, border control
- Administration of justice and democratic processes
- Safety components of products covered by EU product safety legislation

High-risk AI in Annex I products (regulated products like medical devices, machinery): compliance by August 2, 2028.

**High-Risk Provider Obligations (Art. 9–16):**
- Risk management system: ongoing identification, analysis, evaluation of risks
- Data governance: training datasets must be relevant, representative, sufficiently free from errors and complete; document data collection, labeling, data gaps
- Technical documentation: detailed pre-market documentation (system purpose, architecture, training details, accuracy/robustness metrics)
- Record-keeping: automatic logging of events throughout system lifecycle
- Transparency and user information: clear instructions for use; identify known risks; disclose accuracy limitations
- Human oversight: design to enable human monitoring, intervention, override
- Accuracy, robustness, cybersecurity: maintain performance metrics; adversarial robustness testing
- Quality management system: written policies and procedures for compliance throughout lifecycle
- Conformity assessment: self-assessment or third-party depending on risk category
- Registration: in EU database before placing on market
- Post-market monitoring: collect and analyze real-world performance data

**Tier 3: Limited Risk (Transparency Obligations)**
Effective December 2, 2026:
- Chatbots/conversational AI: must inform users they are interacting with AI (not human)
- Deepfakes: AI-generated images, audio, video must be labeled as artificially generated
- Emotion recognition systems in customer service: disclosure required
- AI-generated text for public interest (news, PR): must disclose AI authorship

**Tier 4: Minimal/No Risk**
Spam filters, AI-recommended playlists, basic automation — no specific obligations.

### General Purpose AI (GPAI) Models

**Applies to**: providers of AI models trained on large amounts of data capable of competently performing a wide range of distinct tasks (GPT-4, Claude, Gemini class).

**Obligations for all GPAI providers (effective August 2, 2025):**
- Technical documentation
- Information for downstream providers (to comply with their own obligations)
- Copyright compliance policy
- Summary of training data (published online)

**Additional obligations for GPAI with "systemic risk"** (training compute > 10^25 FLOPs, or EC designation):
- Adversarial testing (red-teaming)
- Incident reporting to EC
- Cybersecurity protection
- Energy efficiency reporting

### Penalties
- Prohibited AI violations: up to €35M or 7% of global annual turnover
- High-risk/GPAI obligations: up to €15M or 3% of global annual turnover
- Incorrect/misleading information to authorities: up to €7.5M or 1% of global annual turnover
- SME/startup penalty floors lower than large company floors

### Implementation Timeline
| Date | Event |
|---|---|
| August 1, 2024 | Regulation enters into force |
| February 2, 2025 | Prohibited AI practices banned |
| August 2, 2025 | GPAI model obligations apply; AI Office established |
| December 2, 2026 | Transparency obligations for limited-risk AI |
| December 2, 2027 | High-risk Annex III AI compliance deadline |
| August 2, 2028 | High-risk Annex I (product-integrated) AI compliance |

---

## US Federal AI Regulation

**No comprehensive federal AI law** as of June 2026. Sector-specific agencies apply existing law:

**Executive Actions:**
- EO 14110 (Oct 2023, Biden): AI safety testing, reporting requirements for frontier models, agency-specific AI governance. Trump admin issued own EO revoking EO 14110 (Jan 2025) and focusing on AI leadership/innovation over precautionary regulation.
- AI Safety Institute (NIST): renamed in 2025; US AI Safety Institute (USAISI) coordinates voluntary safety testing.

**Agency-Specific Enforcement:**
- **FTC**: Section 5 (unfair or deceptive acts) applies to AI; guidance on AI-generated content disclosures; enforcement against deceptive AI claims (e.g., "AI can do X" false claims in marketing)
- **CFPB**: guidance that AI-based credit decisions must provide explanation under Equal Credit Opportunity Act (ECOA/Reg B); adverse action notices required
- **EEOC**: guidance that AI hiring tools may constitute employment discrimination if they have disparate impact on protected classes (Title VII)
- **FDA**: AI/ML in medical devices regulated as SaMD; Software as Medical Device Pre-Specifications (SaMD Pre-Specs) and Predetermined Change Control Plans
- **SEC**: guidance on AI disclosures in securities filings; proposed rules on AI conflicts of interest in investment advice (Investment Advisers Act)

**NIST AI Risk Management Framework (AI RMF 1.0)**
Released January 26, 2023. Voluntary but widely adopted.
Functions: **Govern** → **Map** → **Measure** → **Manage**
- Govern: establish AI risk policies, culture, accountability
- Map: categorize AI risks by context (technical, societal, organizational)
- Measure: analyze, assess, benchmark, evaluate AI risks
- Manage: prioritize, respond to, monitor AI risks

**NIST AI 600-1 (Generative AI Profile)**: specific guidance for GPAI systems; covers 12 risk areas including confabulation, data privacy, harmful bias, dangerous content, intellectual property, security vulnerabilities.

**NIST AI RMF Alignment with EU AI Act**: US companies using NIST RMF as governance baseline can map controls to EU AI Act high-risk requirements — not a complete substitute but strong foundation.

---

## US State AI Laws

**Colorado SB 205 (AI Act, effective February 1, 2026)**:
- Applies to developers and deployers of "high-risk AI systems" making consequential decisions in employment, education, financial services, healthcare, housing, insurance, legal services
- Obligations: risk management program, impact assessments, consumer notifications, opt-out rights, appeal mechanisms
- First US state law modeled on EU AI Act approach

**California AI laws:**
- AB 2013 (2024): disclosure requirements for AI training data
- SB 942 (2024): AI content detection provisions
- AB 1008 (2024): CCPA amendments addressing AI-generated data
- Multiple bills pending 2025–2026 legislative session

**New York Local Law 144**: mandatory bias audit for automated employment decision tools (AEDTs) used in NYC; annual third-party audit; disclosure to candidates. Effective July 2023.

**Texas SB 2488 (Responsible AI Governance Act, 2025)**: voluntary framework encouraging adoption of NIST AI RMF; state agency procurement requirements.

---

## AI Liability Framework

**Current US approach**: no AI-specific liability law; apply existing doctrines.

**Product Liability**: if AI system causes physical harm, manufacturer/deployer may face strict liability (for products) or negligence claims. Key issue: is AI output a "product" or a "service"?

**Professional Liability**: AI used in professional advice (legal, medical, financial) — professional may be liable for AI-assisted malpractice; AI vendor unlikely to bear professional liability.

**IP Liability**: see IP reference — training on copyrighted data; AI-generated outputs potentially infringing; Thaler v. Vidal held AI cannot be named as inventor.

**Discrimination Liability**: AI hiring, lending, or housing tools with disparate impact on protected classes violate existing discrimination law (Title VII, ECOA, FHA) — employer/lender liable even if no discriminatory intent.

**EU Product Liability Directive (2024/2853)**: modernized to cover AI; software (including AI) explicitly covered; reversal of burden of proof for complex products — claimant need only show defect and damage, not causation.

**Contract Allocation of AI Risk**: Limit AI liability in contracts; define AI outputs as "information" not professional advice; include human review requirements for consequential decisions; negotiate indemnification for IP infringement from AI training.
