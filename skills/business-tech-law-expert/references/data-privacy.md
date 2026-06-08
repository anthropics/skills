# Data Privacy & Security Law Reference

## GDPR (EU General Data Protection Regulation)

**Legal basis**: Regulation (EU) 2016/679, effective May 25, 2018.
**Territorial scope**: Applies to any organization worldwide that:
- Has an establishment in the EU, OR
- Offers goods/services to EU/EEA residents (even for free), OR
- Monitors behavior of EU/EEA residents (e.g., tracking cookies, behavioral analytics)

**Key Definitions**
- **Personal data**: any information relating to an identified or identifiable natural person
- **Processing**: any operation on personal data (collection, storage, use, disclosure, deletion)
- **Controller**: determines purposes and means of processing
- **Processor**: processes data on behalf of controller
- **Data subject**: the individual whose data is processed

**Lawful Bases for Processing (Art. 6) — must have one:**
1. Consent (must be freely given, specific, informed, unambiguous, withdrawable)
2. Performance of a contract with the data subject
3. Compliance with legal obligation
4. Vital interests
5. Public task
6. Legitimate interests (controller's interests vs. data subject rights — balancing test)

**Special Categories (Art. 9) — require explicit consent or specific exemptions:**
Health data, genetic data, biometric data, racial/ethnic origin, political opinions, religious beliefs, sexual orientation, trade union membership, criminal convictions.

**Data Subject Rights**
- Right of access (Art. 15): within 1 month; must provide free copy of data; electronic format if requested
- Right to rectification (Art. 16)
- Right to erasure/"right to be forgotten" (Art. 17): must erase without undue delay in specific circumstances
- Right to restriction of processing (Art. 18)
- Right to data portability (Art. 20): machine-readable format
- Right to object (Art. 21): including to direct marketing (must honor immediately)
- Rights related to automated decision-making/profiling (Art. 22)

**Breach Notification (Art. 33/34)**
- To supervisory authority: within 72 hours of becoming aware (where feasible); if > 72 hours, include reasons for delay
- To data subjects: without undue delay if breach is "likely to result in high risk" to individuals
- Not required if data encrypted, anonymized, or risk mitigated
- Content: nature of breach, categories/numbers of individuals, DPO contact, likely consequences, measures taken

**Data Protection Officer (DPO) — Required When:**
- Core activities require large-scale systematic monitoring of individuals
- Core activities involve large-scale processing of special categories
- Public authority processing
- DPO must have expert knowledge of data protection law; can be external; cannot be conflicted

**Technical and Organizational Measures (Art. 32)**
- Encryption and pseudonymization
- Confidentiality, integrity, availability assurance
- Regular testing and evaluation
- Risk-appropriate measures

**Records of Processing Activities (Art. 30)**
Required for organizations with 250+ employees OR processing that is not occasional, involves special categories, or poses risk. Must document: purposes, categories of data/subjects, recipients, transfers, retention periods, security measures.

**Penalties**
- Tier 1: up to €10M or 2% of global annual turnover (whichever higher) — administrative requirements, consent, data subject rights
- Tier 2: up to €20M or 4% of global annual turnover (whichever higher) — core principles, lawful basis, special categories, international transfers

**Enforcement examples (relevant)**: Meta €1.2B (2023, data transfers), Amazon €746M (2021, cookie consent), WhatsApp €225M (2021, transparency), TikTok €345M (2023, children's data)

---

## CCPA/CPRA (California)

**Legal basis**: California Consumer Privacy Act (Cal. Civ. Code §1798.100 et seq.), amended by CPRA (Prop. 24); CPRA provisions effective Jan 1, 2023.
**Regulator**: California Privacy Protection Agency (CPPA) — independent agency with rulemaking and enforcement authority.

**Applicability threshold** (must meet ONE):
- Annual gross revenue > $26.6M (2025 inflation-adjusted threshold; originally $25M)
- Buys, sells, receives, or shares personal information of 100,000+ consumers or households per year
- Derives 50%+ of annual revenue from selling or sharing consumers' personal information

**Consumer Rights**
- Right to know: categories and specific pieces of PI collected, disclosed, sold, or shared
- Right to delete (with exceptions: legal obligations, complete transactions, research, etc.)
- Right to opt-out of "sale" or "sharing" of PI (including for cross-context behavioral advertising)
- Right to correct
- Right to limit use and disclosure of sensitive personal information
- Right to non-discrimination for exercising rights
- Verification required before honoring requests

**Sensitive Personal Information (SPI)** — new CPRA category:
Social security numbers, financial account credentials, precise geolocation, racial/ethnic origin, religious beliefs, sexual orientation, union membership, health/medical data, biometric data, genetic data, private communications.

**Cure Period**: eliminated as of January 1, 2025 — violations immediately subject to civil penalties.

**Penalties**
- Up to $2,500 per unintentional violation
- Up to $7,500 per intentional violation
- Up to $7,500 per violation involving a minor's data
- Private right of action: $100–$750 per consumer per incident for data breaches (or actual damages if higher)

**2025/2026 Regulatory Updates**: CPPA finalized regulations adding obligations around automated decision-making technology (ADMT), cybersecurity audits for companies posing significant risk, and risk assessments. Effective January 1, 2026.

---

## Other US State Privacy Laws

As of 2025, 21 states have enacted comprehensive privacy laws. Key ones:

| State | Law | Effective | Key Difference from CCPA |
|---|---|---|---|
| Virginia | VCDPA | Jan 1, 2023 | No private right of action; opt-out for profiling |
| Colorado | CPA | July 1, 2023 | Universal opt-out mechanism required |
| Connecticut | CTDPA | July 1, 2023 | 60-day cure period initially |
| Texas | TDPSA | July 1, 2024 | No revenue threshold; size-based |
| Montana | MCDPA | Oct 1, 2024 | Biometric data protections |
| Oregon | OCPA | July 1, 2024 | Nonprofit coverage |
| Iowa | ICDPA | Jan 1, 2025 | Narrower consumer rights |
| Indiana | INCDPA | Jan 1, 2026 | Moderate obligations |
| New Hampshire | NHPA | Jan 1, 2025 | Threshold: 35K+ residents |

**Compliance note**: A company subject to CCPA/CPRA that also complies fully with GDPR will typically satisfy most state law requirements — GDPR is the most demanding standard globally.

---

## HIPAA (Health Insurance Portability and Accountability Act)

**Key rules:**
1. **Privacy Rule** (45 CFR Part 164, Subparts A and E): governs use/disclosure of PHI; patients have rights to access, amend, restrict
2. **Security Rule** (45 CFR Part 164, Subparts A and C): administrative, physical, and technical safeguards for electronic PHI (ePHI)
3. **Breach Notification Rule** (45 CFR Part 164, Subpart D)

**Who is covered:**
- Covered entities: health plans, healthcare clearinghouses, healthcare providers that transmit PHI electronically
- Business Associates: entities that create, receive, maintain, or transmit PHI on behalf of covered entity

**PHI (Protected Health Information)**: individually identifiable health information in any form (electronic, paper, oral) created/received by covered entity or BA.

**18 HIPAA Identifiers**: name, address, dates, phone, fax, email, SSN, medical record #, health plan beneficiary #, account #, certificate/license #, vehicle identifiers, device identifiers, URLs, IP addresses, biometric identifiers, full-face photographs, any unique identifying number.

**Breach Notification Timeline:**
- BA to covered entity: within 60 days of discovery (best practice: 24–72 hours contractually in BAA)
- Covered entity to HHS + affected individuals: within 60 days of discovery
- If 500+ individuals in one state: contemporaneous media notification required
- If 500+ individuals affected: immediate HHS notification (< 500: annual HHS report by March 1)

**HIPAA Security Rule Safeguards (2025 NPRM)**:
HHS published most significant proposed changes since 2003 (Jan 6, 2025 NPRM):
- Remove "addressable" vs. "required" distinction (make all safeguards required)
- Mandatory encryption of all ePHI at rest and in transit
- Multi-factor authentication requirements
- Network segmentation required
- 72-hour restoration of critical systems after contingency

**Penalties**
- Tier 1 (did not know): $100–$50,000 per violation; $25,000/year max
- Tier 2 (reasonable cause): $1,000–$50,000 per violation; $100,000/year max
- Tier 3 (willful neglect, corrected): $10,000–$50,000 per violation; $250,000/year max
- Tier 4 (willful neglect, not corrected): $50,000 per violation; $1.5M/year max
- Criminal: up to 10 years imprisonment for knowing sale of PHI

---

## COPPA (Children's Online Privacy Protection Act)

**Scope**: Applies to commercial websites and online services (including apps) directed to children under 13, OR that have actual knowledge they're collecting data from children under 13.

**Requirements:**
- Verifiable parental consent before collecting personal information from children under 13
- Privacy notice describing data practices
- Parents' rights: review, delete, opt out of ongoing collection
- Reasonable data security
- Data retention limits — only as long as necessary for purpose collected

**Penalties**: up to $51,744 per violation (2025 adjusted amount). High-profile enforcement: Google/YouTube $136M (2019), Musical.ly/TikTok $5.7M (2019, later increased to $92M FTC settlement).

**Edge cases**: COPPA applies to mixed-audience services (e.g., YouTube's "made for kids" designation); age verification systems; services that "should know" they're reaching children.

---

## International Data Transfers

**EU Transfer Mechanisms:**
1. **Adequacy decision**: EC declares receiving country's laws adequate (UK, Japan, South Korea, Canada partial, US under EU-US DPF)
2. **Standard Contractual Clauses (SCCs)**: Most common for US companies. 2021 EU SCCs replaced old SCCs (completely invalid after Dec 2022). Must use module appropriate to relationship (controller-to-controller, controller-to-processor, etc.)
3. **Binding Corporate Rules (BCRs)**: multinational companies' internal data governance; requires DPA approval
4. **Derogations (Art. 49)**: explicit consent, contractual necessity, vital interests — limited use

**EU-US Data Privacy Framework (DPF)**: operational since July 2023; replaces Privacy Shield; self-certification through US Commerce Dept; challenges pending (Schrems III risk — Schrems II invalidated Privacy Shield in 2020). Companies should maintain SCCs as backup.

**Transfer Impact Assessment (TIA)**: Since Schrems II, must assess whether receiving country law undermines SCCs' protections. US-based companies receiving EU data must document TIA showing US surveillance law doesn't prevent compliance with SCC obligations.

**China Cross-Border Data Transfer:**
- Three mechanisms: security assessment (CAC mandatory for 1M+ individuals or sensitive data for 10K+/yr or critical information infrastructure); standard contract (for smaller transfers); certification by approved institution
- PIPL (Personal Information Protection Law): China's comprehensive privacy law, effective Nov 2021; extra-territorial scope similar to GDPR
- Localization requirements: operators of critical information infrastructure must store personal information and important data within China
