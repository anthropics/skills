# Trade Secrets for Technology Companies

## Federal Framework: Defend Trade Secrets Act (DTSA)

The **Defend Trade Secrets Act of 2016** (18 U.S.C. §§ 1831–1839) created a federal civil cause of action for trade secret misappropriation. It supplements, but does not preempt, state laws (most states follow the Uniform Trade Secrets Act, UTSA).

### What Qualifies as a Trade Secret

A trade secret must satisfy two requirements under DTSA (18 U.S.C. § 1839(3)):

**1. Information with independent economic value from secrecy**
- Derives actual or potential economic value from not being generally known or readily ascertainable through proper means
- The information would have value to competitors if known

**2. Subject to reasonable measures to maintain secrecy**
- The owner must take affirmative steps to protect the secret
- "Reasonable measures" is a fact-specific standard — courts look at the totality of circumstances

**What constitutes a trade secret in tech**:
- Source code and proprietary algorithms
- Machine learning model weights and architectures
- Training datasets and data curation methodologies
- Hyperparameter configurations and training recipes
- Customer data, usage patterns, and behavioral analytics
- Business methods and internal processes
- Pricing algorithms and financial models
- Hardware designs and chip architectures
- API designs before public release
- Competitive intelligence and strategic plans

### What Misappropriation Means

Misappropriation under DTSA includes:
- Acquisition by improper means (theft, bribery, espionage, breach of duty)
- Disclosure or use of a trade secret knowing it was acquired through improper means
- Disclosure or use in breach of a duty to maintain secrecy

Proper means of acquiring trade secrets (NOT misappropriation):
- Independent development
- Reverse engineering (if the product was legitimately acquired)
- Public domain discovery

## Reasonable Measures: What Courts Require

Courts have increasingly held that **passwords alone are insufficient** to establish reasonable measures. A March 2025 federal court decision determined that restricting access through firewalls, usernames, and passwords is insufficient without **explicit contractual protections**.

**Required reasonable measures for tech companies**:

1. **NDAs with all employees and contractors** (signed before access to confidential information)
2. **Invention Assignment / PIIA agreements** with all employees and contractors
3. **Access controls**: Role-based access, least-privilege principle, logging and auditing
4. **Physical security**: Locked server rooms, visitor policies, badge access
5. **Employee training**: Onboarding training on confidentiality obligations; annual reminders
6. **Marking confidential information**: Label sensitive documents, code repositories, and data as "Confidential" or "Trade Secret"
7. **Exit procedures**: Revoking access immediately on termination, exit interviews covering IP obligations, certificate of compliance
8. **Vendor agreements**: Require confidentiality from all vendors, customers, and partners with access
9. **DTSA whistleblower immunity notice**: Required in ALL contracts governing use of trade secrets (see below)

**DTSA whistleblower notice (CRITICAL)**: The DTSA requires notice of whistleblower immunity in any contract governing use of a trade secret. Failure to include this notice **eliminates eligibility for exemplary (double) damages and attorney's fees** in a subsequent DTSA lawsuit. Standard language: "An individual shall not be held criminally or civilly liable under any federal or state trade secret law for the disclosure of a trade secret that (A) is made in confidence to a federal, state, or local government official, either directly or indirectly, or to an attorney, and solely for the purpose of reporting or investigating a suspected violation of law..."

## NDA Structures for Tech Startups

### Mutual NDA (MNDA)
Used when both parties share confidential information (e.g., partnership discussions, co-development). Each party receives and owes confidentiality obligations.

Key provisions:
- **Definition of Confidential Information**: Broad — technical, financial, business, customer data; specify that orally disclosed information confirmed in writing within 30 days is covered
- **Exclusions**: Standard carve-outs for information that is publicly known, independently developed, received from a third party without restriction, or required to be disclosed by law
- **Non-use obligation**: Explicitly state that confidential information may only be used for the stated purpose
- **Term**: 2–5 years for the NDA itself; confidentiality obligation for trade secrets should survive indefinitely or for the life of the trade secret
- **Return/destruction**: Require return or certified destruction of confidential materials on request
- **No license**: Explicitly state the NDA does not grant a license to use the confidential information for any other purpose

### One-Way NDA (OW-NDA)
Used for one-directional disclosures (e.g., to a vendor, advisor, or potential investor who receives your information but discloses nothing).

### Employee Confidentiality Agreements
Always part of a broader **PIIA (Proprietary Information and Inventions Agreement)** — see references/ip-ownership.md. Should cover:
- All company confidential information during and after employment
- No carve-outs for "general skills and knowledge" (legitimate carve-outs exist but should be narrow)
- Return of company property on termination
- DTSA immunity notice (required)

## AI Models and Datasets as Trade Secrets

**Model weights**: Model weights (the trained parameters of an ML model) can be trade secrets. They have significant economic value (cost millions to train), are not publicly known (if kept private), and can be protected by reasonable measures. Unlike patents, trade secret protection on model weights never expires.

**Training datasets**: The composition, curation, and labeling of training datasets can be trade secrets. Who's in the dataset, how it was filtered, what quality thresholds were applied — these are valuable competitive advantages.

**Training methodology**: Hyperparameter schedules, learning rate strategies, data augmentation techniques, RLHF reward model details — all protectable as trade secrets.

**Practical protection strategy for AI startups**:
1. Never reveal model architecture details beyond what is disclosed in research papers
2. Keep weights and training checkpoints in access-controlled storage (separate from general code repos)
3. Use model API access (not model download) for commercial products where possible
4. Include trade secret protections in API terms of service (prohibit model extraction/distillation)
5. Log all access to model weights and training infrastructure

**AI-generated trade secrets**: If an AI system generates something with trade secret value, the human/company directing that AI system owns the trade secret (analogous to employer owning employee-created trade secrets). Contract law, not statutory inventorship rules, governs.

## Key 2024-2025 Trade Secret Developments

**Motorola v. Hytera (7th Cir. 2024)**: DTSA permits recovery of **worldwide damages** caused by misappropriation when at least one act in furtherance occurred in the US. Significant expansion of DTSA reach for international cases.

**Insulet v. EOFlow (D. Mass. 2024)**: $452M jury award ($59.4M after court reduction) for trade secret misappropriation of medical device designs — shows potential scale of DTSA damages.

**Password-only security insufficient (2025)**: Federal courts clarifying that mere password protection without NDAs and other measures fails the "reasonable measures" standard.

## Non-Compete and Non-Solicitation Clauses

### FTC Non-Compete Rule — DEAD (as of September 2025)
The FTC's April 2024 rule banning nearly all non-compete agreements for employees was enjoined by federal courts in Texas and Florida. The FTC voluntarily dismissed its appeal in September 2025. **The federal non-compete ban is no longer in effect.**

### State Law Governs — Wide Variation

**California (strongest ban)**:
- Business and Professions Code § 16600 prohibits non-compete agreements for employees
- SB 699 (effective January 1, 2024) — **illegal for employers to even ask employees to sign non-competes**, including attempting to enforce out-of-state non-competes against California employees
- Choice-of-law clauses do not override California's prohibition

**Other ban/near-ban states**: Minnesota (total ban since 2023), North Dakota, Oklahoma

**Moderate restrictions**: Washington, Oregon, Illinois, Virginia, Colorado — require non-competes to be limited in duration (typically 1 year max), reasonable in scope, and compensated

**Enforcement-friendly states**: Texas, Florida, Georgia, Virginia (with proper drafting) — still allow broader non-competes

### Non-Solicitation of Employees and Customers
Non-solicitation clauses (prohibiting former employees from soliciting company's employees or customers) are treated differently from non-competes. They are:
- Generally enforceable in most states (including California, with limitations)
- California courts increasingly scrutinize broad non-solicitation of employees clauses
- Must be narrowly tailored to be enforceable — protect specific customer relationships, not all business relationships

**Trade secret protection vs. non-compete**: In California and other ban states, trade secret law (DTSA + state UTSA) is the primary tool to prevent competitive harm from employee departures. Ensure robust PIIA agreements capture all relevant trade secrets in writing.
