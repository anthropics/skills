# Startup Contracts Reference

## Founder Agreements

### Equity Split and Vesting
- No legally mandated formula for equity splits; common approaches: equal split (simplest), contribution-weighted (accounts for idea, capital, experience), dynamic equity (Slicing Pie model).
- **Vesting**: almost universally 4-year vesting with 1-year cliff. After cliff, monthly vesting. Protects company if a co-founder leaves early. Unvested shares typically repurchasable at cost.
- **Acceleration**: single-trigger (acceleration on change of control alone) generally disfavored by acquirers; double-trigger (change of control + termination/constructive termination within 12–18 months) is market standard for executives.
- **Good Leaver/Bad Leaver provisions**: bad leaver (terminated for cause, voluntary resignation pre-cliff) — company repurchases unvested AND sometimes some vested at cost; good leaver (disability, death, termination without cause) — more favorable repurchase terms or acceleration.

### IP Assignment (PIIA — Proprietary Information and Inventions Agreement)
Every founder, employee, advisor, and contractor must sign a PIIA before contributing any work.

**Core PIIA provisions:**
1. **Invention assignment**: assigns to company all IP created during employment (and sometimes within 6–12 months after) that relates to company business or uses company resources
2. **Prior inventions carve-out**: schedule listing IP created before employment that is NOT assigned — must be listed at signing or it may be deemed assigned
3. **California Labor Code §2870 carve-out**: California employees cannot be required to assign IP created on own time, own resources, unrelated to company business, and unrelated to anticipated company business — PIIA must include this carve-out in California
4. **Confidentiality**: non-disclosure of trade secrets and confidential information (survives termination indefinitely for trade secrets, typically 2–5 years for confidential information)
5. **Non-solicitation**: typically 12 months post-employment; enforceable in most states
6. **Non-compete**: enforceable in most states (reasonableness test); void in California, Minnesota, North Dakota, Oklahoma; unenforceable for FTC rule purposes pending court challenge

**Due diligence note**: NVCA and most VCs require all founders and key employees to have signed PIIAs before any funding round closes. Missing PIIAs are a common deal-killer.

**Work-for-hire vs. assignment**: Copyright in works by employees created within scope of employment is automatically "work made for hire" under 17 U.S.C. §101. Patents are NOT automatically work-for-hire — assignment clause in PIIA is essential. Independent contractors' IP is NOT work-for-hire (unless specific categories + written agreement) — PIIA or separate IP assignment required for every contractor.

## SaaS Contract Architecture

A production SaaS agreement typically uses a layered structure:

```
Master Service Agreement (MSA)
  └── Order Form (specific deal terms)
  └── SaaS/Subscription Terms Addendum
  └── Data Processing Agreement (DPA)
  └── Acceptable Use Policy (AUP)
  └── Service Level Agreement (SLA)
  └── [If health data] Business Associate Agreement (BAA)
  └── [If government] Security Addendum / FedRAMP terms
```

### Master Service Agreement (MSA)
The umbrella contract. Covers:
- IP ownership (vendor retains software; customer retains data and content)
- Warranties (limited performance warranty + warranty disclaimer)
- Indemnification
- Limitation of liability
- Confidentiality
- Term and termination
- Governing law and dispute resolution

### Key Clauses (Expert Detail)

**Limitation of Liability (LOL)**
- Standard: aggregate liability capped at 12 months' fees paid in prior 12 months
- Enterprise negotiation: buyers push for "super-caps" for catastrophic events (data breach, IP infringement) — 2–3x fees or fixed dollar amount (e.g., $5M)
- Standard exceptions to the cap (mutual): (1) death/personal injury from negligence, (2) fraud, (3) willful misconduct, (4) indemnification obligations
- CONSEQUENTIAL DAMAGES DISCLAIMER: vendors disclaim lost profits, lost data, business interruption — customers fight to carve out data breach losses
- Watch for asymmetric caps: some vendor templates cap vendor liability but not customer liability

**Indemnification**
- Vendor indemnity: IP infringement of third parties' IP by the software (standard); some vendors exclude open source claims
- Customer indemnity: misuse of software in violation of AUP; breach of customer data input warranties
- Process: indemnitee must give prompt notice, tender control of defense, cooperate; indemnitor controls settlement (but cannot settle in ways that admit liability or impose obligations on indemnitee without consent)
- Enterprise buyers often push for vendor indemnity covering data breach costs — resist or limit with sub-cap

**Warranty**
- Express warranty: software will perform materially in accordance with documentation; vendor will maintain adequate security controls
- Vendor disclaims: implied warranties of merchantability, fitness for particular purpose, non-infringement (beyond the express IP indemnity), title (for open source components)
- SLA-based remedy: service credits as sole remedy for downtime (not damages)

**IP Ownership**
- Crystal clear: vendor owns the platform, code, models, improvements
- Customer owns: all customer data, configurations, outputs (if applicable), and customer's pre-existing IP
- License grant: vendor grants customer limited, non-exclusive, non-transferable license to use the service
- Output ownership for AI products: explicitly address ownership of AI-generated outputs — typically licensed to customer but vendor retains right to improve models using anonymized/aggregated data

**Data Ownership and Use**
- Customer data: customer retains all rights; vendor has limited license to operate service (process, store, display)
- AI training on customer data: highly negotiated — enterprise customers typically prohibit use of their data to train vendor's models; must be explicit in agreement
- Data portability: customer right to export data in machine-readable format; export available for X days after termination
- Data deletion: vendor commits to deleting customer data within 30–90 days of termination

**Confidentiality**
- Definition: non-public business information disclosed by either party
- Exceptions: public domain, independently developed, rightfully received from third party, required by law
- Return/destruction of confidential information upon termination
- Residuals clause: some vendors include a "residuals" exception allowing use of information retained in unaided memory of employees — fought by customers

### Data Processing Agreement (DPA)

Required by GDPR Art. 28 for any processor handling EU personal data on behalf of a controller.

**Required DPA provisions (GDPR Art. 28(3)):**
- Process only on documented instructions from controller
- Confidentiality obligations on all authorized processors
- Appropriate technical and organizational security measures (Art. 32)
- Sub-processor approval and flow-down obligations (controller must approve or have general authorization for categories of sub-processors)
- Data subject rights assistance (erasure, access, portability)
- Security assistance and breach notification (typically 48–72 hours to controller after becoming aware)
- Return/deletion of data at contract end
- Audit rights

**Sub-processor management**: vendor must maintain list of sub-processors; provide advance notice of changes; allow customer to object; ensure same obligations flow down.

**Standard Contractual Clauses (SCCs)**: must be incorporated or attached if transferring EU personal data to processors in non-adequate countries (including US — US–EU Data Privacy Framework exists but may face legal challenge).

### Business Associate Agreement (BAA)

Required under HIPAA for any Business Associate (entity that creates, receives, maintains, or transmits PHI on behalf of a covered entity).

**Required BAA provisions (45 CFR §164.504(e)):**
- Permitted uses and disclosures of PHI
- BA will not use or disclose PHI except as permitted
- BA will implement HIPAA-required safeguards
- BA will report breaches within 60 days of discovery (many BAAs set tighter internal timelines: 24–72 hours)
- BA will ensure sub-BAs are under equivalent obligations
- Return or destruction of PHI upon termination
- Government access for compliance reviews

### Acceptable Use Policy (AUP)
Prohibitions on: illegal activities, spam, malware, CSAM, doxxing, unauthorized data scraping, reverse engineering, benchmarking (check if permitted), mining competitor intelligence, circumventing usage limits.

### Service Level Agreement (SLA)
- Uptime commitment: 99.9% (8.76 hrs/yr downtime) is enterprise minimum; 99.95% or 99.99% for mission-critical
- Measurement: monthly uptime percentage; exclude scheduled maintenance
- Remedies: service credits (typically 5–25% of monthly fee per 0.1% below SLA)
- Response time SLAs for support tiers (P1: 1 hour, P2: 4 hours, P3: 1 business day)
- Sole remedy clause: service credits are the exclusive remedy for downtime (vendors protect against full contract value claims)

## Enterprise Contract Negotiation Framework

**Buyer-side priorities (in order):**
1. Uncapped or high-capped liability for data breaches
2. IP indemnification with no open source carve-out
3. Data deletion and portability on termination
4. Prohibition on AI training with customer data
5. Sub-processor approval rights
6. Audit rights (with reasonable notice)
7. Source code escrow for critical applications

**Vendor-side priorities:**
1. Cap liability at 12 months fees
2. Disclaim consequential damages broadly
3. Limit indemnification triggers
4. Retain right to improve product using aggregated/anonymized data
5. Define "confidential information" narrowly (exclude benchmark results)
6. Limit audit rights (questionnaire-based vs. on-site)

**Standard market positions (2025):**
- Liability cap: 12 months (vendor default) → 24 months (compromise) → higher for enterprise
- Security breach carve-out: increasingly standard to exclude or super-cap
- Data processing restriction for AI training: increasingly demanded by enterprise buyers
