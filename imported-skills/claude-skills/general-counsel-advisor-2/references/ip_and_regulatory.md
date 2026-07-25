# IP Strategy & Regulatory Landscape

The two areas where startups most often discover legal exposure after it's too late to fix cheaply: IP ownership and regulatory triggers. **Not legal advice.**

## Part 1: IP Strategy

### IP Inventory — The Four Categories

| Type | What it protects | How you get it | How you lose it |
|---|---|---|---|
| **Patents** | Inventions (novel, non-obvious, useful) | File application | Public disclosure > 12 months before filing |
| **Copyright** | Original works of authorship (code, content, designs) | Automatic on fixation | Almost never; can be assigned away |
| **Trademark** | Brand identifiers (names, logos, slogans) | Use in commerce + registration | Not policing infringement; becoming generic |
| **Trade secret** | Confidential business information | Reasonable measures to keep secret | Public disclosure; failure to maintain confidentiality |

### Invention Assignment — The Single Most Important IP Practice

**Rule:** Every person who touches the company's product or systems must sign an invention assignment agreement **before** they start work.

This includes:
- Co-founders (often forgotten — usually fixed via founder restricted-stock purchase agreements)
- Employees (in employment agreement)
- Contractors (in contractor agreement; NOT automatic in US law)
- Interns (often forgotten — use a short standalone IP agreement)
- Advisors (in advisor agreement, scope limited to inventions related to company)

**Why it matters:** Without written assignment, the creator retains ownership. A contractor who built a critical service for 6 months and never signed an assignment can come back years later and demand a license — or assert that competitors can also use what they built.

**The "previously created inventions" exhibit:** Every IP assignment should include an exhibit where the signer lists pre-existing inventions they want to exclude. This protects everyone — the signer's prior work isn't accidentally assigned, and the company has documentation of what came in.

### Open Source License Compliance

**Permissive licenses** (MIT, Apache 2.0, BSD 2/3): Use freely, attribute, no copyleft.

**Weak copyleft** (LGPL, MPL): Can use in proprietary product; modifications to the OSS itself must be released. Distribution model matters.

**Strong copyleft** (GPL v2, GPL v3, AGPL): Distribution / SaaS use of a strong-copyleft component can require releasing your derivative work under the same license. **AGPL is the most aggressive** — it applies even when you only run the software on a server (SaaS / network use).

**Practice:**

1. Maintain an OSS inventory: `pip-licenses`, `license-checker` (npm), `cargo-license`, `go-licenses`.
2. Identify any GPL / AGPL / SSPL dependencies.
3. For each: either (a) comply with the license, (b) replace with a permissively-licensed alternative, or (c) document the carve-out (some companies build internally with GPL but only ship the binary externally — verify with counsel).
4. Run the inventory before any due diligence (acquisition, financing).

### Patents — When to File

**File when:**

- You have a genuinely novel technical invention (algorithm, hardware design, materials, biotech process).
- You face well-funded competitors who could copy without consequence.
- You're in a patent-dense industry (semiconductors, pharma, networking, medical devices).
- Filing strengthens fundraising / acquisition optics (limited weight for software-only startups).

**Don't bother when:**

- Your "invention" is a UX flow or business method (these are extremely hard to patent post-Alice Corp).
- You're in early stage with limited capital and no competitors close enough to copy.
- Defensive only and joining a patent pool (LOT Network, OIN) might be cheaper.

**Process:**

1. **Provisional patent** ($300-500 USPTO fee + $3K-5K attorney). 12 months to file non-provisional.
2. **Non-provisional / utility patent** ($1K USPTO fee + $10K-15K attorney + prosecution costs).
3. **PCT application** for international filings ($5K-10K).
4. **National phase entries** in each country you care about ($5K-15K per country).

Budget $25K-50K total for one well-prosecuted patent family with international coverage.

### Trade Secrets

**Reasonable measures required for legal protection:**

- NDA / confidentiality clauses with everyone who has access.
- Access controls (need-to-know basis, not company-wide).
- Marking documents "Confidential."
- Departure procedures (return of materials, exit interview, deactivation).
- Training employees on what's a trade secret.

**Without these measures, the information may not qualify for trade secret protection if disclosed — even by a thief.**

**Common trade secrets:**

- Customer lists with usage / pricing data
- Algorithms not disclosed in published patents
- Manufacturing processes
- Sales playbooks and pricing models
- Internal financial projections
- Source code (unless OSS)

### Trademark Strategy

**Search before launch:**

- USPTO TESS search (free, but limited; doesn't catch common-law marks).
- Professional search via attorney ($500-2K) catches common-law marks and similar-mark conflicts.
- International searches via WIPO Global Brand Database.

**Register early:**

- US: Intent-to-use application (1B) lets you reserve a mark before launch.
- International: Madrid Protocol filing extends to 100+ countries.
- Word marks first (the brand name itself), design marks second (logos).

**Policing:**

- Set up Google Alerts and USPTO TMNG for your mark.
- Send cease-and-desist letters promptly; failure to police can weaken the mark.

---

## Part 2: Regulatory Landscape — When to Engage Counsel

The startups that survive their first regulatory encounter engage specialist counsel **before** building, not after. The ones that don't usually pivot, retreat, or pay heavy fines.

### Trigger Matrix

| Trigger | Regulatory Regime | Specialist Needed | Earliest Action |
|---|---|---|---|
| Healthcare data (patient records, claims, PHI) | HIPAA, HITECH, state breach laws | Health-tech attorney | Business Associate Agreement, OCR-aligned risk assessment |
| Cardholder data | PCI DSS (industry standard; contractually required) | QSA + counsel | Scope reduction, tokenization, certified processor |
| Money movement (transmitting funds, custody, crypto) | BSA/AML, state money-transmitter (50-state patchwork) | Fintech attorney | Stripe Treasury / Banking as a Service to avoid MT registration |
| Lending | Truth in Lending Act, state usury laws, ECOA | Fintech / consumer-finance attorney | Bank partnership, state licensing analysis |
| Medical device claims | FDA 510(k), De Novo, PMA; EU MDR; ISO 13485 | Medical-device regulatory specialist | Pre-submission meeting with FDA |
| EU residents' personal data | GDPR + ePrivacy + EU AI Act if AI | EU privacy attorney | DPA, SCCs for international transfer, DPIA |
| California residents | CCPA / CPRA | Privacy generalist | Privacy notice, opt-out mechanisms, vendor management |
| Children's data (under 13 US, under 16 in some EU states) | COPPA, GDPR-K | Privacy attorney | Parental consent, no-track defaults |
| Securities (tokens, equity crowdfunding, advisory boards) | SEC rules (Reg D, Reg A+, Reg CF, Howey test) | Securities attorney | Token sale legal opinion, Form D filing |
| Defense / aerospace customers | ITAR, EAR, DFARS, CMMC | Export-control attorney | Export classification, registered with State Dept |
| AI in EU | EU AI Act (risk-tiered: prohibited / high-risk / limited / minimal) | EU privacy + product attorney | Risk assessment, conformity assessment for high-risk |
| AI for hiring | NYC Local Law 144, CO SB 21-169, IL HB 53 | Employment attorney | Bias audit, candidate notice |
| Telehealth / online prescribing | State medical board rules, DEA registration for controlled substances | Telehealth specialist | State-by-state physician licensing strategy |
| Insurance (sale, underwriting, brokerage) | State insurance commissioners | Insurance attorney | State licensing, agency agreement |

### Sequencing: SOC 2 → ISO 27001 → Industry-Specific

For most B2B SaaS, the security/compliance sequence is:

1. **SOC 2 Type 1** (point-in-time audit) — ~$15K-25K, 3-6 months prep
2. **SOC 2 Type 2** (continuous, ~6-12 month audit window) — ~$25K-50K
3. **ISO 27001** if expanding internationally — ~$30K-60K, builds on SOC 2 controls
4. **ISO 42001** if AI is core to product — first AI management system standard
5. **Industry overlays:** HIPAA technical safeguards, FedRAMP (federal customers), PCI DSS (cardholder data)

**Sequencing logic:** SOC 2 unlocks the majority of enterprise sales. ISO 27001 unlocks European and Asia-Pacific. Industry overlays are required for specific verticals.

### When to Get a General Counsel Hire

| Stage | GC need |
|---|---|
| Pre-seed / seed | None. Use outside counsel ad-hoc + Clerky/Stripe Atlas templates |
| Series A | Fractional GC (~$10-20K/month) OR senior associate at firm |
| Series B | Full-time GC if regulated industry, customer contracts are heavy, or fundraising is constant |
| Series C+ | Full-time GC + Deputy/Associate GC if international |

**Signs you need a GC hire:**

- You're spending > $200K/year on outside counsel
- You're signing > 1 enterprise contract per week with customer redlines
- You're in a regulated industry (healthcare, fintech, defense)
- You're preparing for IPO or going-public transaction
- You're acquiring companies

### Cross-Border Considerations

**Hiring international employees:**

- Use Deel / Remote / Velocity Global for first 1-5 contractors per country.
- Establish an entity (subsidiary or EOR-to-entity transition) at 5-10+ employees.
- Tax residency, permanent establishment risk, and equity grants vary significantly.

**International data flows:**

- EU → US: SCCs + Transfer Impact Assessment (TIA); DPF if certified.
- China → outbound: PIPL approval + standard contract + security assessment.
- UK → outside: UK SCCs (similar to EU).
- Schrems / DPF status changes regularly — monitor with privacy counsel.

**International IP:**

- Patent: PCT application within 12 months of first national filing.
- Trademark: Madrid Protocol for multi-country filings.
- Copyright: Berne Convention covers most countries automatically.

---

## Closing: The General Counsel's Three Rules

1. **Get it in writing.** Verbal agreements and "we'll figure it out later" produce 80% of post-engagement disputes.
2. **Identify the regulatory trigger before you build.** It's 10x cheaper to design around a regulation than to retrofit.
3. **Always have outside counsel review anything binding.** This document is triage; real legal review is mandatory.
