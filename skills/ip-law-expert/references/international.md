# International IP for Technology Companies

## Patent Cooperation Treaty (PCT): International Patent Filing

The **Patent Cooperation Treaty (PCT)**, administered by WIPO, allows a single international patent application that preserves the right to seek patent protection in 155+ contracting states.

**PCT is not a single patent**: It is a procedural mechanism that delays the cost of filing in each country while preserving rights. Each national/regional patent office still examines and grants (or rejects) its own patent.

### PCT Process

**Phase 1: International Phase**

1. **File an international application** with the receiving office (USPTO for US applicants)
   - File within 12 months of your provisional or first national application (to claim priority)
   - Cost: ~$3,300–$5,000 in WIPO fees + attorney fees ($4,000–$10,000)

2. **International Search Report (ISR)**: WIPO's International Searching Authority (typically the EPO, USPTO, or JPO) conducts a prior art search and issues a Written Opinion on patentability
   - Typically issued 3–9 months after filing
   - Non-binding but extremely valuable for assessing patent prospects

3. **Publication**: Application published 18 months after priority date — **provides global "patent pending" notice**

4. **Chapter II (optional)**: Request International Preliminary Examination — additional search and opinion; can address examiner concerns before national phase entry

**Phase 2: National Phase (30 months from priority date)**

At 30 months from the earliest priority date, you must enter national phase in each desired country and pay national filing fees. This is when costs escalate dramatically:
- US national phase: ~$3,000–$8,000 in attorney fees (if PCT was filed; examination continues)
- EPO (covers 38 European countries): €4,000–€12,000 in fees + attorney fees; validation in individual countries after grant adds €500–€3,000 per country
- China (CNIPA): ~$2,000–$6,000
- Japan (JPO): ~$3,000–$7,000 + translation costs
- South Korea, India, Brazil, Canada, Australia, others: Each $2,000–$6,000+ separately

**Realistic total cost for filing in US + EU + China + Japan**: $60,000–$150,000 from provisional through prosecution and grant in all jurisdictions over 3-5 years.

### PCT Filing Strategy for Startups

**File the PCT at 12 months**: Use the 30-month window to assess commercial traction in international markets before committing national phase costs. Abandon countries where you won't have commercial activity.

**Prioritize by market and risk**: Enter national phase in countries where you have revenue, major competitors are based, or manufacturing occurs.

**Common national phase selections for tech startups**:
- Must: US (if not already filed), EPO, China
- Should: Japan, South Korea (if relevant tech sector)
- Situational: India, Brazil, Canada, Australia, Israel

### Expedited Examination

**USPTO PPH (Patent Prosecution Highway)**: If your PCT application receives a positive Written Opinion, you can file a PPH request at the USPTO for expedited examination (~6 months to first Office Action vs. 20+ months standard).

## European Patent Office (EPO)

**EPO Software Patent Standard**: "Technical character" — the invention must solve a technical problem by technical means. Pure mathematical methods, mental acts, and abstract business methods are excluded (EPC Article 52).

**In practice**: EPO is more software-patent-friendly than the US post-Alice. Software claims framed as improving computer functionality (reduced memory usage, faster processing, improved data transmission) regularly pass EPO examination. Business methods implemented in software that produce a technical effect are eligible.

**AI at the EPO**: EPO Guidelines for Examination (2025) Chapter II-2.3.6 explicitly addresses AI and ML:
- A "mathematical method" claim for an abstract ML algorithm is excluded
- BUT: If the ML method produces a technical effect (improved classification accuracy for a specific technical application, reduced computational load), the claim can be eligible
- "Functional" technical features (what the model does) are sufficient if they reflect a real technical effect

**EPO search quality**: EPO international searches (under PCT) are generally very thorough and provide the best indication of prior art globally. A positive EPO ISR is a strong signal of patentability.

**Post-grant in Europe**: An EPO patent must be "validated" in each individual country where protection is desired, with national translation requirements in some countries. The **Unitary Patent** (effective June 2023) allows a single patent covering 17+ EU member states — simplifying and reducing validation costs. UK requires separate validation (post-Brexit).

## China (CNIPA) — China National Intellectual Property Administration

**Why China matters**: China is the #1 PCT filer (70,160 applications in 2024 vs. US's 54,087). Domestic AI patent filing in China is massive. Any tech startup with China revenue or manufacturing exposure needs a China IP strategy.

**Chinese Patent System Basics**:
- Three types of patents: Invention patents (20 years), Utility Models (10 years — lower bar, no inventive step examination), Design Patents (15 years)
- Utility models are fast (typically 6-12 months to grant) and cheap — useful for manufacturing-related IP
- Invention patents take 2-4+ years

**AI at CNIPA (2024 Guidelines)**:
- CNIPA's "Guidelines for Patent Applications for AI-Related Inventions" (effective December 31, 2024) significantly clarified AI patent examination
- Standard: "Technical solution" — must solve technical problems using technical means following natural laws to achieve technical effects
- More permissive than US for AI drug discovery, industrial applications, and applied AI with measurable technical results
- Explicit guidance that neural network architecture innovations and training optimizations can be patentable if technical effects are specific

**China's first-to-file trademark system**: Unlike the US, China awards trademark rights to the first to file, not the first to use. Trademark squatting is rampant in China — competitors and professional squatters register well-known foreign brands. File in China immediately upon deciding to enter the Chinese market, even before launch.

**Enforcement in China**: Has improved significantly. Chinese courts actively enforce IP rights; foreign companies have won significant judgments. Anti-unfair competition law supplements trade secret law.

## Key Jurisdiction Comparison for Software/AI Patents

| Issue | US | EU (EPO) | China | 
|---|---|---|---|
| AI as inventor | No (Thaler v. Vidal) | No | No |
| Software patent eligibility standard | Alice/Mayo — "practical application" | "Technical character" | "Technical solution" |
| Abstract ML application | Ineligible post-Recentive | Potentially eligible if technical effect | Case-by-case; 2024 guidelines helpful |
| AI improving AI | Eligible | Eligible | Eligible |
| Typical prosecution time | 2-3 years | 3-5 years | 2-4 years |
| Business method software | Generally ineligible | Generally ineligible | Generally ineligible |
| Trade secret law | DTSA (federal) + state UTSA | Directive 2016/943 (EU Trade Secrets Directive) | Anti-Unfair Competition Law |

## EU AI Act — IP-Relevant Provisions

**Scope**: Applies to any provider placing an AI system on the EU market, regardless of where the provider is based.

**Copyright compliance obligations** (Article 53, effective August 2, 2025):
- GPAI model providers must implement a copyright policy
- Must honor text and data mining opt-outs under EU Copyright Directive 2019/790 Article 4(3)
- Must publish a "sufficiently detailed summary" of training content using the EU AI Office template
- Applies even if training occurred outside the EU

**Transparency obligations**: Technical documentation requirements for high-risk AI systems. GPAI models above computational thresholds (10^25 FLOPs for systemic risk models) face additional obligations.

**Penalties**: Up to €35M or 7% of global annual turnover for violations of prohibited AI practices; €15M or 3% for violations of other obligations.

**Implications for US AI startups with EU users**: The EU AI Act's copyright obligations are extraterritorial. US startups must ensure their AI training practices comply with EU copyright law if they operate in the EU market.

## UK — Post-Brexit

- UK is no longer covered by EU trademarks (EUTM) or EPO Unitary Patents (UK remains an EPO contracting state for validation of non-Unitary Patents)
- UK IPO issued its own AI and patents consultation — current position is that AI cannot be a named inventor (Thaler v. Comptroller-General, 2023 UK Supreme Court)
- UK Copyright Office: Similar to US — human authorship required for copyright
- Copyright law: "Computer-generated works" have a specific provision in UK copyright law (CDPA 1988 s.178) providing 50-year protection for works with no human author — unique to UK, not recognized in US or EU
- Data protection: UK GDPR (substantially mirrors EU GDPR post-Brexit)

## International Trade Secret Protection

**EU Trade Secrets Directive (2016/943)**: Harmonized minimum standards for trade secret protection across EU member states. Requirements similar to DTSA — economic value from secrecy + reasonable measures to maintain secrecy + misappropriation by improper means.

**China**: Anti-Unfair Competition Law (AUCL) protects trade secrets. Enforcement has improved significantly. Companies with China operations must execute Chinese-law NDAs and IP assignments with local employees.

**Cross-border misappropriation**: DTSA permits worldwide damages if at least one act in furtherance of the misappropriation occurred in the US (Motorola v. Hytera, 7th Cir. 2024). This significantly expands DTSA reach for cross-border trade secret theft.
