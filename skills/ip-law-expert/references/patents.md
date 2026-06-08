# Patents — Software & AI for Tech Startups

## What is Patentable in Software (Post-Alice Landscape)

Software is patentable in the US, but the rules are complex. The governing statute is **35 U.S.C. § 101**, which allows patents for "any new and useful process, machine, manufacture, or composition of matter." However, abstract ideas, natural phenomena, and laws of nature are judicial exceptions.

### The Alice/Mayo Two-Step Test

All software/AI patent claims are evaluated under the **Alice Corp. v. CLS Bank International** (2014) framework, applied via the **USPTO's 2019 Revised Guidance** (updated July 2024):

**Step 1 (Threshold)**: Is the claim directed to a process, machine, manufacture, or composition of matter? (Virtually always yes for software.)

**Step 2A, Prong 1**: Is the claim directed to a judicial exception (abstract idea, natural phenomenon, law of nature)?
- Abstract ideas include: mathematical concepts, methods of organizing human activity, mental processes
- Software claims routinely implicate mathematical concepts and mental processes

**Step 2A, Prong 2**: Does the claim integrate the exception into a "practical application"?
- Key inquiry: Does the claim improve computer functionality itself, or merely use a computer as a tool to execute an abstract idea?
- Surviving examples: improved data compression, reduced network latency, novel error correction, specific database query optimization
- Failing examples: generic "apply it on a computer," using software to run a business process faster

**Step 2B (only if Step 2A fails)**: Does the claim provide an "inventive concept" significantly more than the exception alone?
- Must be more than "well-understood, routine, conventional" computer functions
- Generic hardware (processor, memory, network) does not save an abstract claim

### USPTO's July 2024 AI Guidance (Effective July 17, 2024)

The USPTO released updated guidance specific to AI inventions, including Examples 47, 48, and 49:
- **Example 47**: AI training method for anomaly detection — found eligible when the claims recited a specific technical improvement to the training process itself (faster convergence via novel gradient techniques)
- **Example 48**: AI-based audio processing — found ineligible when claims merely used AI to organize data without technical improvement
- **Example 49**: Personalized medical AI — found eligible when claims recited specific data processing techniques in a particular medical application context

The 2025 USPTO Memo (August 4, 2025) reaffirmed the 2024 Guidance. A 2025 precedential decision, **Ex parte Desjardins**, clarified that improvements to AI model performance (not just better outputs) can confer eligibility.

### What Software Patents Survive Alice

Eligible software claims typically:
- Improve computer/network performance (speed, security, efficiency, reliability)
- Enable something previously impossible or impractical computationally
- Recite specific technical steps, not generic "process data" instructions
- Identify a concrete technical problem and a specific technical solution
- Improve a particular technological field (e.g., data compression algorithms with measurable results)

Examples of patents that have survived: memory management optimizations, specific cryptographic protocols, novel network routing algorithms, improved data structure designs, specialized UI interactions solving a technical problem.

Examples that fail: using software to run financial transactions on generic hardware, using AI to recommend products (abstract idea with generic implementation), automating human scheduling processes.

## Patent Prosecution Process

### Step 1: Provisional Patent Application
- Establishes a priority date (not a patent — no examination occurs)
- Must file a non-provisional within **12 months** (deadline is absolute, non-extendable)
- Lower formality requirements — no claims required
- Less expensive: USPTO fee $65–$320 (micro/small/large entity) + attorney prep $1,500–$4,000
- Strategic value: "patent pending" status, buys 12 months to assess commercial viability
- Approximately 52–60% of provisionals convert to non-provisionals; remainder are abandoned strategically

**Key strategic use**: File a provisional before public disclosure, product launch, or investor presentations. Establishes your priority date globally (in PCT countries). Use the 12 months to test product-market fit, then decide whether to proceed.

**Critical caution**: A provisional that doesn't fully disclose the invention cannot support a later non-provisional's priority claim. Provisionals should be substantive, not just a page of notes.

### Step 2: Non-Provisional (Utility) Patent Application
- Formal patent application — begins examination
- Must include: specification, claims, abstract, drawings (if necessary)
- USPTO filing fee: $320–$1,760 (micro/small/large entity) for basic application
- Attorney preparation: $8,000–$18,000+ depending on complexity
- **First Office Action**: typically 14–22 months from filing (average ~19.9 months in FY2024; 22.6 months in FY2025)
- **Track One Prioritized Examination**: $1,000–$4,200 additional fee, targets 6–12 months to first Office Action

### Step 3: Office Action Responses
- Most applications receive at least one rejection (35 USC 102 — novelty, 35 USC 103 — obviousness, 35 USC 101 — eligibility)
- Response window: 3 months (extendable to 6 months with fees)
- Response attorney fees: $2,000–$6,000 per office action
- Typically 1–3 rounds of prosecution

### Step 4: Issuance
- Issue fee: $580–$1,200
- Average total pendency: 24–36 months from non-provisional filing

### Step 5: Maintenance Fees
- Due at 3.5, 7.5, and 11.5 years post-grant
- Fees: $800–$7,700 per payment (small/large entity) — total life cost $2,000–$20,000+
- Missing a maintenance fee results in patent expiration

## Total Cost Summary

| Stage | Estimated Cost (Small Entity) |
|---|---|
| Provisional patent (attorney-prepared) | $2,500–$5,000 |
| Non-provisional filing + prosecution | $12,000–$25,000 |
| Complex/multi-claim software patent | $20,000–$40,000+ |
| FTO opinion (freedom to operate) | $5,000–$30,000 |
| IPR petition (defense against troll) | $100,000–$400,000 |
| Full patent litigation (to verdict) | $3M–$10M+ |

## Patent vs. Trade Secret: Strategic Decision Framework

**Choose patents when:**
- The innovation is detectable in the product (reverse-engineerable)
- You need enforcement rights (ability to sue infringers, license)
- The product will be widely distributed
- Blocking competitors from using the technique is critical to your moat
- The invention has a finite development cycle (trade secrets become stale if key employees leave)

**Choose trade secrets when:**
- The innovation is not reverse-engineerable from the product (e.g., training data composition, model weights, proprietary datasets)
- You want indefinite protection (trade secrets don't expire; patents last 20 years from filing)
- You cannot afford $20,000+ per patent
- Disclosure in a patent would give competitors a roadmap
- The USPTO 101 eligibility risk is high (post-Alice/Recentive)

**The hybrid approach**: File a provisional to preserve the priority date. Use the 12-month pendency to assess commercial viability and patent-eligibility risk. Decide whether to convert or maintain as a trade secret. The abandoned provisional is never published — secrecy is preserved if you don't convert.

## Patent Claim Drafting Strategy for Software/AI

1. **Frame the problem as technical, not business**: "The prior art compression algorithm required 40% more memory due to X limitation" — not "customers wanted cheaper storage."

2. **Claim the specific technical solution**: Recite concrete steps — data structures, algorithms with specific parameters, hardware configurations, threshold values — not generic "processing data."

3. **Include a technical improvement statement**: Specifications should explicitly state the technical problem solved and measurable technical benefit achieved (latency reduction, accuracy improvement, memory reduction).

4. **Avoid purely functional claiming**: "Means for processing data" without specific technical structure fails Alice and 35 U.S.C. § 112.

5. **Multiple claim levels**: Independent claims for the broadest defensible scope. Dependent claims add specificity for fallback positions during prosecution.

6. **For AI-specific claims**: Focus on improvements to the training process, novel architectures, or new training data methodologies — not "use machine learning to do X." (See references/ai-patents.md.)

## Key Patent Statutes

- **35 U.S.C. § 101** — Patent-eligible subject matter
- **35 U.S.C. § 102** — Novelty requirement (no prior art)
- **35 U.S.C. § 103** — Non-obviousness requirement
- **35 U.S.C. § 112** — Written description and enablement
- **35 U.S.C. § 119** — Foreign priority (12-month window from first filing)
- **35 U.S.C. § 154** — 20-year patent term from filing date
- **35 U.S.C. § 311-319** — Inter Partes Review procedure
