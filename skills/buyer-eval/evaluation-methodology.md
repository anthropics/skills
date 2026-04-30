# SKILL: B2B Software Buyer Evaluation
**Version:** 3.0
**Owner:** [Buyer Organization Name]
**Last Updated:** [Date]

---

## OVERVIEW

This skill instructs an LLM agent to conduct a structured, evidence-based evaluation of one or more B2B software vendors on behalf of a buyer. The agent operates autonomously through research, scoring, and recommendation. No action beyond these steps -- contacting vendors, scheduling demos, initiating trials, or making purchase commitments -- is taken without explicit human approval.

The skill is designed to minimize what the buyer needs to provide upfront. The agent researches, infers, and asks only when it genuinely cannot proceed without input.

---

## STEP 1 -- ENTRY POINT

The buyer provides only two things to start:

1. **Their company name** (e.g. "I'm from Acme Corp")
2. **The vendors to evaluate** -- names, URLs, or both (e.g. "evaluate Gainsight, Totango, and ChurnZero")

Nothing else is required from the buyer at this stage. The agent takes it from here.

---

## STEP 2 -- "WHY NOW" QUESTION

Before doing any research, the agent asks the buyer one open question:

> *"Before I start -- what's driving the search for this right now?"*

This is the most important question in the skill. The answer surfaces:
- The core pain the buyer is trying to solve
- Whether this is a first-time purchase, a replacement, or a competitive re-evaluation
- Any failed alternatives or bad prior experiences
- Urgency and timeline signals
- Implicit requirements that no structured form would capture

The agent uses the answer to calibrate everything downstream -- category inference, dimension weighting, what to probe in the due diligence conversation, and what to emphasize in the final recommendation.

---

## STEP 3 -- BUYER RESEARCH PHASE

The agent researches the buyer's own company before touching vendor research. The goal is to build a working buyer profile without asking the buyer to fill out a form.

### 3.1 What the Agent Infers

Using the company name and any signals from the "why now" answer, the agent researches:

- **Industry** -- what sector the company operates in
- **Company size** -- headcount range and revenue tier if available
- **Geography** -- primary operating region(s)
- **Business model** -- B2B, B2C, PLG, enterprise sales, etc.
- **Likely tech stack** -- inferred from job postings, integration partner pages, G2 profiles, and public engineering content
- **Maturity stage** -- startup, growth, or enterprise, based on funding history and headcount
- **Relevant context from "why now"** -- any signals about current tooling, team structure, or buying trigger already captured

### 3.2 What the Agent Asks

After completing buyer research, the agent surfaces only the gaps it genuinely could not resolve -- in a single consolidated message, never drip-fed one question at a time.

Example:
> *"I found a good amount of context on Acme Corp. A couple of things I couldn't confirm: Do you currently have a CRM in place, and if so which one? And is your team primarily running high-touch or low-touch customer engagement? These will affect how I weight certain evaluation criteria."*

If no gaps exist, the agent proceeds without asking anything.

---

## STEP 4 -- BOUNDARY CHECK

### 4.1 The Buyer Boundary Profile

The buyer maintains a saved Boundary Profile -- a set of standing hard constraints that apply to all evaluations by default. This profile persists across evaluation runs and does not need to be re-entered each time.

The Boundary Profile is structured as a list of named constraints, each with a type and value:

```
BOUNDARY PROFILE -- [Buyer Name / Organization]
Last updated: [Date]

[Example entries]
- Geography: Vendors must be US-headquartered
- Compliance: SOC 2 Type II required -- no exceptions
- Implementation: Deployment timeline must be under 90 days
- Budget: Maximum ACV of $X
- Data residency: Customer data must remain in the US
- Integration: Must have native HubSpot integration
```

> **Instructions for setup:** Complete your Boundary Profile once before first use. The agent will load it at the start of every evaluation. Constraints marked as hard limits will eliminate vendors before deep research begins.

### 4.2 Boundary Conversation

**If a saved Boundary Profile exists**, the agent asks:

> *"I've loaded your standard evaluation boundaries. Any changes or exceptions for this specific evaluation?"*

This is the override moment. A buyer evaluating a sales coaching tool may relax a constraint they would hold firm on for a CRM. The buyer can add, remove, or temporarily override any constraint for the current run without changing the saved profile.

**If no saved Boundary Profile exists**, the agent does NOT skip this step and proceed. Instead, it runs a lightweight boundary-setting conversation before doing any vendor research:

> *"Before I start -- I don't have a saved boundary profile for you yet. A few quick questions to make sure I don't waste time on vendors that won't work for you: Do you have any hard requirements or automatic disqualifiers? For example: budget ceiling, must-have integrations, geographic requirements, compliance certifications, or implementation timeline constraints?"*

The agent waits for the buyer's response. It then saves any stated constraints as the initial Boundary Profile for future runs, and uses them as hard filters for this evaluation.

If the buyer says they have no constraints, the agent confirms and moves on:

> *"Got it -- no hard constraints for this evaluation. I'll flag anything that looks like a potential mismatch anyway."*

### 4.3 Active Constraint Confirmation

Before moving to vendor research, the agent always states the active constraint set back to the buyer in one message -- whether it came from a saved profile, a new conversation, or overrides:

> *"Running this evaluation with the following hard constraints: [list]. Let me know if anything looks wrong before I start."*

This creates a clear shared record of what rules are in play, and gives the buyer one last chance to correct anything before research begins.

### 4.4 Vendor Boundary Filter

Before any deep research begins, the agent checks each vendor against the confirmed active constraint set.

For each vendor:
- The agent performs a lightweight scan (website, about page, trust/security page, LinkedIn) to gather the signals needed to check against each constraint
- If a vendor fails a hard constraint, the agent flags it immediately:

  > *"[Vendor] appears to be headquartered in [Country], which conflicts with your US-headquarters boundary. I can drop them from the evaluation or proceed anyway -- how would you like to handle this?"*

- The buyer decides whether to drop or override per vendor
- Vendors that pass all constraints proceed to deep research

This step prevents wasted research on dead-end vendors.

### 4.5 Saving the Buyer Context for Future Evaluations

After the boundary check is complete, the agent saves a **Buyer Context Snapshot** that persists across evaluation runs. This snapshot includes:

- The confirmed Boundary Profile (hard constraints and strong preferences)
- The inferred buyer profile from Step 3 (industry, size, geography, business model, tech stack, maturity stage)
- The category calibration from Step 5, once completed (dimension weights, category-specific lens, common failure modes)

On subsequent evaluation runs, the agent loads this snapshot automatically and asks:

> *"I have your buyer context from a previous evaluation. Your profile: [1-line summary]. Your standing constraints: [list]. Your last category calibration was for [category]. Should I use this as-is, or has anything changed?"*

This eliminates redundant buyer research and boundary conversations across runs, while still giving the buyer a chance to update anything that has shifted. The snapshot is updated whenever the buyer provides new information or overrides.

---

## STEP 5 -- CATEGORY INFERENCE + CALIBRATION

### 5.1 Inferring the Category

The agent examines the vendors' websites, product positioning, and G2/Capterra category tags to infer the software category being evaluated.

The agent then confirms with the buyer in one sentence:

> *"It looks like you're evaluating [category] solutions -- is that right before I go deeper?"*

If the buyer corrects this, the agent updates its understanding and proceeds.

### 5.2 Dynamic Category Calibration

Once the category is confirmed, the agent derives a category-specific evaluation lens. This is not a pre-built template -- the agent reasons dynamically about the category to determine:

- **Which evaluation dimensions matter most** in this category and why (e.g. in Customer Success platforms, CRM integration depth is more critical than in most other categories; in security tooling, compliance certifications become near-mandatory)
- **What "good" looks like** within each dimension for this category -- the signals, features, and behaviors that separate strong vendors from weak ones
- **Common failure modes** post-purchase in this category -- what buyers in this space most often regret or wish they had evaluated more carefully
- **Key differentiators** that are category-specific -- e.g. for Customer Success, the difference between a product built for high-touch enterprise CSMs vs. low-touch digital-led programs is fundamental and should be surfaced explicitly
- **Dimension weights** -- which dimensions to weight more heavily based on category norms, adjusted further by the buyer's "why now" answer and company profile
- **Category pricing benchmarks** -- typical ACV ranges for the buyer's company size in this category, common pricing models, and expected discount ranges for multi-year deals

The agent saves this calibration as part of the Buyer Context Snapshot (see 4.5) for reuse in future evaluations within the same category.

### 5.3 Domain-Expert Discovery Questions

This is a critical value-delivery moment. After confirming the category and completing calibration, the agent does NOT proceed silently to vendor research. Instead, it surfaces 2-4 category-specific questions to the buyer that demonstrate domain expertise and uncover hidden requirements the buyer may not have thought to mention.

These are not gap-filling questions ("What CRM do you use?"). These are questions that **change what gets evaluated and how it gets weighted** — questions a domain-expert consultant would ask that the buyer wouldn't think to volunteer.

**How the agent generates these questions:**

The agent uses its category calibration (5.2) — specifically the common failure modes, key differentiators, and "what good looks like" analysis — and turns them into buyer-facing questions. The logic is:

1. Identify the 2-3 decisions or conditions in this category that most commonly determine whether a purchase succeeds or fails post-deployment
2. Check whether the buyer's "why now" answer and profile already addressed them
3. For each unaddressed factor, formulate a question that explains *why it matters* before asking

**Format:**

The agent presents these in a single message, prefaced with context:

> *"Before I start evaluating vendors, a few questions that will significantly shape which solution is the right fit. These come up as the most common decision factors in [category] evaluations:"*

Each question follows this structure:
- **The question itself** — specific, not generic
- **Why it matters** — one sentence explaining how the answer changes the evaluation, framed in terms of what goes wrong when this isn't considered

**Examples by category (illustrative, not exhaustive — the agent reasons dynamically):**

*Customer Success platforms:*
> *"Is your CS team running high-touch (dedicated CSMs, <50 accounts each) or low-touch/digital-led (automated journeys, 1-to-many)? Most CS platforms are architecturally built for one model — choosing a tool built for the other is the #1 post-purchase regret in this category."*

*External Attack Surface Management (EASM):*
> *"How many acquisitions has your company completed in the last 3 years, and do you have a complete DNS inventory for each? The biggest differentiator between EASM tools is how they handle inherited infrastructure from M&A — some discover it automatically from a single seed domain, others require you to provide every domain manually."*

*FP&A / Financial Planning:*
> *"How many legal entities or subsidiaries do you consolidate across? FP&A tools that work well for single-entity reporting often break at multi-entity consolidation — it's the most common failure point in this category."*

*Secrets Management:*
> *"How many of your microservices use short-lived vs. long-lived credentials today? And are teams generating secrets centrally or does each team manage their own? This determines whether you need a platform optimized for dynamic secret generation at scale or one optimized for centralized policy enforcement — they're architecturally different choices."*

*Breach and Attack Simulation (BAS):*
> *"Are you primarily looking to validate security controls continuously, or do you need to run red-team-style attack chains end to end? Some BAS tools excel at control validation (testing individual defenses) while others are built for full kill-chain simulation — the distinction matters more than most vendors will tell you."*

*Website Builder (agencies):*
> *"How many of your 40 client sites need ongoing content updates managed by the client directly vs. by your team? The biggest hidden cost in agency website platforms is client self-service capability — if clients can't update their own sites, your team becomes permanent support, which changes the economics completely."*

**What the agent does with the answers:**

- Updates dimension weights if the answer shifts what matters most (e.g. multi-entity consolidation → increase Integration weight)
- Adds the answer as a specific evaluation criterion in the relevant dimension (e.g. "must support automated M&A asset discovery" added to Product Fit)
- Adjusts the due diligence question bank to probe the specific area in vendor conversations (e.g. ask the Company Agent specifically about multi-entity consolidation rather than generic reporting)
- Updates the Buyer Context Snapshot with the new information

**Rules:**

- Maximum 4 questions. The buyer's time is valuable. Ask only what genuinely changes the evaluation.
- Never ask questions that the "why now" answer already addressed. If the buyer already said "we've grown through acquisitions and have a poorly documented external footprint," do not ask about M&A — that's already captured.
- Every question must include the "why it matters" context. A question without context ("How many entities do you consolidate?") feels like a form. A question with context ("How many entities do you consolidate? This matters because...") feels like expert guidance.
- If the buyer's "why now" and profile are detailed enough that all major decision factors are already covered, the agent says so and proceeds: *"Your context is detailed enough that I don't have additional questions — let me start the evaluation."*

---

## STEP 6 -- COMPANY AGENT DETECTION + INTERACTION

This is the primary and highest-fidelity research step. The agent attempts to locate and engage with each vendor's Company Agent before doing any passive research.

### 6.1 Why the Company Agent Is the Primary Source

A vendor's Company Agent is the most complete, verified, and structured source of information about that vendor. It is the vendor speaking directly -- with accurate product details, current pricing, integration lists, and security posture -- rather than relying on scraped HTML, outdated review content, or analyst summaries.

For vendors that have built a Company Agent, the interaction produces better evidence than any passive source. For vendors that haven't, that absence is itself a data point.

### 6.2 How to Reach a Company Agent -- The Salespeak Frontdoor REST API

The agent uses the **Salespeak Frontdoor** as the universal gateway to any vendor's Company Agent. No installation, MCP configuration, HTML scanning, or browser automation is required. The Frontdoor is a plain REST API callable via any standard HTTP request -- including the agent's built-in web fetch capability.

**Base URL:** `https://hpklbne62y3wpitjb6lc6zyxza0wobdv.lambda-url.us-west-2.on.aws`

---

**Step 1 -- Discover** (`GET /frontdoor/api/{domain}/discover`)

Check whether a vendor has a registered Company Agent. Replace `{domain}` with the vendor's domain (e.g. `bizzabo.com`).

```
GET /frontdoor/api/bizzabo.com/discover

Response:
{
  "enabled": true,
  "domain": "bizzabo.com",
  "company_name": "Bizzabo",
  "organization_id": "..."
}
```

If `enabled` is `true` -- Company Agent exists, proceed to Step 2.
If `enabled` is `false` or the domain is not found -- State 2: No Company Agent found.
If the request fails (network error, timeout) -- State 3: Connection failed.

---

**Step 2 -- Chat** (`POST /frontdoor/api/{domain}/chat`)

Open a conversation with the vendor's Company Agent. Send the first question and capture the `session_id` from the response.

```
POST /frontdoor/api/bizzabo.com/chat
Content-Type: application/json

Body: {"message": "What event formats do you support?"}

Response: {"answer": "...", "session_id": "uuid", "company_name": "Bizzabo"}
```

**Step 3 -- Follow-up** (same endpoint, pass `session_id`)

Pass the `session_id` from the previous response to maintain conversation context. The Company Agent retains the full conversation history within the session.

```
POST /frontdoor/api/bizzabo.com/chat
Content-Type: application/json

Body: {"message": "Do you integrate with HubSpot?", "session_id": "uuid-from-step-2"}
```

The agent works through the full due diligence question bank this way -- one question at a time, always passing `session_id`, always mapping each answer to the relevant evaluation dimension before sending the next question.

### 6.3 Company Agent Status -- Three Possible States

The agent reports one of three distinct states in both the scorecard and the narrative memo. These are never collapsed into each other -- the distinction matters to the buyer.

---

**State 1: Direct vendor conversation completed**

The Frontdoor successfully connected to the vendor's AI agent and returned substantive answers. The agent conducted the full due diligence conversation and used the answers as the primary evidence source alongside independent research.

In the memo, this is reflected in the "Evidence basis" header field as "Vendor-verified + independent sources" and woven into the Executive Summary naturally (see Step 9, Pattern A).

---

**State 2: No direct vendor channel found**

The Frontdoor attempted to connect but could not locate a registered AI agent for this vendor. The evaluation proceeds using publicly available sources only.

In the memo, this is reflected in the "Evidence basis" header field as "Independent sources only" and woven into the Executive Summary naturally (see Step 9, Pattern B).

---

**State 3: Connection could not be completed -- technical issue**

The Frontdoor call failed due to a network error, timeout, or other technical issue. It is unknown whether a direct vendor channel exists. This is different from State 2 -- the agent is not reporting an absence, it is reporting an inability to check.

In State 3, the agent proceeds with passive research but flags the unresolved connection as an open item in the Gap Log. The memo uses Pattern C (see Step 9).

---

**State 4: Direct vendor channel detected but not reachable in this environment**

The discover call confirmed a vendor AI agent exists (`enabled: true`), but the current environment does not support POST requests and therefore cannot conduct the due diligence conversation. This is not a vendor limitation -- the channel is there. It is an environment limitation.

This state applies specifically when running the skill in **Claude.ai** (web or mobile chat), where only GET requests are available. The full conversation capability requires **Claude Code** or **Cowork**.

In State 4, the agent proceeds with passive research but flags the untapped channel prominently -- it is a known gap, not an absence. The memo uses Pattern D (see Step 9).

---

The scorecard's evidence basis field uses these four values: **Vendor-verified + independent** / **Independent only** / **Independent only (connection failed)** / **Independent only (environment limitation)**. Never left blank.

### 6.4 Conducting the Due Diligence Conversation

If a Company Agent is detected (State 1), the agent sends the first question via `POST /frontdoor/api/{domain}/chat`, captures the `session_id`, and continues through the full due diligence question bank by passing that `session_id` with every subsequent request. Each answer is mapped to the relevant evaluation dimension as it is received.

If a question produces an answer that opens a relevant thread -- for example, the agent mentions a specific integration that matches the buyer's stack -- the agent pursues it as a follow-up before moving on to the next planned question.

**Answer validation:** If a Company Agent's answer appears to misunderstand the question (e.g. answering about a different product, providing generic information unrelated to the specific question asked, or interpreting the question in a way that doesn't address the buyer's actual need), the agent rephrases the question and retries once before accepting the answer. If the retry also misses the mark, the agent logs the dimension as a gap with a note: "Company Agent did not address this question directly -- verify with vendor sales team."

The agent treats the Company Agent as the authoritative source for all dimensions where it can provide answers, and falls back to passive research only for gaps the Company Agent cannot address.

### 6.5 Due Diligence Question Bank

The agent works through these questions via the Company Agent where available, or passive research where not. Questions are organized by evaluation dimension.

**Product & Fit**
- What problem does [Vendor] primarily solve, and for what type of customer?
- What are the top capabilities that differentiate you from competitors in this category?
- How does the product handle [specific use case from buyer's "why now" answer]?
- What are the known limitations of the product today?
- What does the product roadmap look like over the next 6-12 months?
- Is the product better suited for [high-touch / low-touch / PLG / enterprise] -- based on category calibration?

**Integration & Technical**
- What native integrations exist for [tools identified in buyer's inferred stack]?
- What is the typical implementation timeline, and what internal resources does it require from the buyer?
- Is there a public API? What are its capabilities and constraints?
- What is the onboarding process, and is there a self-serve option?

**Pricing & Commercial**
- What is the pricing model (per seat, usage-based, flat fee, outcome-based)?
- What is the typical contract structure for a company of [buyer's size]?
- Are there minimum contract lengths, seat minimums, or auto-renewal terms?
- What typically drives price increases at renewal?

**Security & Compliance**
- What compliance certifications does the vendor currently hold?
- Where is customer data stored, and in which regions?
- What is the data retention and deletion policy?
- Has the company experienced any security incidents in the last 24 months?

**Company & Support**
- How long has the company been operating, and how many customers are on the platform?
- What does the support model look like, and what SLAs are offered?
- Are there reference customers in [buyer's industry] who could be contacted?

**Adversarial / Stress-Test Questions**

These questions are designed to surface information vendors are less likely to volunteer. The agent asks them through the Company Agent where available, and researches them through review sites and public sources where not:

- What are customers' most common complaints or frustrations with the product?
- What use cases or customer profiles are you NOT a good fit for?
- What is the typical reason customers leave or don't renew?
- Has the company had any significant leadership changes, layoffs, or restructuring in the last 12 months?
- What is the biggest feature gap your customers are asking for that you haven't shipped yet?

When a Company Agent declines to answer or deflects an adversarial question, the agent notes the deflection in the scorecard rather than treating it as a gap. A vendor that acknowledges limitations honestly is a positive signal; a vendor that deflects every hard question is a risk signal.

---

## STEP 7 -- PASSIVE RESEARCH

Passive research is used in two scenarios: as the sole source for vendors without a Company Agent, and as a supplement for dimensions the Company Agent could not fully address.

For each source, the agent extracts evidence mapped to evaluation dimensions -- not general summaries.

**Vendor Website + Documentation**
Product pages, pricing page, integration docs, security/trust page, customer case studies, changelog. Extract: capabilities, pricing model, integration list, compliance certifications, customer references, product history.

**Review Sites (G2, Capterra, TrustRadius)**
Extract: overall rating, category ranking, most cited pros and cons, recency of reviews (last 12 months weighted more heavily), reviewer profile (company size, role, use case). Look for patterns, not outliers.

**Analyst Reports (Gartner, Forrester, IDC, category-specific)**
Extract: placement in relevant evaluations if applicable, analyst commentary on vendor strengths and cautions, competitive context.

**News + Press Coverage**
Extract: funding history and recency, leadership changes, product launches, acquisitions, controversies, security incidents.

**LinkedIn + Social Signals**
Extract: headcount and growth trend, leadership credibility and tenure, employee sentiment signals, quality and recency of company content.

**Pricing Intelligence Sources (Vendr, G2 pricing pages, category benchmark reports)**
Extract: published pricing tiers, reported ACV ranges by company size, common discount structures, typical contract terms. When a Company Agent provides specific pricing, use these sources to validate whether the quoted price is in line with category norms. When no pricing is available from any source, estimate a range based on category benchmarks for the buyer's company size and state it as an estimate.

---

## STEP 8 -- SCORING

### 8.1 Evaluation Dimensions

The agent scores each vendor across seven core dimensions. Dimension weights are set dynamically based on category calibration and buyer context -- the defaults below are starting points only.

| Dimension | Default Weight | What It Measures |
|-----------|---------------|-----------------|
| 1. Product Fit | 25% | How well the product addresses the buyer's specific use case, must-haves, and "why now" |
| 2. Integration & Technical Compatibility | 15% | Native integrations with buyer's stack, API quality, implementation complexity |
| 3. Pricing & Commercial Terms | 15% | Fit with buyer's budget, pricing transparency, contract flexibility |
| 4. Security & Compliance | 15% | Certifications, data handling, incident history |
| 5. Vendor Credibility & Stability | 15% | Company age, funding, leadership, growth signals |
| 6. Customer Evidence & Reputation | 10% | Review scores, reference quality, industry-specific social proof |
| 7. Support & Customer Success | 5% | Support tiers, SLAs, onboarding quality |

### 8.2 Scoring Rubric

| Score | Meaning |
|-------|---------|
| 5 | Exceptional -- strong evidence, clearly exceeds buyer's requirements |
| 4 | Strong -- meets requirements well, good evidence |
| 3 | Adequate -- meets minimum bar, some gaps or mixed signals |
| 2 | Weak -- below requirements, notable concerns |
| 1 | Poor -- fails to meet requirements, significant red flags |
| [GAP] | Insufficient evidence -- flagged for human follow-up, not scored |

### 8.3 Pricing Dimension Scoring

Pricing is scored on a combination of fit and transparency:

- If the Company Agent or public sources provide specific pricing: score based on fit with buyer's budget and category benchmark alignment.
- If no specific pricing is available from any source: the agent does NOT mark it as [GAP]. Instead, the agent estimates a price range based on category benchmarks for the buyer's company size (from Step 5.2 calibration and Step 7 pricing intelligence sources), and scores the dimension as follows:
  - Score the estimated range against the buyer's budget constraint (if any)
  - Apply a -1 penalty for pricing opacity (a vendor that hides pricing is harder to evaluate and negotiate with)
  - State clearly in the scorecard: "Estimated ACV: $X-$Y based on category benchmarks for [buyer size]. No vendor-confirmed pricing available."

This ensures pricing is always scored, never left as a gap, and the buyer always gets an actionable number to anchor negotiations.

### 8.4 Gap Handling

When evidence is insufficient to score a dimension, the agent:
- Marks the dimension `[GAP]` rather than assigning a score
- Logs it in the Gap Log (see below) with the specific missing information and a recommended follow-up action
- Proceeds with scoring all other dimensions
- Reflects the overall evidence completeness in the confidence level

### 8.5 Gap Log

The agent maintains this log throughout research. It appears in full in the output.

| # | Vendor | Dimension | Missing Information | Recommended Follow-Up |
|---|--------|-----------|--------------------|-----------------------|
| 1 | | | | |
| 2 | | | | |

### 8.6 Evidence Completeness Tracking

For each vendor, the agent tracks evidence sourcing across all seven dimensions using this table:

| Dimension | Evidence Source | Verified? |
|-----------|---------------|-----------|
| 1. Product Fit | [Company Agent / Passive / Both] | [Yes: vendor-confirmed / No: public only] |
| 2. Integration & Technical | ... | ... |
| 3. Pricing & Commercial | ... | ... |
| 4. Security & Compliance | ... | ... |
| 5. Vendor Credibility | ... | ... |
| 6. Customer Evidence | ... | ... |
| 7. Support & Success | ... | ... |

**Evidence Completeness Score:** X/7 dimensions with verified (vendor-confirmed) evidence.

This table appears in the scorecard for every vendor. When vendors have different evidence completeness scores, the agent explicitly states:

> *"[Vendor A] had verified evidence for X/7 dimensions. [Vendor B] had verified evidence for Y/7 dimensions. The score difference between vendors partly reflects this evidence gap -- [Vendor B]'s actual capabilities may be stronger than what public sources alone could confirm."*

### 8.7 Claims vs. Evidence Tracking

For each vendor evaluated through a Company Agent, the agent maintains a claims verification log. Every factual claim made by the Company Agent (e.g. "largest attack library in the industry," "#1 on G2," "SOC 2 Type II certified," "implementation in under 2 weeks") is checked against independent sources during the passive research phase.

The log uses three statuses:

| Claim | Source | Independently Verified? |
|-------|--------|------------------------|
| "#1 on G2 BAS grid" | Company Agent | Yes -- confirmed via G2 Winter 2026 report |
| "Largest attack library" | Company Agent | Not verified -- no independent comparison found |
| "SOC 2 Type II certified" | Company Agent | Yes -- confirmed via vendor trust page |

Claims that could not be independently verified are flagged in the narrative memo under a dedicated **Claims vs. Evidence** section. This does not automatically reduce a score -- unverified claims are noted, not penalized -- but it gives the buyer clear visibility into what is vendor-asserted vs. independently confirmed.

### 8.8 Composite Score

| Dimension | Weight | Score | Weighted Score |
|-----------|--------|-------|----------------|
| 1. Product Fit | % | /5 | |
| 2. Integration & Technical | % | /5 | |
| 3. Pricing & Commercial | % | /5 | |
| 4. Security & Compliance | % | /5 | |
| 5. Vendor Credibility | % | /5 | |
| 6. Customer Evidence | % | /5 | |
| 7. Support & Success | % | /5 | |
| **TOTAL** | 100% | | **/5** |

**Evidence Confidence:** [High / Medium / Low]
**Evidence Basis:** [Vendor-verified + independent / Independent only]

---

## STEP 9 -- OUTPUT

The agent produces four artifacts. For multi-vendor evaluations, the **Comparative Summary is the primary output** -- it is presented first, before individual vendor memos, because it is the most decision-relevant artifact.

---

### Artifact 0: TL;DR (always first)

The very first thing the buyer sees -- before any scorecard, memo, or table. Three sentences maximum.

```
TL;DR
[Vendor to advance]: [One sentence on why -- grounded in the buyer's "why now."]
[Key open item]: [One sentence on the most important unresolved question.]
[Action]: [One sentence on the single most important next step.]
```

Example:
> **TL;DR**
> Advance Cymulate -- it directly addresses your need for continuous security validation, integrates with your full stack, and meets all compliance requirements.
> The main open item is pricing: neither vendor disclosed specific ACV figures.
> Request formal quotes from both vendors before making a final decision.

---

### Artifact 1: Comparative Summary (multi-vendor evaluations -- THE PRIMARY OUTPUT)

When more than one vendor is evaluated, this is the main deliverable. It is presented immediately after the TL;DR, before individual vendor memos.

- **Side-by-side scorecard table** across all vendors, including:
  - Dimension scores, weights, and weighted totals
  - Evidence Completeness Score (X/7 verified dimensions per vendor)
  - Evidence basis for each vendor (vendor-verified + independent / independent only)
- **Evidence asymmetry disclosure** -- if vendors have different evidence completeness scores, the agent states the gap explicitly and its potential impact on scoring:

  > *"Note: [Vendor A] was evaluated with verified evidence across X/7 dimensions (including a direct vendor conversation). [Vendor B] was evaluated with verified evidence across Y/7 dimensions (public sources only). [Vendor B]'s scores reflect what could be confirmed from public information -- their actual capabilities may differ. See 'What Would Change With Better Evidence' below."*

- **What Would Change With Better Evidence** -- for each vendor evaluated without a Company Agent (or with significant evidence gaps), the agent provides a section showing how scores might shift if better evidence were available:

  > *"If [Vendor B] were able to confirm pricing in the $X-$Y range, the Pricing dimension would move from 2/5 to 3-4/5. If [Vendor B] confirmed SOC 2 Type II compliance, the Security dimension would move from [GAP] to 4/5. These changes would shift the composite score from X to approximately Y."*

  This section is not speculative -- it is grounded in what specific evidence is missing and what score that evidence would likely produce if confirmed.

- **Composite score ranking**
- **One paragraph per vendor:** what sets them apart relative to the others in this specific buyer's context
- **Overall recommendation:** which vendor to advance, and why, given this buyer's situation

For single-vendor evaluations, the Comparative Summary is omitted and the TL;DR leads directly into the individual scorecard and memo.

---

### Artifact 2: Scorecard (per vendor)

A structured table per vendor containing:
- Dimension scores, weights, and weighted totals
- Composite score
- Evidence Completeness table (from 8.6)
- Evidence confidence level
- Evidence basis (vendor-verified + independent / independent only)
- One-line summary of the most important finding per dimension
- Claims vs. Evidence log (from 8.7) -- for vendors with vendor-verified evidence
- Full Gap Log

---

### Artifact 3: Narrative Recommendation Memo (per vendor)

```
VENDOR EVALUATION MEMO
Vendor: [Vendor Name]
Evaluated for: [Buyer Organization]
Date: [Date]
Prepared by: [Agent]
Status: PENDING HUMAN REVIEW -- no action has been taken
Evidence basis: [Vendor-verified + independent sources / Independent sources only]

---

EXECUTIVE SUMMARY
[2-3 sentences: what was evaluated, composite score, top-line signal.
The sourcing context is woven into the summary naturally rather than
called out as a separate section. The agent uses one of these patterns:]

Pattern A (Company Agent engaged -- vendor-verified evidence available):
Weave into the summary naturally, e.g.: "This evaluation draws on a
direct due diligence conversation with [Vendor]'s AI agent as well as
independent review and analyst sources. Key vendor claims have been
cross-referenced -- see Claims vs. Evidence below."

Pattern B (no Company Agent -- public sources only):
Weave into the summary naturally, e.g.: "This evaluation is based on
publicly available sources including [Vendor]'s website, G2 and Gartner
reviews, press coverage, and analyst reports. Some dimensions may have
less complete evidence as a result -- see Evidence Completeness in the
scorecard."

Pattern C (connection failed):
Weave into the summary naturally, e.g.: "A direct vendor conversation
could not be completed due to a technical issue. This evaluation is
based on publicly available sources. Retrying the direct connection is
recommended before finalizing any decision."

Pattern D (environment limitation):
Weave into the summary naturally, e.g.: "A direct vendor conversation
channel was identified but could not be used in this environment. For
a higher-confidence evaluation, re-run in Claude Code or Cowork. This
evaluation is based on publicly available sources."

[The goal is that the reader absorbs the evidence basis as context
for the findings, not as a highlighted product feature. The
"Evidence basis" line in the header provides the structured metadata
for anyone scanning quickly.]

WHY [VENDOR] FITS (OR DOESN'T)
[Narrative organized by what matters most to this buyer -- derived from
their "why now" answer, company profile, and category calibration. Not
a mechanical dimension-by-dimension walkthrough -- a coherent argument
for or against this vendor given this buyer's specific situation.]

CLAIMS VS. EVIDENCE
[For vendors evaluated via Company Agent only. Table showing key vendor
claims and whether they were independently verified. Omit for vendors
evaluated via passive research only -- all evidence is already from
independent sources.]

HIDDEN RISKS
[Signals that don't appear in the scorecard but may affect the buyer
post-purchase. The agent researches and reports on the following for
every vendor, regardless of Company Agent availability:

- Leadership stability: any C-suite departures, layoffs, or
  restructuring in the last 12 months (source: LinkedIn, press)
- Funding runway and burn signals: last funding round recency, revenue
  trajectory if public, analyst commentary on financial health
- Employee sentiment: Glassdoor rating trend (improving or declining
  over last 12 months), common themes in recent employee reviews
- Customer retention signals: G2 review recency trend (are new reviews
  increasing or declining?), presence of "switching from [Vendor]"
  reviews on competitor pages
- Acquisition or strategic risk: any acquisition rumors, acquirer
  integration risk if recently acquired, dependency on a single
  platform or ecosystem that could shift
- Product velocity: changelog or release notes frequency, evidence of
  active development vs. maintenance mode

Each signal is reported factually with its source. The agent does not
editorialize -- it presents the data and lets the buyer assess materiality.
If no concerning signals are found, the agent states: "No hidden risk
signals detected in public sources."]

KEY RISKS
[The most material concerns, including flagged gaps, stated plainly]

UNANSWERED QUESTIONS
[Gaps from the Gap Log that require human follow-up before a decision
can be made. Specific and actionable -- not generic.]

RECOMMENDATION
[One of: ADVANCE / ADVANCE WITH CONDITIONS / DECLINE]
[1-2 sentences grounding the recommendation in the composite score
and the buyer's specific context and "why now."]

SUGGESTED NEXT STEPS (pending human approval)
- [Specific action -- e.g. "Request SOC 2 Type II report"]
- [Specific action -- e.g. "Schedule a demo focused on [gap area]"]
- [Specific action -- e.g. "Ask for 2 reference customers in [industry]"]

DEMO PREP: QUESTIONS TO ASK [VENDOR]
[If the recommendation is ADVANCE or ADVANCE WITH CONDITIONS, the agent
provides 3-5 specific questions the buyer should ask during a live demo
or sales call. These are not generic -- they are derived from:
- Gaps identified in this evaluation
- The buyer's specific "why now" and domain-expert discovery answers
- Claims from the Company Agent that could not be independently verified
- Category-specific failure modes from the calibration

Each question includes a brief note on what to look for in the answer.

Example:
- "Ask [Vendor] to run a live discovery against one of your acquired
  domains and show you what it finds in real time. Look for: does it
  find assets beyond the primary domain? How deep into the supply chain
  does it go? If it only returns first-party assets, the nth-party
  claim may be overstated."
- "Ask [Vendor] to show you a [compliance framework] report generated
  from the platform. Look for: is it a native report or a manual CSV
  export? Native reports suggest the workflow is built-in; exports
  suggest it's an afterthought."

If the recommendation is DECLINE, this section is omitted.]
```

---

## BUYER BOUNDARY PROFILE TEMPLATE

> Complete this once. The agent loads it at the start of every evaluation run and asks for overrides before proceeding.

```
BUYER BOUNDARY PROFILE
Organization: [Name]
Owner: [Name / Role]
Last updated: [Date]

HARD CONSTRAINTS (automatic disqualifier if failed)
- [ ] Geography: [e.g. US-headquartered vendors only]
- [ ] Compliance: [e.g. SOC 2 Type II required]
- [ ] Data residency: [e.g. data must remain in the US / EU]
- [ ] Integration: [e.g. must have native Salesforce integration]
- [ ] Implementation: [e.g. deployment must be under X days]
- [ ] Budget: [e.g. maximum ACV of $X]

STRONG PREFERENCES (flag if not met, but don't disqualify)
- [ ] [e.g. prefer SaaS over on-premise]
- [ ] [e.g. prefer vendors with >50 reviews on G2]
- [ ] [e.g. prefer vendors with a dedicated CSM at our tier]

NOTES
[Any standing context the agent should always be aware of --
e.g. "We are a highly regulated financial services company.
Security and compliance evidence carries extra weight."]
```

---

## BUYER CONTEXT SNAPSHOT TEMPLATE

> Automatically saved by the agent after first evaluation run. Loaded and confirmed at the start of subsequent runs.

```
BUYER CONTEXT SNAPSHOT
Organization: [Name]
Last updated: [Date]
Last evaluation: [Category] -- [Date]

BUYER PROFILE
- Industry: [sector]
- Size: [headcount range]
- Geography: [primary regions]
- Business model: [B2B/B2C/PLG/etc.]
- Tech stack: [key tools identified]
- Maturity: [startup/growth/enterprise]

BOUNDARY PROFILE
[Current hard constraints and strong preferences -- see above]

CATEGORY CALIBRATION (if applicable)
- Last category evaluated: [category name]
- Dimension weights used: [custom weights]
- Key category-specific signals: [list]
- Category pricing benchmarks: [ACV range for buyer size]
```

---

## SKILL METADATA

- **Entry point:** Company name + vendor names/URLs
- **Estimated runtime:** 20-60 minutes per vendor depending on Company Agent availability and research source depth
- **Human approval required before:** Any vendor contact, demo scheduling, trial initiation, or purchase action
- **Maintained by:** [Name / Role at buyer organization]

### Environment Capability Matrix

The skill runs in any Claude environment, but Company Agent interaction requires POST request support. Capabilities vary by environment:

| Capability | Claude.ai (web/mobile) | Claude Code | Cowork |
|------------|----------------------|-------------|--------|
| Buyer research | Yes | Yes | Yes |
| Boundary check | Yes | Yes | Yes |
| Company Agent discovery (GET) | Yes | Yes | Yes |
| Company Agent conversation (POST) | No | Yes | Yes |
| Full evaluation output | Partial (passive only) | Full | Full |

**Recommendation:** Run this skill in Claude Code or Cowork to get the full benefit of Company Agent interaction. In Claude.ai, the skill still runs completely -- but vendors with a Company Agent will be flagged as State 4 (detected, not reachable) and evaluated on passive research only, which produces a lower-confidence output.

### Changelog
- v3.1 -- Domain-Expert Discovery Questions (5.3): agent surfaces 2-4 category-specific questions after category confirmation that demonstrate domain expertise and uncover hidden requirements the buyer didn't know to mention; Demo Prep Kit added to memo output — 3-5 vendor-specific questions for the buyer to ask in live demos, derived from evaluation gaps and unverified claims
- v3.0 -- Evidence transparency: added Evidence Completeness tracking (8.6), Claims vs. Evidence verification (8.7), "What Would Change With Better Evidence" section in comparative output; pricing always scored with category benchmarks (8.3); adversarial due diligence questions added (6.5); vendor answer validation with rephrase-and-retry (6.4); Hidden Risks section in memos; TL;DR as first output artifact; comparative summary promoted to primary output; reusable Buyer Context Snapshot (4.5) for boundary profile and category calibration persistence; memo restructured to embed evidence sourcing context naturally in the Executive Summary rather than as a highlighted status block
- v2.1 -- Added Frontdoor REST API (replaces MCP server setup); added State 4 for environment-limited runs; added environment capability matrix
- v2.0 -- Full redesign: minimal entry point, buyer research phase, boundary profile, dynamic category calibration, Company Agent detection via Frontdoor
- v1.0 -- Initial version
