# Compilation Examples

Three annotated examples showing the full compilation workflow at different complexity levels. Each example walks through all four stages: Parse, Select, Construct, Validate.

---

## Example 1: Simple Task (2-3 Layers)

### User Input

"Write a professional email declining a vendor's proposal."

### Stage 1 — Parse

- Core task: Write a decline email.
- Task category: Creative / Generative (professional communication).
- Audience: External vendor.
- Constraints: Email format, professional tone, firm but polite.
- Context signals: None specific — no vendor name, proposal details, or relationship context provided.
- Deliverable type: Email.

Defaults assumed: Business context (not personal). The vendor relationship is ongoing (hedge toward preserving it). Standard professional tone.

### Stage 2 — Select

Simple task — 2-3 layers only. No formal reasoning or quality control needed.

- Identity: Brief professional communicator role (one sentence, not a full identity approach).
- Output: Email structure — subject line, body with clear decline, relationship preservation, and professional close.

### Stage 3 — Construct

```xml
<role>
You are a professional business communicator who writes clear, respectful correspondence.
</role>

<objective>
Write an email declining a vendor's proposal. Be direct about the decision (do not leave ambiguity about whether the answer is no), but maintain a respectful tone that preserves the professional relationship.
</objective>

<output_format>
Structure as a professional email:
- Subject line
- Opening acknowledgment of the proposal (1-2 sentences)
- Clear, direct decline with a brief reason (1-2 sentences)
- Relationship preservation — leave the door open for future opportunities (1 sentence)
- Professional close

Total length: 80-120 words. Do not over-explain the decision or apologize excessively.
</output_format>
```

### Stage 4 — Validate

- Objective is clear: decline, preserve relationship, be direct. Passes clarity test.
- No conflicting instructions.
- Complexity matches task — no unnecessary layers.
- Output specifies structure and length.
- Ready to use as-is.

### Compilation Note

Simple communication task — used a minimal 3-layer prompt (identity, objective, output format). No reasoning or quality control layers needed. Defaults assumed: ongoing vendor relationship, standard professional tone. To improve: add the vendor's name, what the proposal was for, and your specific reason for declining — this will make the output feel personalized rather than templated.

---

## Example 2: Medium Task (4-5 Layers)

### User Input

"Evaluate three cloud providers for our migration. We're a 200-person fintech company currently on-premise."

### Stage 1 — Parse

- Core task: Evaluate cloud providers and recommend one.
- Task category: Comparative / Decision (with technical elements).
- Audience: Implied — technical leadership or decision-makers. Defaulting to mixed technical/business audience.
- Constraints: Fintech → regulatory compliance is a hard constraint. 200 people → mid-size team capacity.
- Context signals: On-premise currently. Fintech industry. 200-person company. Missing: which three providers, current architecture details, budget, timeline, evaluation criteria.
- Deliverable type: Comparative evaluation with recommendation.

Defaults assumed: The three providers are AWS, Azure, and GCP (the industry standard comparison). Evaluation criteria default to: compliance and security, cost, migration complexity, managed services for fintech workloads, and team skill availability.

### Stage 2 — Select

Medium task — 4-5 layers.

- Identity: Technical Architect with cloud migration and fintech compliance expertise.
- Reasoning: Vendor/Tool Selection variant from the Comparative family — systematic evaluation against defined criteria.
- Output: Decision Matrix structure — criteria-based evaluation with recommendation.
- Quality Control: Standard checks plus edge case identification (what could go wrong during migration).

### Stage 3 — Construct

```xml
<role>
You are a principal cloud architect specializing in infrastructure migration for regulated financial services companies. You evaluate platforms against security, compliance, operational cost, and migration feasibility. You are direct in your recommendations and explicit about tradeoffs.
</role>

<objective>
Evaluate AWS, Azure, and GCP as migration targets for a 200-person fintech company currently running on-premise infrastructure. Produce a structured comparison with a clear recommendation that technical leadership can use for a go-decision.
</objective>

<context>
We are a 200-person fintech company migrating from on-premise infrastructure to cloud. As a financial services company, we have regulatory compliance requirements (SOC 2, PCI DSS at minimum). Our current infrastructure details and specific workload characteristics are not yet specified — evaluate based on typical fintech workloads: transaction processing, data analytics, customer-facing APIs, and regulatory reporting.
</context>

<reasoning>
Approach this comparison as follows:
1. Define the evaluation criteria before comparing: regulatory compliance capability, total cost of ownership for a fintech workload, migration complexity from on-premise, managed services relevant to financial services, and team skill availability in the market.
2. Evaluate each provider against every criterion consistently — same dimensions, same depth.
3. Identify where the providers are functionally equivalent — do not manufacture differences for commodity capabilities.
4. Identify where they genuinely diverge and why it matters for a fintech migration specifically.
5. Make a clear recommendation with explicit reasoning. State what the recommended provider sacrifices compared to alternatives.
</reasoning>

<output_format>
Structure as a cloud provider evaluation:

Executive Summary (3-4 sentences: recommendation, primary rationale, and key tradeoff)

Evaluation Criteria (1 paragraph defining the criteria and their relative weight for fintech)

Provider Comparison (one subsection per criterion, evaluating all three providers consistently — 2-3 paragraphs per criterion)

Summary Matrix (table: Criterion | AWS | Azure | GCP with brief ratings)

Recommendation (1 paragraph: which provider, why, and what to watch for)

Migration Considerations (1 paragraph: the top 3 risks specific to moving from on-premise to the recommended provider)

Total length: 1200-1500 words. Write for a mixed technical/business audience.
</output_format>

<quality_standards>
- Do not treat all three providers as equally good "in different ways." Make a clear recommendation.
- Distinguish between vendor marketing claims and demonstrated capability in regulated environments.
- All cost comparisons should note assumptions and typical ranges rather than specific pricing that becomes outdated.
- Identify at least two migration risks specific to moving a fintech workload from on-premise to cloud.
</quality_standards>
```

### Stage 4 — Validate

- Objective passes clarity test — unambiguous deliverable and decision.
- No conflicting instructions.
- Reasoning is specific to vendor comparison, not generic "think step by step."
- Output specifies per-section structure.
- Quality control targets the most likely failure modes: false equivalence, vendor marketing, stale pricing.
- Context notes its own gaps (current architecture not specified) — prompt still works but produces more generic output.
- Ready to use as-is.

### Compilation Note

Used the Technical Architect identity with fintech compliance specialization. Vendor/Tool Selection reasoning from the Comparative family. Decision Matrix output adapted for cloud evaluation. Defaults assumed: AWS/Azure/GCP as the three providers, and standard fintech compliance requirements (SOC 2, PCI DSS). To improve results: add your current architecture details (databases, languages, key dependencies), your migration timeline, budget constraints, and your team's existing cloud experience — these would make the evaluation significantly more specific to your situation.

---

## Example 3: Complex Task (All 5 Layers + Quality Control)

### User Input

"Develop a market entry strategy for our AI product in the healthcare vertical. We're a mid-size SaaS company ($85M ARR) with 300+ enterprise customers, mostly in retail and hospitality. Engineering team of 40, strong NLP capabilities. We can allocate max 8 engineers without impacting core roadmap. Need to show traction within 18 months. Zendesk, Intercom, and several startups are already in market. Our potential edge is deep integration with workforce management."

### Stage 1 — Parse

- Core task: Evaluate market entry opportunity and recommend go/no-go with strategy.
- Task category: Strategic / Advisory (primary) with market research elements (secondary).
- Audience: Executive team making a go/no-go decision.
- Constraints: 8 engineers max, 18 months to show traction, cannot impact core roadmap.
- Context signals: Rich — $85M ARR, 300+ enterprise customers, retail/hospitality concentration, 40-person engineering team, NLP capabilities, workforce management integration as differentiator, named competitors.
- Deliverable type: Strategic recommendation / executive brief.

No defaults needed for the core task — the user provided rich context. Default: the "AI product in healthcare" likely means AI-powered customer service for healthcare given the competitive context (Zendesk, Intercom). Flag this assumption.

### Stage 2 — Select

Complex task — full 5-layer treatment.

- Identity: Strategic Advisor with market entry and competitive analysis expertise. Senior seniority for executive audience.
- Reasoning: Market and Competitive Strategy (primary) with Resource Allocation elements (secondary — 8-engineer constraint is a resource allocation problem).
- Output: Executive Brief — recommendation-first, with supporting analysis.
- Quality Control: Standard checks plus internal consistency, agreeableness counter (do not manufacture a positive recommendation if the market entry does not make sense), and assumption transparency.

### Stage 3 — Construct

```xml
<role>
You are a senior strategy consultant specializing in market entry and competitive analysis for technology companies. You evaluate opportunities using quantitative evidence, competitive dynamics, and operational feasibility. You are direct in your recommendations and explicit about tradeoffs.
</role>

<objective>
Evaluate whether our company should enter the AI-powered customer service market in the healthcare vertical within the next 12 months. Produce a recommendation with clear reasoning that our executive team can use to make a go/no-go decision.
</objective>

<context>
Background:
We are a mid-size SaaS company ($85M ARR) selling workforce management software to enterprises. Our engineering team (40 people) has strong NLP capabilities from our existing product's scheduling module. We have 300+ enterprise customers, 60% in retail and hospitality.

Constraints:
- Maximum of 8 engineers allocated to a new initiative without impacting core roadmap.
- Sales cycle is 6-9 months for enterprise deals.
- Need to show measurable traction within 18 months to satisfy board expectations.

Competitive landscape:
Zendesk, Intercom, and several well-funded startups are already in market. Our potential advantage is deep integration with workforce management — connecting AI customer service to actual staffing and scheduling.
</context>

<reasoning>
Approach this strategically:
1. Map the competitive landscape and identify where the healthcare AI customer service market is underserved.
2. Assess our differentiation — is the workforce management integration a genuine advantage or an assumed one? What would healthcare customers specifically value about it?
3. Evaluate the resource constraints — can 8 engineers build something competitive in the required timeline? What scope is realistic?
4. Model two scenarios: the optimistic case and the realistic case. Base your recommendation on the realistic case.
5. Identify the biggest risk to the recommendation and what would mitigate it.
</reasoning>

<output_format>
Structure as an executive brief:

Recommendation (2-3 sentences: go, no-go, or conditional go with specific conditions)

Market Opportunity (2 paragraphs: size, growth, underserved segments in healthcare specifically)

Competitive Assessment (2 paragraphs: where we can and cannot win against Zendesk, Intercom, and startups)

Feasibility Analysis (2 paragraphs: can we build it with 8 engineers in the required timeline?)

Key Risks (top 3 risks with mitigation for each)

Recommended Next Steps (3-5 concrete actions if the answer is go)

Total length: 800-1000 words. Be decisive, not hedging.
</output_format>

<quality_standards>
- If the market entry does not make strategic sense, say so directly. Do not manufacture a positive recommendation.
- All claims about market size or competitive dynamics must be grounded in the provided context or clearly marked as estimates.
- Recommendations must be achievable within the stated constraints (8 engineers, 18-month traction window).
- Verify that your recommendations do not contradict each other — if you recommend entering the market, your feasibility analysis must support that it can be done with available resources.
</quality_standards>
```

### Stage 4 — Validate

- Objective passes clarity test — specific decision (go/no-go), specific audience (executive team), specific deliverable (recommendation with reasoning).
- No conflicting instructions.
- Reasoning is specific to market entry strategy — competitive mapping, differentiation assessment, resource feasibility, scenario modeling.
- Output specifies per-section structure with approximate lengths.
- Quality control addresses the most important failure modes: manufactured optimism (agreeableness counter), unsupported market claims, constraint-violating recommendations, and internal inconsistency.
- Context is rich — all provided by the user.
- Ready to use as-is.

### Compilation Note

Used the Strategic Advisor identity with market entry specialization, calibrated for executive audience. Market and Competitive Strategy reasoning with resource allocation elements folded into step 3 (the 8-engineer constraint makes this a resource allocation problem within a strategic decision). Executive Brief output with per-section structure. Quality control includes an agreeableness counter — the prompt explicitly instructs Claude to recommend against market entry if the analysis does not support it. The user's context is rich; no major defaults were needed. Assumed "AI product in healthcare" means AI-powered customer service based on the competitive context (Zendesk, Intercom). To adjust: if the AI product is something other than customer service, revise the competitive landscape section of the context.
