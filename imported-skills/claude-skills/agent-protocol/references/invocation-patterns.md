# Invocation Patterns — Inter-Agent Protocol

Common cross-functional patterns, with examples and guidance on when to invoke vs assume.

---

## Pattern 1: Revenue Planning Chain
**CRO → CFO → CMO**

Used when: setting revenue targets, allocating growth budget, modeling pipeline scenarios.

```
CRO initiates:
"Planning Q3 revenue targets. Need financial constraints and marketing input."

CRO → [INVOKE:cfo|What's our Q3 revenue target given current runway and burn?]

CFO responds:
[RESPONSE:cfo]
Key finding: To maintain 12-month runway without new raise, Q3 ARR target ≥ $2.4M (+20% QoQ)
Supporting data:
  - Current ARR: $2.0M, burn: $180K/month, runway: 14 months
  - 20% QoQ growth maintains runway; <15% triggers bridge discussion
  - Board expectation communicated as 25% QoQ
Confidence: high
Caveat: Assumes no new hires or major infrastructure spend in Q3.
[/RESPONSE]

CRO → [INVOKE:cmo|Given a $2.4M Q3 ARR target, what pipeline coverage and CAC should we plan for?]
[CHAIN: cro → cfo → cmo]

CMO responds:
[RESPONSE:cmo]
Key finding: Need 3x pipeline ($7.2M) and CAC ≤ $8,400 to hit $2.4M ARR target.
Supporting data:
  - Historical close rate: 33% → 3x coverage required
  - Current CAC: $9,100 → 8% efficiency improvement needed
  - Recommended channel mix: 60% outbound, 30% inbound, 10% partner
Confidence: medium
Caveat: Close rate assumes no sales team changes; any rep turnover drops it to 25%.
[/RESPONSE]
```

**What CRO does with this:** Synthesizes CFO constraint (target) + CMO playbook (how to hit it) into a revenue plan. Does not invoke further (depth limit reached).

---

## Pattern 2: Hiring Decision Chain
**CHRO → CFO → COO**

Used when: headcount planning, role approval, capacity vs budget tradeoffs.

```
CHRO initiates:
"Engineering wants to hire 3 senior engineers. Need budget clearance and capacity validation."

CHRO → [INVOKE:cfo|Can we afford 3 senior engineers in H2? Fully loaded ~$180K each.]

[RESPONSE:cfo]
Key finding: Budget supports 2 hires now; 3rd is contingent on Q2 ARR closing above $2.1M.
Supporting data:
  - Current H2 headcount budget: $340K remaining
  - 2 hires = $270K fully loaded → $70K buffer
  - 3 hires = $405K → $65K over; triggers board approval
Confidence: high
Caveat: Based on current runway projection — fundraise close changes this completely.
[/RESPONSE]

CHRO → [INVOKE:coo|Do operations support onboarding 2-3 engineers in H2? Any capacity constraints?]
[CHAIN: chro → cfo → coo]

[RESPONSE:coo]
Key finding: Can absorb 2 comfortably; 3rd requires dedicated onboarding lead or delays velocity 6 weeks.
Supporting data:
  - Current eng team: 8 → adding 2 is 25% growth (manageable)
  - Onboarding bottleneck: 1 senior eng mentor per 1-2 new hires, currently at capacity
  - Dev environment setup: 3-week lead time per hire
Confidence: medium
Caveat: Assumes no concurrent product launches requiring full team focus.
[/RESPONSE]

CHRO synthesis: Recommends 2 hires now, pipeline 3rd for Q3 contingent on ARR milestone.
```

---

## Pattern 3: Product Launch Chain
**CPO → CTO → CMO**

Used when: planning feature launches, assessing readiness, aligning go-to-market.

```
CPO initiates:
"Planning Q3 launch of [Feature X]. Need technical readiness and GTM input."

CPO → [INVOKE:cto|Is Feature X technically ready for Q3 launch? Key risks?]

[RESPONSE:cto]
Key finding: 70% complete; Q3 launch is achievable with scope cut — 2 items must move to Q4.
Supporting data:
  - Core feature: complete; performance optimization: 3 weeks remaining
  - Infrastructure scaling: needs load testing at 10x current volume
  - Scope cuts needed: advanced analytics dashboard, third-party integrations
Confidence: medium
Caveat: Assumes no critical bugs found in load testing; historical rate suggests 1-2 found.
[/RESPONSE]

CPO → [INVOKE:cmo|Given Q3 launch of Feature X (core only, no analytics/integrations), what's the GTM plan?]
[CHAIN: cpo → cto → cmo]

[RESPONSE:cmo]
Key finding: Core-only launch works for existing customers; new logo acquisition needs integrations — recommend phased announcement.
Supporting data:
  - Phase 1: Early access for top 20 accounts → testimonials and case studies
  - Phase 2: Full launch with integration partners in Q4
  - CAC impact: core-only launch reduces new logo conversion rate 15%
Confidence: medium
Caveat: Competitor launched similar feature last month — window for differentiation is narrow.
[/RESPONSE]
```

---

## Pattern 4: Crisis Broadcast
**CEO → All Roles**

Used when: major adverse event, fundraise miss, key customer loss, market disruption.

```
CEO broadcasts:
[BROADCAST:all|Scenario: largest customer (28% of ARR) gives 60-day termination notice. 
Each role: what's the immediate impact on your domain and your top recommended action?]

Roles respond INDEPENDENTLY (no agent sees others' responses first):

[RESPONSE:cfo]
Key finding: 28% ARR loss drops runway from 14 to 8 months at current burn.
Supporting data:
  - Lost ARR: ~$560K → burn multiple increases from 1.8x to 3.2x
  - Bridge options: $500K credit line (pre-approved), defer 2 planned hires
  - Fundraise timeline must compress: target term sheet within 60 days
Confidence: high
Caveat: Assumes no secondary customer churn triggered by news.
[/RESPONSE]

[RESPONSE:cro]
Key finding: Pipeline must replace $560K ARR within 6 months to avoid emergency measures.
Supporting data:
  - Current qualified pipeline: $1.8M → need 31% close rate (currently 28%)
  - 3 deals in late stage can cover 70% of gap if closed this quarter
  - Churn risk: 2 other accounts had similar usage patterns — immediate EBR required
Confidence: medium
Caveat: Close rate may drop if word spreads; manage communication carefully.
[/RESPONSE]

[RESPONSE:chro]
Key finding: Hiring freeze recommended immediately; retain all current staff.
Supporting data:
  - 4 open reqs should pause pending CFO guidance
  - At-risk of counter-poaching: 2 senior engineers, 1 product lead
  - Retention bonuses for key staff: ~$80K to secure 12-month commitments
Confidence: high
Caveat: Morale impact of freeze can accelerate attrition if not communicated well.
[/RESPONSE]

[RESPONSE:cpo]
Key finding: Accelerate features that differentiate with remaining accounts; reduce scope to core.
Supporting data:
  - Lost customer's feature requests: deprioritize (no longer strategic)
  - Features most valued by remaining top 5 accounts: [list from account data]
  - Reduce Q3 scope by 30% to free engineering capacity for retention work
Confidence: medium
Caveat: Need sales input on which features are blocking new logo deals.
[/RESPONSE]

[RESPONSE:cmo]
Key finding: Control the narrative; proactive communication to market reduces churn cascade risk.
Supporting data:
  - Draft customer communication within 48 hours (frame as strategic pivot, not loss)
  - Press: no comment strategy unless proactively asked
  - Replace pipeline: double down on ICP segments where we're strongest
Confidence: medium
Caveat: If customer goes public with criticism, narrative control becomes much harder.
[/RESPONSE]

CEO synthesis: [Aggregates all 9 responses, identifies conflicts, sets priorities]
```

---

## When to Invoke vs When to Assume

### Invoke when:
- Cross-functional data is material to the decision
- Getting it wrong changes the recommendation significantly
- The other role has data you genuinely don't have
- Time allows (not in Phase 2 isolation)

### Assume when:
- You're in Phase 2 (always — no exceptions)
- The chain is at depth 2 (you cannot invoke further)
- The answer is directionally obvious (e.g., "CFO will care about runway")
- The precision doesn't change the recommendation

### State assumptions explicitly:
```
[ASSUMPTION: runway ~12 months — not verified with CFO; actual may vary ±20%]
[ASSUMPTION: CAC ~$8K based on industry benchmark — CMO has actual figures]
[ASSUMPTION: engineering capacity at ~70% — not verified with CTO]
```

---

## Handling Conflicting Responses

When two agents give incompatible answers, surface it:

```
[CONFLICT DETECTED]
CFO says: runway extends to 18 months if Q3 targets hit
CRO says: only 45% confidence Q3 targets will be hit
Resolution: use probabilistic blend
  - 45% probability: 18-month runway (optimistic case)
  - 55% probability: 11-month runway (current trajectory)
Expected value: ~14 months
Recommendation: plan for 12 months, trigger bridge at 10.
[/CONFLICT]
```

**Resolution options:**
1. **Conservative:** Use worse case — appropriate for cash/runway decisions
2. **Probabilistic:** Weight by confidence scores — appropriate for planning
3. **Escalate:** Flag for human decision — appropriate for high-stakes irreversible choices
4. **Time-box:** Gather more data within 48 hours — appropriate when data gap is closeable

---

## Anti-Patterns to Avoid

| Anti-pattern | Problem | Fix |
|---|---|---|
| Invoke to validate your own conclusion | Confirmation bias loop | Ask open-ended questions |
| Invoke when assuming works | Unnecessary latency | State assumption clearly |
| Hide conflicts between responses | Bad synthesis | Always surface conflicts |
| Invoke across depth > 2 | Loop risk | State assumption at depth 2 |
| Invoke during Phase 2 | Groupthink contamination | Flag with [ASSUMPTION:] |
| Vague questions | Poor responses | Specific, scoped questions only |
