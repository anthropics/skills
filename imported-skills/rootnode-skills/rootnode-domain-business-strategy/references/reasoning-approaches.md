# Business Strategy Reasoning Methods

Four reasoning methods for business strategy tasks. Each provides a structured analytical approach as a `<reasoning>` XML block that you paste into your Claude prompt.

## Table of Contents

- [Due Diligence](#due-diligence)
- [Business Model Analysis](#business-model-analysis)
- [Portfolio Strategy](#portfolio-strategy)
- [Stakeholder & Organizational Dynamics](#stakeholder--organizational-dynamics)
- [Combining Methods](#combining-methods)

---

## Due Diligence

**Use when:** The task requires systematic evaluation of an acquisition target, investment opportunity, or strategic partnership. Due diligence follows a comprehensive evaluation framework covering strategic, financial, operational, and risk dimensions in a specific sequence. Use this when the evaluation needs to be thorough enough that decision-makers can commit significant capital based on it.

**Pairs well with:** M&A / Corporate Development Advisor identity. Investment Case output format.

```xml
<reasoning>
Conduct this due diligence as follows:
1. Start with the strategic rationale. Why is this transaction being considered? What specific gap does it fill or capability does it provide? If the strategic rationale is not compelling on its own, flag this immediately — financial engineering should not substitute for strategic logic.
2. Evaluate the target's market position and competitive dynamics. Is the target's position durable or eroding? What industry trends work for or against it? Assess whether you are buying a position that will appreciate or depreciate.
3. Analyze the financial fundamentals. Revenue quality (recurring vs. one-time, concentration risk, growth trajectory), margin structure, capital requirements, and cash flow characteristics. Distinguish between reported performance and underlying economic performance.
4. Assess operational capabilities and risks. What does the target do well operationally? Where are the dependencies — on key people, specific customers, particular technologies, or regulatory conditions? What breaks if any of these change?
5. Evaluate integration or execution risk. How complex is the integration? Where are the highest-risk integration points — systems, teams, customers, culture? What is the realistic timeline and cost to capture the expected value?
6. Synthesize into a deal assessment. Does the strategic value justify the likely price and integration cost? What are the conditions under which this deal destroys value rather than creates it? What would you need to believe for this to be a good deal?
</reasoning>
```

**Watch for:** Claude may produce diligence that is comprehensive but undifferentiated — giving equal attention to all dimensions rather than identifying which factors actually determine whether this specific deal is good or bad. If the output reads like a checklist rather than a judgment, add: *"After completing the evaluation, identify the two or three factors that most determine whether this deal succeeds or fails. Focus your synthesis on those factors, not on a balanced summary of all dimensions."*

This method works best with a rich `<context>` section containing target financials, market data, and deal parameters. Without that context, the analysis will be generic.

---

## Business Model Analysis

**Use when:** The task requires understanding how a business actually makes money — its unit economics, cost structure, revenue architecture, and value chain position. Distinct from financial analysis (which evaluates performance) in that this examines the structural mechanics of the business. Use for evaluating business model viability, comparing business model approaches, or identifying where a model is structurally vulnerable.

**Pairs well with:** Management Consultant or Corporate Strategist identity. Strategic Options Assessment output format.

```xml
<reasoning>
Analyze this business model as follows:
1. Identify the core value proposition — what does the customer get that they are willing to pay for? Be precise about who the customer is and what problem is being solved. If there are multiple customer segments, map each one separately.
2. Trace the revenue architecture. How does value convert to revenue? Map the pricing model (subscription, transaction, usage, licensing, advertising, or hybrid), the key revenue drivers (volume × price, users × ARPU, transactions × take rate), and where revenue concentration risk exists.
3. Map the cost structure and operating leverage. What are the fixed costs vs. variable costs? How does unit economics change at 2x and 10x scale? Where are the structural cost advantages or disadvantages versus alternatives?
4. Assess the value chain position. Where does this business sit in its value chain? What is its bargaining power relative to suppliers and customers? Is it capturing a defensible share of the total value created, or is it in a position that competitors or adjacent players could squeeze?
5. Identify the flywheel or reinforcing loops, if any. What makes this business get stronger as it grows? Where are the network effects, data advantages, switching costs, or scale economies? Be skeptical — label genuine structural advantages differently from marketing narratives about moats.
6. Stress-test the model. What breaks first? If customer acquisition costs rise 50%, does the model still work? If the key revenue driver declines, how quickly does the economics deteriorate? Identify the single assumption that most determines whether this model is viable long-term.
</reasoning>
```

**Watch for:** Claude may describe a business model rather than analyze it — narrating "they make money by..." rather than evaluating the structural economics. If the output reads like a business description, add: *"This is an analysis, not a description. For every element of the model, evaluate whether it is structurally sound, what makes it defensible or vulnerable, and how it compares to alternative approaches. State the 'so what' for each finding."*

Also watch for Claude being overly generous about moats and flywheels — most businesses that claim network effects don't actually have strong ones. Reinforcing with specific competitive context in the `<context>` section sharpens the analysis.

---

## Portfolio Strategy

**Use when:** The task involves managing a portfolio of businesses, products, investments, or initiatives — deciding how to allocate resources across them, what to add or divest, and how to balance the portfolio for performance and risk. Portfolio strategy addresses composition — what should be in the portfolio and what should not — not just how to distribute a fixed resource pool.

**Pairs well with:** Corporate Strategist identity. Strategic Options Assessment or Board Narrative output format.

```xml
<reasoning>
Approach this portfolio strategy as follows:
1. Define the portfolio's strategic purpose. What is this portfolio optimizing for — growth, cash generation, risk diversification, market coverage, or optionality? The answer determines what "balanced" means. A portfolio optimized for growth looks different from one optimized for resilience.
2. Assess each component on two dimensions: its standalone performance trajectory (growing, stable, or declining) and its strategic contribution to the whole (does it provide capabilities, market access, or cash that other components need?). A low-performing unit that provides critical capabilities may be more valuable than its standalone metrics suggest.
3. Identify the portfolio's structural balance. Where is it concentrated — by market, geography, customer type, growth stage, or risk profile? What shock or disruption would damage multiple components simultaneously? Where is the portfolio under-diversified?
4. Evaluate the gaps. What capabilities, market positions, or growth vectors is the portfolio missing? For each gap, assess whether the better path is building internally, acquiring, or partnering — considering time-to-value, capital required, and integration risk.
5. Determine what to exit. Which components no longer serve the portfolio's strategic purpose and are not likely to in the future? Be explicit — portfolio strategy requires pruning, not just adding. Evaluate exit timing and method (sell, wind down, spin off) for each candidate.
6. Recommend the target portfolio composition and the sequence of moves to get there. Prioritize moves by impact and feasibility. Identify which moves are independent and which are sequenced.
</reasoning>
```

**Watch for:** Claude may avoid recommending divestitures or exits, defaulting to "invest more" or "turnaround" recommendations for underperforming units. If the output lacks pruning recommendations, add: *"Assume that at least one component of the portfolio should be exited or significantly restructured. If you believe none should be, make that case explicitly — but do not skip the evaluation."*

Also watch for the analysis becoming a unit-by-unit review rather than a portfolio-level synthesis — the value of portfolio strategy is in the interactions between components, not in evaluating each one independently.

---

## Stakeholder & Organizational Dynamics

**Use when:** The task involves navigating organizational politics, building support for a strategic initiative, managing resistance to change, or understanding how power dynamics will affect a decision's outcome. This method focuses specifically on the human and political dimensions. Use as a secondary reasoning method when any strategic initiative requires organizational buy-in to succeed.

**Pairs well with:** Corporate Strategist identity. Any output format — this method is most often combined with another primary reasoning method.

```xml
<reasoning>
Map the organizational dynamics as follows:
1. Identify the key stakeholders — not by title, but by their actual influence on this decision. Who can approve, block, accelerate, or undermine the initiative? Map formal authority (who signs off) separately from informal influence (who shapes opinions).
2. For each critical stakeholder, assess their position: What do they gain or lose from this initiative? What are their stated concerns, and what are their underlying interests that they may not state? What is their current stance — active support, passive support, neutral, passive resistance, or active opposition?
3. Identify the coalitions. Who is aligned with whom, and why? Where are the natural alliances and the unlikely ones? Which coalitions have enough combined influence to determine the outcome?
4. Determine the pivotal stakeholders — those whose shift from opposition or neutrality to support would change the outcome. What would it take to move them? Is the required concession or reframing acceptable?
5. Identify the landmines. What organizational dynamics could derail this initiative regardless of its merit? Turf conflicts, historical grievances, competing priorities, timing conflicts with other initiatives, or trust deficits between key players.
6. Recommend the engagement approach. Sequence matters — who should be engaged first, what should be discussed in which forum, and what commitments need to be secured before broader communication? Design for building momentum, not for efficiency.
</reasoning>
```

**Watch for:** Claude may produce stakeholder analysis that is too abstract — categorizing stakeholders as "supportive" or "resistant" without explaining what specifically drives their position. If the analysis lacks behavioral specificity, add: *"For each stakeholder, explain what specific outcome they are trying to achieve or protect. Their position on this initiative follows from their interests — make those interests visible."*

This method works best when paired with a `<context>` section that includes information about specific people, their roles, their known positions, and the organizational history. Without that context, the analysis will be generic.

---

## Combining Methods

For complex business strategy tasks, you can combine two reasoning methods. Follow these rules:

1. **5-7 steps total.** Do not paste two full 6-step methods end-to-end (12 steps produces bloated analysis). Select the most valuable steps from each.
2. **Lead with the dominant method.** If the task is primarily a deal evaluation with organizational considerations, lead with Due Diligence and weave in key Stakeholder & Organizational Dynamics steps.
3. **Watch for contradictions.** Some method pairings can produce conflicting analytical frames. If Due Diligence says "good deal" but Stakeholder & Organizational Dynamics reveals "cannot be executed in this organization," the synthesis must confront this tension rather than letting one conclusion quietly override the other.

### Tested Combinations

| Primary | Secondary | Use Case |
|---|---|---|
| Due Diligence | Stakeholder & Organizational Dynamics | Deal evaluation where internal politics affect whether the deal gets approved or integrated successfully |
| Portfolio Strategy | Business Model Analysis | Portfolio review where you need to understand the structural economics of each business unit before making allocation decisions |
| Business Model Analysis | Stakeholder & Organizational Dynamics | Business model redesign where organizational buy-in is required to execute the change |
