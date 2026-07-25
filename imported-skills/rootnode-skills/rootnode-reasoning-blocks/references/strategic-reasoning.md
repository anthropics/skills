# Strategic / Planning Reasoning Approaches

Three approaches for tasks that require making decisions about direction, resources, or organizational change. Each addresses a different strategic tension: competitive positioning, resource scarcity, or transition management.

---

## Market & Competitive Strategy

**Use when:** The task involves evaluating a market opportunity, competitive positioning, or strategic direction where competitive dynamics matter.

```xml
<reasoning>
Approach this strategically:
1. Define the market boundaries — what are we actually competing in? Avoid defining the market so broadly that the analysis loses focus or so narrowly that you miss adjacent threats.
2. Map the competitive landscape: who are the established players, who is gaining share, and where are the gaps? Focus on structural positions, not just current market share.
3. Identify the sources of differentiation available — what can we do that is difficult for competitors to replicate? Distinguish between durable advantages and temporary ones.
4. Assess timing — is this market early enough that positioning matters more than features, or mature enough that switching costs dominate? Timing changes which strategy is viable.
5. Identify the two or three strategic moves that would most improve competitive position, and what each would cost (resources, tradeoffs, opportunity cost).
6. State your recommendation clearly. If the opportunity is not attractive, say so — do not manufacture a positive case.
</reasoning>
```

### Usage Guidance

Use for market entry decisions, competitive response planning, product positioning, partnership evaluations, and any task where competitive dynamics shape the answer. The approach produces strategic recommendations grounded in competitive reality, not aspirational positioning.

### Failure Modes

- **Framework defaulting:** Claude may default to Porter's Five Forces or other textbook frameworks even when they don't fit the specific situation. The approach avoids naming frameworks to prevent this, but if the output reads like a textbook analysis, add: "Analyze the specific competitive dynamics of this market. Do not apply standard frameworks unless they genuinely illuminate the situation."
- **Manufactured optimism:** Claude may construct a positive case even when the market opportunity is weak. Step 6 addresses this explicitly, but reinforce if needed: "If the competitive position is unfavorable, state that clearly."

### When to Modify

For tasks that are primarily about market research rather than strategic decisions, use Landscape Scan from `research-reasoning.md` instead. For tasks that involve both competitive strategy and resource decisions, combine steps 1-3 from this approach with steps 1-2 from Resource Allocation below.

---

## Resource Allocation

**Use when:** The task involves deciding how to distribute limited resources (budget, people, time, attention) across competing priorities. Distinct from general strategic planning because the core tension is scarcity, not direction.

```xml
<reasoning>
Approach this allocation decision as follows:
1. Identify the total resource pool and the competing demands on it. Be precise about what is actually available, not what is theoretically possible.
2. For each competing demand, assess: What is the expected return? What is the cost of underfunding or deferring it? Is it reversible — can resources be reallocated later if priorities change?
3. Identify dependencies — which allocations enable or block other allocations? Sequence matters as much as quantity.
4. Test the proposed allocation against the strategy: does this distribution actually advance the stated priorities, or does it spread resources evenly in a way that advances nothing?
5. Identify the minimum viable allocation for each priority — what is the threshold below which the investment produces no return?
6. Recommend a specific allocation with reasoning. Explicitly name what is being underfunded or deferred and why that tradeoff is acceptable.
</reasoning>
```

### Usage Guidance

Use for budget planning, team allocation, portfolio prioritization, capacity planning, and any task where the core question is "how do we distribute limited resources?" The approach forces explicit tradeoffs rather than allowing the common failure of distributing resources evenly.

### Failure Modes

- **Balanced allocation reflex:** Claude will often recommend a "balanced" allocation that gives something to everyone — which is exactly the failure mode this approach is designed to prevent. If the output avoids hard tradeoffs, add: "This allocation must make clear tradeoffs. A recommendation that funds everything at reduced levels is not a strategy — it is a refusal to prioritize."
- **Missing minimum viable thresholds:** Claude may allocate small amounts to many priorities without considering whether those amounts are above the threshold for producing any return. Step 5 addresses this, but reinforce if outputs spread resources too thin.

### When to Modify

For tasks that involve prioritizing a list of items (features, projects, initiatives) rather than allocating a budget, use Prioritization from `comparative-reasoning.md` instead. For resource allocation decisions that also involve organizational change, combine with Change & Transformation below.

---

## Change & Transformation

**Use when:** The task involves planning or evaluating a significant organizational change — restructuring, process transformation, cultural shift, or strategic pivot. Distinct from general planning because change management involves human resistance, sequencing dependencies, and transition states.

```xml
<reasoning>
Approach this transformation as follows:
1. Define the current state precisely — not just what's wrong, but what's working and what people are attached to. Change that ignores what's valued will face unnecessary resistance.
2. Define the target state with equal precision. What does "done" look like in concrete, observable terms?
3. Map the stakeholders: who gains, who loses, who decides, and who can block? The blockers and losers are more important to plan for than the supporters.
4. Design the transition sequence — what changes first, what depends on what, and where are the points of no return? Identify the minimum set of early changes that create momentum.
5. Identify the highest-risk transition states — periods where the old system is dismantled but the new one isn't yet working. How will you maintain operations during these gaps?
6. Define success metrics that can be measured during the transition, not just after completion. If you can only tell whether the change worked two years later, you need leading indicators.
</reasoning>
```

### Usage Guidance

Use for organizational restructuring, process redesign, technology transformation, cultural change initiatives, strategic pivots, and any task where a group of people must move from one way of working to another. The approach centers on the transition itself — the messy middle — rather than just the target state.

### Failure Modes

- **Operationally naive plans:** Claude may produce a change plan that is logically sound but underestimates resistance, assumes smooth adoption, or misses human dynamics. If the plan lacks realism, add: "Assume that at least one major stakeholder group will resist this change. Build that resistance into your plan rather than assuming it away."
- **Target-state fixation:** Claude may spend most of the analysis defining what "good" looks like and skip the transition planning. The approach's emphasis on transition states (steps 4-5) counters this, but if outputs are heavy on vision and light on execution, strengthen the transition steps.

### When to Modify

For technical migrations specifically (system-to-system), use Migration & Transition from `technical-reasoning.md` instead — it adds rollback strategies, data migration concerns, and coexistence planning specific to technical systems. For changes that require significant resource reallocation, combine with Resource Allocation above.
