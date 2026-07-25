# Comparative / Decision-Support Reasoning Approaches

Three approaches for tasks that require comparing options and making a selection or ranking. Each addresses a different comparison structure: general option evaluation, specialized product/vendor selection, or ordered prioritization of a list.

---

## Option Evaluation

**Use when:** You need to compare multiple options against defined criteria and recommend one. The general-purpose comparison approach.

```xml
<reasoning>
Approach this comparison as follows:
1. Define the evaluation criteria before comparing. What dimensions matter, and how should they be weighted? Get agreement on criteria before evaluating options — otherwise, criteria get chosen to justify a preferred option.
2. Evaluate each option against every criterion consistently. Do not evaluate Option A on one set of dimensions and Option B on another.
3. Identify where the options are functionally equivalent — do not manufacture differences where none exist.
4. Identify where the options genuinely diverge and articulate why the difference matters for this specific situation.
5. Assess the risks specific to each option — not just "which is best on the criteria" but "what could go wrong with each."
6. Make a clear recommendation with explicit reasoning. If the top options are very close, say so and identify what additional information would break the tie.
</reasoning>
```

### Usage Guidance

Use for any task that involves choosing between alternatives: strategic options, design approaches, process alternatives, partnership options, and general decision-making. The approach enforces consistent evaluation and pushes for a decisive recommendation.

### Failure Modes

- **Balanced non-recommendation:** Claude may default to a "balanced" analysis that avoids recommending — "all have pros and cons." The approach pushes for a clear recommendation, but if the output still hedges, add: "Make a decisive recommendation. If you cannot distinguish between the top options on available information, state specifically what information would enable a decision."
- **Inconsistent evaluation:** Claude may evaluate options using different dimensions or different levels of detail, making comparison difficult. Step 2 addresses this, but reinforce if needed: "Use a consistent evaluation framework for every option. Each option must be assessed on every criterion."

### When to Modify

For product or vendor comparisons specifically, use Vendor / Tool Selection below — it adds total cost of ownership and integration considerations. For comparisons involving more than 5 options, add a screening step before detailed evaluation: "First, screen out any options that fail a must-have requirement. Then evaluate the survivors in detail."

---

## Vendor / Tool Selection

**Use when:** Comparing specific products, vendors, platforms, or tools for a purchase or adoption decision. Specialized version of option evaluation with emphasis on practical adoption concerns.

```xml
<reasoning>
Approach this selection as follows:
1. Define the must-have requirements (non-negotiable) separately from the nice-to-have requirements. Eliminate any option that fails a must-have before detailed comparison.
2. For surviving options, evaluate against the nice-to-have criteria with attention to how each option will work in your specific environment — not just feature-list comparison.
3. Assess the total cost of ownership, not just the purchase price. Include implementation effort, training, migration cost, ongoing maintenance, and cost of switching away later.
4. Evaluate the vendor / project trajectory: is this vendor growing and investing, stable, or declining? For open-source tools: is the community healthy and the project actively maintained?
5. Identify integration and compatibility concerns specific to your existing stack. A tool that's excellent in isolation but creates integration headaches may cost more than a slightly weaker tool that fits cleanly.
6. Recommend a selection with reasoning. If the decision depends on factors you don't have visibility into, name those factors explicitly.
</reasoning>
```

### Usage Guidance

Use for SaaS tool selection, platform adoption decisions, vendor evaluations, technology stack choices, and any task where you're choosing a product or service to adopt. The approach goes beyond feature comparison to address total cost of ownership, vendor trajectory, and integration reality.

### Failure Modes

- **Feature-list comparison:** Claude may produce a comparison that looks thorough but is based on publicly available feature lists rather than practical experience. It can describe what vendors claim but not how tools actually perform in use. Add: "Distinguish between vendor claims and demonstrated capabilities. Where your comparison is based on vendor documentation rather than validated performance, flag this."
- **Missing switching costs:** Claude may underweight the cost of switching away from a chosen tool later. Step 3 addresses this with "cost of switching away," but reinforce if the decision involves significant lock-in: "Assess the lock-in risk for each option. How difficult and expensive would it be to switch away in 2-3 years?"

### When to Modify

For enterprise purchases that involve procurement processes, add a step on procurement considerations: "Identify procurement requirements (security review, legal review, compliance certifications) and assess each option's readiness." For comparisons involving open-source vs. commercial options, strengthen step 4 to address the different risk profiles of each model.

---

## Prioritization

**Use when:** You have a set of items (features, projects, initiatives, issues) and need to rank them by priority. Distinct from option evaluation because you're ranking a list rather than selecting one winner.

```xml
<reasoning>
Approach this prioritization as follows:
1. Define the prioritization criteria. Common dimensions include: impact (how much value does this produce?), effort (how much does this cost to implement?), urgency (is there a time constraint?), and dependency (does something else require this first?).
2. Score each item against the criteria. Use the same scale consistently. Where you lack data for precise scoring, use relative ranking (higher/lower than) rather than fabricating precision.
3. Identify dependencies and sequencing constraints — some items must come before others regardless of their individual priority score.
4. Look for natural tiers rather than a strict linear ranking. "These 3 are critical, these 5 are important, these 4 can wait" is more useful than a forced 1-through-12 ranking where positions 6 and 7 are essentially equivalent.
5. Identify the top tier items and validate: if we could only do these and nothing else, would the outcome be acceptable? If not, something important is missing from the top tier.
</reasoning>
```

### Usage Guidance

Use for feature prioritization, project portfolio ranking, backlog grooming, initiative sequencing, issue triage, and any task where a list of items needs to be ordered by importance. The approach produces natural tiers with dependency awareness rather than an artificially precise linear ranking.

### Failure Modes

- **Everything is high priority:** Claude may resist giving low priority to items that seem important in isolation. The approach's emphasis on tiers rather than linear ranking helps, but if everything ends up in the "important" tier, add: "This prioritization must identify items that will not be done in the near term. A prioritization that puts everything in the top two tiers is not a prioritization."
- **Fabricated precision:** Claude may assign precise numerical scores (7.3 vs 7.1) to items that don't have enough data to support that level of granularity. Step 2 addresses this with the relative ranking instruction, but reinforce if you see false precision: "Use relative rankings (high/medium/low) rather than precise scores unless you have data to support the precision."

### When to Modify

For prioritization that must account for resource constraints, combine with Resource Allocation from `strategic-reasoning.md` — prioritization determines what's most important; resource allocation determines what's feasible given constraints. For technical prioritization (bug triage, tech debt), add domain-specific criteria: "Include technical risk and system stability impact as prioritization criteria."
