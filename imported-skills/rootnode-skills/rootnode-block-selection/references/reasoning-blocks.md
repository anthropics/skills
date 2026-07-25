# Reasoning Approaches

Eighteen tested reasoning approaches across six categories. Each controls HOW Claude thinks through a problem — the analytical steps, order of operations, and where to direct attention. This is the highest-leverage selection: the difference between shallow and deep output almost always traces back to reasoning quality.

Select the approach matching the task category, then look at the variants for a more specific fit. If the task spans categories, combine elements from multiple approaches — keeping total steps to 5-7.

---

## Contents

1. Analytical / Evaluative — General Analysis, Root Cause Diagnosis, Risk Assessment
2. Strategic / Planning — Market & Competitive Strategy, Resource Allocation, Change & Transformation
3. Creative / Generative — Concept Development, Messaging & Narrative, Solution Ideation
4. Technical / Problem-Solving — System Design, Debugging & Incident Analysis, Migration & Transition
5. Research / Synthesis — Evidence Synthesis, Landscape Scan, Gap Analysis
6. Comparative / Decision-Support — Option Evaluation, Vendor / Tool Selection, Prioritization
7. Combining Reasoning Approaches

---

## 1. Analytical / Evaluative

### General Analysis

**Use when:** Thorough evaluation of a situation, opportunity, or problem. The default for most analytical tasks.

```xml
<reasoning>
Approach this analysis as follows:
1. State the core question you are answering before beginning analysis.
2. Identify the key assumptions embedded in the problem. Test each — which are well-supported, which are fragile?
3. Examine the evidence. Distinguish between strong signals and noise. Flag where data is insufficient.
4. Consider at least one alternative interpretation of the same evidence.
5. Draw conclusions proportional to the strength of the evidence. Do not overstate.
6. Identify what would change your conclusion if it turned out differently.
</reasoning>
```

**Watch for:** Claude may spend too much time on assumption-testing and produce a long preamble before actual analysis. If assumptions are straightforward, trim to focus on steps 3-6.

---

### Root Cause Diagnosis

**Use when:** Something is failing or underperforming and you need to find out why. Works backward from symptoms to causes rather than forward from evidence to conclusions.

```xml
<reasoning>
Approach this diagnosis as follows:
1. List the observable symptoms — what is actually happening vs. what should be happening? Be precise about the gap.
2. Map the causal chain backward: for each symptom, what are the possible immediate causes? For each cause, what could produce it?
3. Identify where multiple symptom chains converge on the same root cause — convergence points are the highest-probability explanations.
4. Test your leading hypothesis: if this root cause were fixed, would it explain all (or most) of the symptoms? Which symptoms would remain unexplained?
5. Identify the simplest intervention that addresses the root cause, not the symptoms.
6. Flag any symptoms that your root cause does not explain — these may indicate a second, independent problem.
</reasoning>
```

**Watch for:** Claude may identify a root cause that is actually just restating the symptom at a higher level of abstraction ("the root cause of low engagement is that users aren't engaged"). Push for specificity — the root cause must be concrete enough that someone could design an intervention to address it directly.

---

### Risk Assessment

**Use when:** Evaluating risks of a decision, project, or course of action. Focuses on what could go wrong and how to prepare, not on what the evidence currently shows.

```xml
<reasoning>
Approach this risk assessment as follows:
1. Identify the decision or action being evaluated. State the expected outcome if everything goes well.
2. List the material risks — things that could prevent the expected outcome or create significant negative consequences. Prioritize by impact, not just likelihood.
3. For each risk, assess: How likely is it? How severe is the impact if it occurs? How early would we detect it? Can it be mitigated, transferred, or must it be accepted?
4. Identify risk interactions — which risks compound each other or share a common trigger? A scenario where two moderate risks hit simultaneously may be worse than either alone.
5. Distinguish between risks you can influence and risks that are external. Focus mitigation efforts on the ones you can influence.
6. Produce a clear risk profile: what is the overall risk level, what are the top 3 risks that need active management, and what is the recommended risk posture (proceed, proceed with safeguards, delay until resolved, or abandon)?
</reasoning>
```

**Watch for:** Claude tends to generate long, undifferentiated lists of risks. If output is still a laundry list despite the prioritization instruction, add: *"Limit your assessment to the 5 most material risks. If a risk would not change the decision, it does not belong in this assessment."*

---

## 2. Strategic / Planning

### Market & Competitive Strategy

**Use when:** Evaluating a market opportunity, competitive positioning, or strategic direction where competitive dynamics matter.

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

**Watch for:** Claude may default to Porter's Five Forces or other standard frameworks even when they don't fit. If output reads like a textbook analysis, add: *"Analyze the specific competitive dynamics of this market. Do not apply standard frameworks unless they genuinely illuminate the situation."*

---

### Resource Allocation

**Use when:** Deciding how to distribute limited resources (budget, people, time, attention) across competing priorities. The core tension is scarcity, not direction.

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

**Watch for:** Claude will often recommend a "balanced" allocation that gives something to everyone — exactly the failure mode this approach is designed to prevent. If output avoids hard tradeoffs, add: *"This allocation must make clear tradeoffs. A recommendation that funds everything at reduced levels is not a strategy — it is a refusal to prioritize."*

---

### Change & Transformation

**Use when:** Planning or evaluating a significant organizational change — restructuring, process transformation, cultural shift, or strategic pivot. The core challenge is human resistance, sequencing dependencies, and transition states.

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

**Watch for:** Claude may produce a change plan that is logically sound but operationally naive — underestimating resistance. If the plan lacks realism, add: *"Assume that at least one major stakeholder group will resist this change. Build that resistance into your plan rather than assuming it away."*

---

## 3. Creative / Generative

### Concept Development

**Use when:** Generating something new — a concept, design, approach, or creative work — rather than analyzing something that exists.

```xml
<reasoning>
Approach this creatively:
1. Before committing to a direction, explore the possibility space. What are the distinct angles, framings, or entry points? Generate at least three that are structurally different, not variations of one idea.
2. For each direction, articulate what makes it interesting or distinctive — what would it enable that the others wouldn't?
3. Select the strongest direction. Develop it with specificity and craft, not just a sketch.
4. Revisit the other directions: are there elements that would strengthen the chosen concept? The best creative work often combines insights from multiple starting points.
5. Stress-test the developed concept: where is it weakest? What would someone who doesn't like it point to? Strengthen those points or acknowledge them as intentional tradeoffs.
</reasoning>
```

**Watch for:** Claude may generate three "different" directions that are actually surface variations of the same idea. If brainstorming feels homogeneous, add: *"Each direction must have a structurally different premise — not just a different framing of the same idea."*

---

### Messaging & Narrative

**Use when:** Crafting a message, story, positioning, or narrative arc where sequence, framing, and audience psychology matter.

```xml
<reasoning>
Approach this narratively:
1. Start with the audience. What do they currently believe about this topic? What do they need to believe? What is the gap between those two states?
2. Identify the single most important idea to land. If the audience remembers only one thing, what should it be?
3. Design the narrative arc: what is the hook that earns attention, the progression that builds understanding, and the conclusion that drives the desired response?
4. Choose the framing deliberately. The same facts can be framed as opportunity or threat, evolution or revolution, correction or innovation. Which framing best serves the objective?
5. Test for internal coherence: does every element of the message support the core idea, or are there tangents that dilute it? Cut what doesn't serve the through-line.
</reasoning>
```

**Watch for:** Can produce messaging that is well-structured but generic — could apply to any company or product. The cure is rich context with specific audience details, competitive positioning, and brand voice.

---

### Solution Ideation

**Use when:** Generating potential solutions to a defined problem — creative problem-solving where the problem is specified but the solution space is open.

```xml
<reasoning>
Approach this problem-solving creatively:
1. Restate the problem in its most fundamental form. Strip away assumptions about solution type — what is the actual need, constraint, or gap?
2. Identify what conventional solutions look like and why they might be insufficient. Understanding the limits of obvious approaches opens space for better ones.
3. Generate solutions across different categories: a technology solution, a process solution, a people/organizational solution, and a reframing that dissolves the problem rather than solving it.
4. Evaluate each solution against the actual constraints (not just feasibility, but effort, risk, time-to-value, and sustainability).
5. Identify whether a hybrid approach — combining elements of different solutions — outperforms any single approach.
6. Recommend the solution with the best tradeoff profile for the stated constraints.
</reasoning>
```

**Watch for:** Claude may anchor too heavily on the first solution category explored and generate "variations" rather than genuinely different approaches. If output feels narrow, add: *"I need genuinely different solution types, not variations within one type."*

---

## 4. Technical / Problem-Solving

### System Design

**Use when:** Designing a system, architecture, or technical solution from requirements. Building something new, not fixing something broken.

```xml
<reasoning>
Approach this design as follows:
1. Clarify the requirements: what must the system do (functional), how must it perform (non-functional), and what constraints exist (team, budget, timeline, existing systems)?
2. Identify the key architectural decisions — the choices that are expensive to change later. Focus your analysis on these, not on implementation details that can be adjusted.
3. For each key decision, evaluate at least two viable approaches. State the tradeoffs explicitly: what does each approach optimize for, and what does it sacrifice?
4. Design for the failure modes, not just the happy path. How does the system behave when components fail, when load exceeds expectations, when bad data enters the pipeline?
5. Consider operational reality: who maintains this system? How is it monitored, deployed, and debugged? A design that is elegant but un-debuggable is a bad design.
6. Present your recommended architecture with clear reasoning for each major decision. Flag decisions that depend on assumptions the stakeholders should validate.
</reasoning>
```

**Watch for:** Claude may over-engineer — proposing distributed systems for problems a single database could solve. Add context about team size and scale. Also watch for descriptions that omit data flow — add: *"Trace the primary data flows from input to output. The architecture must make data movement explicit."*

---

### Debugging & Incident Analysis

**Use when:** Something is broken, failing, or behaving unexpectedly. Hands-on technical troubleshooting, distinct from root cause diagnosis (which is analytical, not hands-on).

```xml
<reasoning>
Approach this debugging as follows:
1. Reproduce the problem statement precisely. What is the expected behavior? What is the actual behavior? What are the exact conditions under which it occurs?
2. Narrow the scope. What has changed recently? What works correctly and bounds the problem area? Use working subsystems to isolate where the failure occurs.
3. Form a hypothesis for the most likely cause based on the symptoms and the narrowed scope. What specific evidence would confirm or eliminate this hypothesis?
4. Test the hypothesis. If confirmed, verify that the fix addresses the root cause and does not introduce new issues. If eliminated, what does the test result tell you about the actual cause?
5. Before implementing a fix, identify: Does this fix handle edge cases? Could this bug exist elsewhere in similar code? Is this a symptom of a systemic issue that needs a broader fix?
</reasoning>
```

**Watch for:** Claude may jump to a solution before properly diagnosing, especially if symptoms resemble a common problem. If you see premature conclusions, add: *"Do not propose a fix until you have identified the specific mechanism causing the failure."*

---

### Migration & Transition

**Use when:** Moving from one system, platform, or architecture to another while maintaining operations. The core challenge is the transition, not the target state.

```xml
<reasoning>
Approach this migration as follows:
1. Map the current state comprehensively: what exists, what depends on what, and what implicit behaviors or undocumented features are in play? Migrations fail most often because of things the team didn't know the old system was doing.
2. Define the target state and the delta — what is genuinely changing vs. what is being replicated in a new environment?
3. Design the migration path: can this be done incrementally (component by component) or must it be a cutover? Incremental is almost always safer — identify what prevents it and whether those barriers can be removed.
4. Identify the rollback strategy for each phase. A migration without a rollback plan is a one-way bet. If rollback is impossible at certain stages, those stages need extra validation.
5. Define the validation criteria — how do you know each phase succeeded before proceeding to the next? What data consistency checks, functional tests, and performance benchmarks must pass?
6. Plan for the transition period when both systems coexist. How is data synchronized? How are users routed? What happens to in-flight transactions?
</reasoning>
```

**Watch for:** Claude may underestimate data migration complexity. If the migration involves significant data, add: *"Pay special attention to data migration: schema differences, data quality issues, referential integrity across systems, and the strategy for handling data that doesn't map cleanly to the new schema."*

---

## 5. Research / Synthesis

### Evidence Synthesis

**Use when:** Multiple sources of information need to be synthesized into a coherent, evidence-grounded analysis that goes beyond summarizing each source individually.

```xml
<reasoning>
Approach this synthesis as follows:
1. Identify the key themes, patterns, or findings that emerge across the available information. Organize by theme, not by source.
2. Note where sources agree and where they conflict. Conflicts are often the most informative — they may indicate nuance, changing conditions, or differences in methodology.
3. Assess the quality and reliability of each source. Not all evidence is equal — consider methodology, recency, potential bias, and whether the source is primary or secondary.
4. Synthesize a coherent picture that integrates the strongest evidence. Clearly distinguish between what is well-established, what is likely, and what is speculative.
5. Identify the most important gaps — what do we not know that would matter most for the decision at hand?
</reasoning>
```

**Watch for:** Claude may give equal weight to all sources rather than discriminating by quality. If sources vary significantly in reliability, add specific guidance: *"Prioritize [primary research / peer-reviewed sources / first-party data] over [secondary analysis / opinion / anecdotal reports]."*

---

### Landscape Scan

**Use when:** A broad overview of a domain — what exists, who the players are, what the trends are — rather than a deep dive into a specific question. The goal is breadth and orientation, not depth and conclusion.

```xml
<reasoning>
Approach this landscape scan as follows:
1. Define the boundaries of the landscape. What is in scope and what is adjacent-but-out-of-scope? Without boundaries, landscape scans expand indefinitely.
2. Map the major categories or segments within the landscape. What are the natural groupings that help organize a complex space?
3. For each segment, identify: the key players or approaches, the current state of maturity, and the direction of movement (growing, stable, declining, or consolidating).
4. Identify the cross-cutting trends that affect multiple segments — these are often more important than developments within any single segment.
5. Highlight the 2-3 most significant developments or emerging patterns that the audience should pay attention to. Not everything in the landscape is equally important.
</reasoning>
```

**Watch for:** Claude may produce a comprehensive but flat scan where everything gets equal treatment. If output lacks a point of view, add: *"After mapping the landscape, identify the 2-3 findings most significant for [our specific situation/decision]. Tell me what matters most."*

---

### Gap Analysis

**Use when:** Comparing a current state against a desired state and identifying what's missing. The framing is explicitly comparative — what exists vs. what should exist.

```xml
<reasoning>
Approach this gap analysis as follows:
1. Define the desired state precisely. What does "good" look like in concrete, measurable terms? Vague target states produce vague gap analyses.
2. Assess the current state with equal precision. Use the same dimensions and metrics as the desired state to make comparison direct.
3. Identify the gaps — where does current state fall short of desired state? Size each gap: is it a minor shortfall or a fundamental absence?
4. Prioritize the gaps by impact: which gaps, if closed, would produce the most significant improvement? Not all gaps are equally important.
5. For each priority gap, identify the most likely root cause and what it would take to close it (effort, time, resources, prerequisites).
6. Distinguish between gaps that can be closed incrementally and gaps that require a step change. This affects the implementation approach.
</reasoning>
```

**Watch for:** Claude may identify gaps that are real but irrelevant to current priorities. Add context about strategic priorities so the analysis stays focused on what matters.

---

## 6. Comparative / Decision-Support

### Option Evaluation

**Use when:** Comparing multiple options against defined criteria and recommending one. The general-purpose comparison approach.

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

**Watch for:** Claude may default to a balanced "all have pros and cons" analysis that avoids recommending. If output still hedges, add: *"Make a decisive recommendation. If you cannot distinguish between the top options on available information, state specifically what information would enable a decision."*

---

### Vendor / Tool Selection

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

**Watch for:** Claude may produce a comparison based on publicly available feature lists rather than practical experience. Add: *"Distinguish between vendor claims and demonstrated capabilities. Where your comparison is based on vendor documentation rather than validated performance, flag this."*

---

### Prioritization

**Use when:** Ranking a set of items (features, projects, initiatives, issues) by priority. Ranking a list rather than selecting one winner.

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

**Watch for:** Claude may resist giving low priority to items that seem important in isolation. If everything ends up in the "important" tier, add: *"This prioritization must identify items that will not be done in the near term. A prioritization that puts everything in the top two tiers is not a prioritization."*

---

## 7. Combining Reasoning Approaches

Some tasks span multiple categories. When combining:

**Keep total steps to 5-7.** More than that and Claude treats each step less carefully. Combine steps from different approaches rather than concatenating entire sets.

**Lead with the dominant task type.** If it's primarily a strategic decision that needs some technical evaluation, use the strategic reasoning structure and fold in the technical steps — not the other way around.

**Watch for contradictions.** Different approaches sometimes push in opposite directions (creative says "explore broadly" while analytical says "narrow to the core question"). Make the sequence explicit: "First, explore broadly. Then, evaluate the most promising directions."

**Example — Strategic Decision with Technical Evaluation:**

```xml
<reasoning>
1. Define the strategic objective and the constraints that bound the decision.
2. Generate 3 structurally different approaches to achieving the objective.
3. For each approach, evaluate the technical feasibility: can our team build this with available resources and timeline? What are the technical risks?
4. Assess each approach against the strategic criteria: competitive positioning, resource efficiency, and alignment with stated priorities.
5. Identify second-order consequences — what does each approach enable or prevent later?
6. Recommend the approach with the best combined strategic-technical tradeoff profile.
</reasoning>
```
