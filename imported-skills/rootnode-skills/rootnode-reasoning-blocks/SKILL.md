---
name: rootnode-reasoning-blocks
description: >-
  Tested reasoning approaches for Claude prompts — 18 variants across 6
  categories (Analytical, Strategic, Creative, Technical, Research,
  Comparative). Use when the user wants a specific reasoning template —
  retrieving, reviewing, customizing, or combining reasoning instructions for
  a prompt. Trigger on: "give me the Root Cause Diagnosis approach," "show me
  the reasoning template for," "I need the Evidence Synthesis method," "show
  me analytical reasoning options," "combine reasoning approaches for," "show
  me all reasoning variants." Also use when a prompt produces shallow output
  and the fix is a reasoning upgrade. Provides 18 tested approaches for
  analytical, strategic, creative, technical, research, and comparison tasks.
  If the user is unsure which reasoning method fits, use
  rootnode-block-selection first if available. Do NOT use for evaluating
  existing prompts — use rootnode-prompt-validation if available. Do NOT use
  for project-level audits — use rootnode-project-audit if available.
license: Apache-2.0
metadata:
  author: rootnode
  version: "1.1"
  original-source: "BLOCK_LIBRARY_REASONING.md"
---

# Reasoning Approach Selection for Claude Prompts

> **Calibration:** Tier 1, Opus-primary. See repository README for model compatibility.

Select the reasoning approach that matches how the task requires Claude to think. The reasoning layer is the highest-leverage component in a prompt — the difference between shallow and deep output almost always traces back to reasoning quality.

## How to Use This Skill

1. Identify the dominant thinking mode the task requires (see the selection guide below).
2. Read the corresponding reference file for that category to find the specific variant that fits.
3. Copy and adapt the reasoning instructions into your prompt.
4. If the task spans categories, see "Combining Reasoning Approaches" below.

## Selection Guide

### Analytical / Evaluative

**Choose when the task requires evaluating, diagnosing, or assessing something that exists.**

| Approach | Best For | Key Differentiator |
|---|---|---|
| General Analysis | Broad evaluation of a situation, opportunity, or problem | Works forward from evidence to conclusions |
| Root Cause Diagnosis | Something is failing or underperforming — find out why | Works backward from symptoms to causes |
| Risk Assessment | Evaluating what could go wrong with a decision or plan | Focuses on failure modes, not current evidence |

**Routing logic:** If the task says "evaluate" or "analyze" → General Analysis. If something is broken or underperforming → Root Cause Diagnosis. If the question is "should we do this?" with emphasis on downside → Risk Assessment.

See `references/analytical-reasoning.md` for complete approaches with usage guidance and failure modes.

### Strategic / Planning

**Choose when the task requires making decisions about direction, resources, or organizational change.**

| Approach | Best For | Key Differentiator |
|---|---|---|
| Market & Competitive Strategy | Evaluating market opportunities and competitive positioning | Centers on competitive dynamics and differentiation |
| Resource Allocation | Distributing limited resources across competing priorities | Centers on scarcity and tradeoffs |
| Change & Transformation | Planning significant organizational or process changes | Centers on transition states and human resistance |

**Routing logic:** If the task involves competitors or market position → Market & Competitive Strategy. If the core tension is "we have X resources and Y demands" → Resource Allocation. If the task involves moving an organization from state A to state B → Change & Transformation.

See `references/strategic-reasoning.md` for complete approaches with usage guidance and failure modes.

### Creative / Generative

**Choose when the task requires generating something new rather than analyzing something that exists.**

| Approach | Best For | Key Differentiator |
|---|---|---|
| Concept Development | Generating a new concept, design, or creative direction | Explores the possibility space, then develops the best direction |
| Messaging & Narrative | Crafting messages, stories, or positioning | Driven by audience psychology and narrative arc |
| Solution Ideation | Creative problem-solving for a defined problem | Problem is known; solution space is open |

**Routing logic:** If the deliverable is a creative concept or design → Concept Development. If the deliverable is a message, story, or narrative → Messaging & Narrative. If there's a defined problem needing creative solutions → Solution Ideation.

See `references/creative-reasoning.md` for complete approaches with usage guidance and failure modes.

### Technical / Problem-Solving

**Choose when the task involves building, fixing, or migrating technical systems.**

| Approach | Best For | Key Differentiator |
|---|---|---|
| System Design | Designing a new system or architecture from requirements | Building something new — key decisions and tradeoffs |
| Debugging & Incident Analysis | Finding and fixing something broken | Hypothesis-driven troubleshooting of existing systems |
| Migration & Transition | Moving from one system or platform to another | Managing the transition while maintaining operations |

**Routing logic:** If building something new → System Design. If something is broken → Debugging & Incident Analysis. If moving between systems → Migration & Transition.

See `references/technical-reasoning.md` for complete approaches with usage guidance and failure modes.

### Research / Synthesis

**Choose when the task requires processing multiple information sources into coherent analysis.**

| Approach | Best For | Key Differentiator |
|---|---|---|
| Evidence Synthesis | Integrating multiple sources into evidence-grounded conclusions | Organizes by theme, discriminates by source quality |
| Landscape Scan | Broad overview of a domain — players, trends, maturity | Optimizes for breadth and orientation, not depth |
| Gap Analysis | Comparing current state vs. desired state | Explicitly comparative framing — what exists vs. what should |

**Routing logic:** If the task is "what does the evidence say about X?" → Evidence Synthesis. If the task is "what's out there in domain X?" → Landscape Scan. If the task is "where do we fall short of target?" → Gap Analysis.

See `references/research-reasoning.md` for complete approaches with usage guidance and failure modes.

### Comparative / Decision-Support

**Choose when the task requires comparing options and making a selection or ranking.**

| Approach | Best For | Key Differentiator |
|---|---|---|
| Option Evaluation | Comparing multiple options against criteria to select one | General-purpose comparison with decisive recommendation |
| Vendor / Tool Selection | Comparing products, vendors, or platforms for adoption | Adds total cost of ownership and integration concerns |
| Prioritization | Ranking a set of items by priority | Produces tiers and sequences, not a single winner |

**Routing logic:** If selecting one option from several → Option Evaluation. If the options are products, tools, or vendors → Vendor / Tool Selection. If ranking a list rather than picking a winner → Prioritization.

See `references/comparative-reasoning.md` for complete approaches with usage guidance and failure modes.

## Combining Reasoning Approaches

Some tasks span multiple categories. When combining, follow these principles:

**Keep the total steps to 5-7.** More than 7 steps and Claude treats each one less carefully. Combine steps from different approaches rather than concatenating entire approaches.

**Lead with the dominant task type.** If it's primarily a strategic decision that needs some technical evaluation, use the strategic reasoning structure and fold in the technical steps — not the other way around.

**Watch for contradictions.** Different approaches sometimes push in opposite directions (e.g., creative approaches say "explore broadly" while analytical approaches say "narrow to the core question"). When combining, make the sequence explicit: "First, explore broadly. Then, evaluate the most promising directions."

### Example: Strategic Decision with Technical Evaluation

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

### Common Combinations

| Task Shape | Lead With | Fold In |
|---|---|---|
| Strategic decision needing technical vetting | Strategic | Technical (feasibility check) |
| Creative concept needing market validation | Creative | Strategic (competitive positioning) |
| Technical design needing business justification | Technical | Analytical (risk + value assessment) |
| Research synthesis needing actionable priorities | Research | Comparative (prioritization) |
| Risk assessment needing root cause depth | Analytical (risk) | Analytical (root cause) |

## Critical: Output Quality

Match reasoning depth to task complexity. A simple comparison needs 4-5 steps, not a 7-step methodology. When the prompt produces shallow output, the fix is usually one of these:

- **Wrong category:** The reasoning approach doesn't match the actual thinking required. Re-read the routing logic above.
- **Too many steps:** Claude spreads attention thin. Cut to the 5 most important steps.
- **Missing context:** The reasoning approach is right, but Claude lacks the domain information to apply it well. The fix is in the context layer of the prompt, not the reasoning layer.
- **Generic output:** Claude is applying the steps mechanically rather than to the specific situation. Add specificity to the prompt's context and identity layers, not more reasoning steps.

## Domain Specialization

The 18 approaches in this Skill are domain-agnostic — they work across contexts. For tasks requiring deeper domain specialization, domain-specific reasoning approaches are available in the rootnode-domain Skills (business strategy, software engineering, content & communications, research & analysis, agentic & context engineering) if installed. Domain approaches extend these core approaches — they do not replace them.

## Troubleshooting

**Output is shallow despite using a reasoning approach:** Check whether the approach category matches the actual thinking required. A strategic task using an analytical approach will produce analysis when you need decisions.

**Claude ignores some reasoning steps:** Too many steps. Cut to 5-7 maximum. Claude gives diminishing attention to steps beyond 7.

**All outputs from this approach look the same:** The reasoning is right but the context is insufficient. Claude needs specific details about the situation to produce specific analysis. Add concrete context to the prompt.

**Claude applies a standard framework instead of thinking specifically:** Some approaches (especially strategic ones) trigger Claude's tendency to apply textbook frameworks (Porter's Five Forces, SWOT, etc.) rather than analyzing the specific situation. Add: "Analyze the specific dynamics of this situation. Do not apply standard frameworks unless they genuinely illuminate the problem."
