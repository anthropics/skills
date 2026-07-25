---
name: rootnode-identity-blocks
description: >-
  Eight tested identity approaches for Claude prompts, each shaping depth,
  vocabulary, reasoning style, and what Claude treats as obvious vs.
  requiring explanation. Use when the user wants a specific identity template
  — retrieving, reviewing, customizing, or building a role definition.
  Trigger on: "give me the Strategic Advisor identity," "show me the identity
  template for," "I need a Technical Architect role," "build a custom role
  for," "show me all available identities." Also use when reviewing a
  prompt's identity layer or when output lacks domain-appropriate depth.
  Provides 8 tested approaches across strategy, technical, research,
  communications, and operations domains plus a template for building custom
  identities. If the user is unsure which identity fits their task, use
  rootnode-block-selection first if available. Do NOT use for evaluating
  complete prompts — use rootnode-prompt-validation if available. Do NOT use
  for full prompt assembly — use rootnode-prompt-compilation if available.
license: Apache-2.0
metadata:
  author: rootnode
  version: "1.1"
  original-source: "BLOCK_LIBRARY_IDENTITY.md"
---

# Identity Approaches for Claude Prompts

> **Calibration:** Tier 1, Opus-primary. See repository README for model compatibility.

Identity is the first layer of a well-structured Claude prompt. It defines WHO Claude is for a task — shaping the depth of analysis, the vocabulary used, the reasoning style applied, and what Claude treats as obvious versus what requires explanation.

A prompt without a clear identity produces generic output. A prompt with the wrong identity produces output that's confident in the wrong domain. Getting the identity right is the single highest-leverage decision in prompt construction.

## When to Use This Skill

- You are building a Claude prompt and need to choose or define a role/persona
- You have a prompt whose output lacks domain-appropriate depth or vocabulary
- You need to decide which expert perspective fits a task
- You want to build a custom identity for a specialized domain

## Choosing the Right Identity

### Quick Selection Table

| If the task involves... | Use this approach |
|---|---|
| Business strategy, competitive dynamics, market opportunity, executive decisions | **Strategic Advisor** |
| System design, infrastructure, migration planning, technical evaluation | **Technical Architect** |
| Evidence review, literature synthesis, data-informed analysis | **Research Synthesist** |
| Process design, workflow optimization, operational efficiency | **Operations Designer** |
| Financial modeling, valuation, investment analysis, budgeting | **Financial Analyst** |
| Product decisions, roadmap planning, feature evaluation, user problems | **Product Strategist** |
| Messaging, positioning, audience analysis, content strategy | **Communications Strategist** |
| Making complex topics accessible, training material, progressive explanation | **Educator / Explainer** |

### Selection Decision Tree

**Step 1 — Is the task about making a decision or producing an artifact?**

If the primary output is a *decision, recommendation, or evaluation*:
- Business/market decision → **Strategic Advisor**
- Technical/architecture decision → **Technical Architect**
- Product/feature decision → **Product Strategist**
- Financial/investment decision → **Financial Analyst**

If the primary output is a *process, system, or workflow*:
- → **Operations Designer**

If the primary output is *synthesized understanding from multiple sources*:
- → **Research Synthesist**

If the primary output is *a message, narrative, or positioning*:
- → **Communications Strategist**

If the primary output is *an explanation or teaching artifact*:
- → **Educator / Explainer**

**Step 2 — Check the audience.**

The identity shapes the output's depth and vocabulary. If the audience differs from what the identity naturally assumes:
- Strategic Advisor assumes executive-level business literacy → add audience constraints for non-business readers
- Technical Architect assumes high technical sophistication → add audience constraints for non-technical stakeholders
- Financial Analyst assumes financial literacy → specify when communicating to non-financial audiences
- Research Synthesist can over-hedge → constrain to reach clear conclusions when needed

**Step 3 — Check for domain specialization.**

These eight approaches are domain-agnostic starting points. For deeper specialization in specific verticals (consulting, M&A, SRE, security, editorial, data analysis, policy research), domain-specific identity approaches are available in the `rootnode-domain-*` skills if installed. Domain approaches extend these core approaches — they do not replace them.

### When Multiple Approaches Seem to Fit

If a task sits at the intersection of two domains, do NOT combine two full identity approaches. Instead:

1. Pick the PRIMARY identity — the one whose reasoning style matters most for the output quality
2. Add domain context from the secondary area as a constraint or context statement
3. Example: A financial analysis of a product decision → use **Financial Analyst** with product context added to the prompt's context layer, not a merged Financial-Product hybrid

### Complete Approach Documentation

Each approach includes the full identity template (ready to paste into a prompt), usage guidance, and specific failure modes to watch for.

- **Strategic approaches:** Strategic Advisor, Financial Analyst, Product Strategist → see `references/strategic-identities.md`
- **Technical approaches:** Technical Architect → see `references/technical-identities.md`
- **Research approaches:** Research Synthesist → see `references/research-identities.md`
- **Communications approaches:** Communications Strategist, Educator / Explainer → see `references/communications-identities.md`
- **Operations approaches:** Operations Designer → see `references/operations-identities.md`

Read the relevant reference file when you need the full identity template text, specific usage guidance, or failure mode documentation for an approach.

## Building Custom Identities

When none of the eight approaches fit, build a custom identity using this template:

```xml
<role>
You are a [SENIORITY] [ROLE] with deep expertise in [DOMAIN 1], [DOMAIN 2], and [DOMAIN 3].

You approach problems by [REASONING STYLE — how you think through issues].

You prioritize [VALUE 1] over [VALUE 2 — the thing you'll sacrifice when there's a tension].

[ONE SENTENCE on your communication style or a behavioral instruction that distinguishes this role from a generic one.]
</role>
```

### Calibration Principles

**Seniority shapes the output.** "Senior" or "principal" produces nuanced analysis with tradeoffs acknowledged. Removing seniority or using "junior" produces more explanatory, step-by-step output. Match seniority to the analytical depth you need, not to the audience's seniority.

**Domain intersections create distinctive thinking.** "Data scientist with supply chain expertise" produces different analysis than either role alone. Use intersections when the task genuinely sits at a crossroads — not as a way to cover more ground.

**Stated values resolve ambiguity.** When Claude faces a tradeoff in the task (thoroughness vs. speed, precision vs. accessibility, innovation vs. safety), the values statement tells it which way to lean. Without this, Claude defaults to optimizing everything simultaneously and producing middling output.

**The behavioral sentence prevents drift.** One concrete instruction about how this role communicates — "You are direct and do not pad analysis with unnecessary caveats" or "You explain your reasoning transparently so others can disagree with your logic, not just your conclusions" — anchors the identity more effectively than additional domain descriptions.

### Common Custom Identity Mistakes

- **Too many domains.** Three is the practical limit. More than three dilutes the identity.
- **No values statement.** Without a clear priority, Claude tries to satisfy every possible objective and produces generic output.
- **Generic behavioral sentence.** "You communicate clearly" adds nothing. Make it specific to a real tension the role faces.
- **Mismatched seniority.** Using "junior" when you need sophisticated tradeoff analysis, or "principal" when you need accessible step-by-step explanation.

## Critical: Identity Is Not Enough

An identity approach defines WHO Claude is. It does not define WHAT Claude should do (objective), WHAT Claude knows (context), HOW Claude should reason (methodology), or WHAT the output looks like (format). A strong identity paired with a vague objective still produces vague output. Always pair identity with clear objective, context, and output instructions.

## Troubleshooting

**Output sounds generic despite having an identity.** The identity is too broad or too similar to Claude's default behavior. Make it more specific — add domain intersections, sharper values, or a behavioral sentence that pushes Claude away from its defaults.

**Output uses wrong vocabulary or depth.** The identity doesn't match the audience. Add explicit audience constraints: who is reading this, what do they already know, what vocabulary is appropriate.

**Claude defaults to frameworks over custom analysis.** Several identities (Strategic Advisor, Product Strategist, Financial Analyst) can push Claude toward standard frameworks. Add a constraint: "Use frameworks only when they genuinely fit the problem. Do not force the analysis into a standard template."

**Claude fabricates specific numbers or statistics.** The Financial Analyst and Research Synthesist identities can trigger confident quantitative claims. Add: "Use only data provided in the context. Where specific numbers are not available, state ranges and label them as estimates."

**Output hedges everything and reaches no conclusion.** The Research Synthesist identity can make Claude overly cautious. Add: "After presenting the evidence fairly, state your assessment clearly. Uncertainty about specific points does not prevent you from reaching a well-reasoned overall conclusion."
