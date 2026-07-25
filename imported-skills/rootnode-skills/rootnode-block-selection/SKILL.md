---
name: rootnode-block-selection
description: >-
  Guides selection of identity, reasoning, and output approaches for Claude
  prompts based on task characteristics. Trigger on: "help me choose an
  approach," "which approach fits this task," "recommend a prompt pattern,"
  "compare reasoning methods," "map this task to the right approach," "what
  combination of approaches," "which identity fits," "which reasoning method."
  Also trigger on symptom-phrased: "my prompt feels generic," "I don't know
  which approach to use," "my output lacks domain depth." Covers decision-tree
  logic across 8 identity approaches, 18 reasoning variants, and 10 output
  formats. After selection, use the relevant catalog skill if available to
  retrieve full templates. Activate whenever approach-selection across multiple
  categories is the primary decision. Do NOT use when the user already names a
  specific approach to retrieve (use the relevant catalog skill directly if
  available) or for evaluating existing prompts (use rootnode-prompt-validation
  if available).
license: Apache-2.0
metadata:
  author: rootnode
  version: "1.1.1"
  original-source: "PROMPT_COMPILER.md, BLOCK_LIBRARY_IDENTITY.md, BLOCK_LIBRARY_REASONING.md, BLOCK_LIBRARY_OUTPUT.md"
---

# Approach Selection for Claude Prompts

> **Calibration:** Tier 2, Opus-primary. See repository README for model compatibility.

This Skill provides the decision logic for choosing the right identity, reasoning method, and output format when building a Claude prompt. Given a task description, it maps task characteristics to the best-fit approach in each category.

## When to Use This Skill

Use this when you need to decide:
- Which identity (role) fits a task
- Which reasoning method produces the best analytical depth for the task shape
- Which output format matches the deliverable
- When to combine approaches across categories
- When core approaches are sufficient vs. when domain-specific approaches add value

This Skill provides selection logic and approach summaries. For the full approach text (ready to paste into a prompt), consult the reference files in `references/`.

## Important

**Be decisive.** When one approach is clearly the best fit, recommend it — do not present three options and ask the user to choose unless the options lead to genuinely different outcomes.

**Match complexity to task.** Not every task needs all four selection decisions. A simple task may need only an identity and output format. A medium task adds a reasoning method. Only complex, high-stakes tasks need the full selection plus quality control additions.

**Core approaches cover 80% of tasks.** The 8 identity approaches, 18 reasoning variants, and 10 output formats handle most prompt construction needs. Route to domain-specific approaches only when the task requires specialization the core catalog cannot provide. See the domain routing guidance at the end of this file.

---

## Reasoning discipline

A defensible recommendation shows its work. Observe the task characteristics — task type, depth required, audience, output shape, constraints — then name the approach pattern they match against the decision tree, then apply the selection. Compressing the sequence into a summary recommendation blurs edge cases; the explicit walk-through produces selections the user (and a later reviewer) can interrogate.

If the task scope is unclear (single-prompt selection? multi-block combination? architecture decision?), confirm scope with the user before proceeding. Do not proceed on inferred assumptions.

---

## Step 1: Classify the Task

Before selecting approaches, classify the task using this routing table. When a task matches multiple categories, lead with the dominant one and fold in elements from the secondary.

**Strategic / Advisory** — Business strategy, market entry, competitive analysis, organizational decisions.
Identity: Strategic Advisor or Product Strategist. Reasoning: Market & Competitive Strategy, Resource Allocation, or Change & Transformation. Output: Executive Brief, Strategic Memo, or Decision Matrix.

**Technical / Engineering** — System design, infrastructure, migration planning, technical evaluation.
Identity: Technical Architect. Reasoning: System Design, Debugging & Incident Analysis, or Migration & Transition. Output: Technical Design Document or Implementation Plan.

**Analytical / Evaluative** — Evidence review, data analysis, root cause investigation, risk evaluation.
Identity: Research Synthesist or Financial Analyst. Reasoning: General Analysis, Root Cause Diagnosis, or Risk Assessment. Output: Research Summary, Post-Mortem, or Decision Matrix.

**Creative / Generative** — Concept development, messaging, content creation, narrative design.
Identity: Communications Strategist or custom. Reasoning: Concept Development, Messaging & Narrative, or Solution Ideation. Output: Custom, matched to deliverable type.

**Research / Synthesis** — Literature review, evidence integration, landscape overview.
Identity: Research Synthesist. Reasoning: Evidence Synthesis, Landscape Scan, or Gap Analysis. Output: Research Summary or Competitive Analysis.

**Comparative / Decision** — Option evaluation, vendor selection, prioritization of a set.
Identity: Matched to domain. Reasoning: Option Evaluation, Vendor/Tool Selection, or Prioritization. Output: Decision Matrix or Executive Brief.

**Operational / Process** — Process design, workflow optimization, operational systems.
Identity: Operations Designer. Reasoning: General Analysis or custom. Output: Process Documentation, Implementation Plan, or Stakeholder Update.

**Educational / Explanatory** — Teaching, explaining, training material, progressive understanding.
Identity: Educator/Explainer. Reasoning: Light — focus on progressive complexity. Output: Custom, matched to format (guide, explainer, training material).

---

## Step 2: Select Identity

The identity determines WHO Claude is for the task — shaping depth, vocabulary, reasoning style, and what Claude treats as obvious vs. requiring explanation.

For full approach text and failure modes, see `references/identity-blocks.md`.

### Identity Decision Tree

```
1. What domain is the task in?
   → Business strategy, market analysis, competitive dynamics → Strategic Advisor
   → System design, infrastructure, technical evaluation → Technical Architect
   → Evidence review, data analysis, research synthesis → Research Synthesist
   → Process design, workflow, operational systems → Operations Designer
   → Financial analysis, valuation, investment → Financial Analyst
   → Product decisions, roadmap, feature evaluation → Product Strategist
   → Messaging, positioning, narrative, content → Communications Strategist
   → Teaching, explaining, training material → Educator / Explainer

2. Does the task sit at an intersection of two domains?
   → Yes → Build a hybrid combining the two relevant approaches.
   → No → Use the single best-fit approach.

3. Does the task require a different seniority calibration?
   → Expert audience → Use "principal" or "world-class" — more nuanced,
     assumption-challenging output.
   → Audience needs step-by-step guidance → Reduce seniority — more
     explanatory output.
   → Default → "Senior" is right for most tasks.

4. Does no approach fit at all?
   → Build custom using the template:
     [SENIORITY] [ROLE] with expertise in [DOMAINS].
     Approaches problems by [REASONING STYLE].
     Prioritizes [VALUE 1] over [VALUE 2].
     [ONE BEHAVIORAL SENTENCE].
```

### Identity Calibration Principles

Seniority shapes the output. "Senior" or "principal" produces nuanced analysis with tradeoffs acknowledged. Removing seniority produces more explanatory, step-by-step output. Match seniority to the depth you need.

Domain intersections create distinctive thinking. "Data scientist with supply chain expertise" produces different analysis than either role alone.

Stated values resolve ambiguity. When Claude faces a tradeoff (thoroughness vs. speed, precision vs. accessibility), the values statement tells it which way to lean.

The behavioral sentence prevents drift. One concrete instruction about communication style anchors the identity more than additional domain descriptions.

---

## Step 3: Select Reasoning

The reasoning method controls HOW Claude thinks through the problem — the analytical steps, order of operations, and where attention is directed. This is the highest-leverage selection: the difference between shallow and deep output almost always traces back to reasoning quality.

For full approach text and failure modes, see `references/reasoning-blocks.md`.

### Reasoning Decision Tree

```
1. What is the primary task shape?
   → Evaluate something that exists → Analytical family
   → Plan or decide a strategic direction → Strategic family
   → Generate something new → Creative family
   → Build or fix a technical system → Technical family
   → Synthesize information across sources → Research family
   → Compare options and recommend → Comparative family

2. Within the family, which variant?

   Analytical:
   → General evaluation of a situation → General Analysis
   → Something is failing, find out why → Root Cause Diagnosis
   → Evaluate risks of a decision → Risk Assessment

   Strategic:
   → Market opportunity or competitive positioning → Market & Competitive Strategy
   → Allocate scarce resources across priorities → Resource Allocation
   → Plan a significant organizational change → Change & Transformation

   Creative:
   → Develop a new concept or design → Concept Development
   → Craft a message, story, or positioning → Messaging & Narrative
   → Solve a defined problem creatively → Solution Ideation

   Technical:
   → Design a new system from requirements → System Design
   → Diagnose and fix a broken system → Debugging & Incident Analysis
   → Migrate between systems while maintaining operations → Migration & Transition

   Research:
   → Synthesize findings across multiple sources → Evidence Synthesis
   → Broad overview of a domain → Landscape Scan
   → Compare current state to desired state → Gap Analysis

   Comparative:
   → General comparison of options → Option Evaluation
   → Select a product, vendor, or tool → Vendor / Tool Selection
   → Rank a set of items by priority → Prioritization

3. Does the task span categories?
   → Yes → Combine elements from both families. Keep total steps to 5-7.
     Lead with the dominant task type. Example: a strategic decision
     needing technical feasibility analysis → Strategic reasoning
     with technical evaluation folded into steps 3-4.
```

### Combining Reasoning Approaches

Some tasks span multiple categories. When combining:

**Keep total steps to 5-7.** More than that and Claude treats each step less carefully. Combine steps from different approaches rather than concatenating entire sets.

**Lead with the dominant task type.** If it's primarily strategic with some technical evaluation needed, use the strategic reasoning structure and fold in the technical steps — not the reverse.

**Watch for contradictions.** Different approaches sometimes push in opposite directions (creative says "explore broadly" while analytical says "narrow to the core question"). Make the sequence explicit: "First, explore broadly. Then, evaluate the most promising directions."

---

## Step 4: Select Output Format

The output format controls WHAT the deliverable looks like — structure, sections, length, and format. Without explicit format guidance, Claude defaults to its own preferences, which often means too-long prose with too many bullet points.

For full approach text and failure modes, see `references/output-blocks.md`.

### Output Decision Tree

```
1. What is the deliverable type?
   → Senior leadership decision or board update → Executive Brief
   → Architecture proposal or system design → Technical Design Document
   → Evidence synthesis or research findings → Research Summary
   → Project plan or rollout strategy → Implementation Plan
   → Structured comparison of options → Decision Matrix
   → Market positioning or competitive landscape → Competitive Analysis
   → Incident or project analysis (what happened, why, fix) → Post-Mortem
   → Status report or progress update → Stakeholder Update
   → Strategy recommendation or policy position → Strategic Memo
   → Workflow, runbook, or SOP → Process Documentation

2. Does no approach fit?
   → Build custom using the template:
     [SECTION 1]: (what it contains, length)
     [SECTION 2]: (what it contains, length)
     [SECTION 3]: (what it contains, length)
     Total length, tone, format, audience.

3. Calibration checks:
   → Does the format specify per-section length? (If only total length,
     add section guidance.)
   → Does the format match the audience? (Technical audience → technical
     depth. Executive audience → lead with insight.)
   → Is the total length realistic for the task? (500-word brief on a
     complex topic may be too compressed. 2000-word brief on a simple
     question is bloated.)
```

### Output Design Principles

Lead with what the reader wants most. Executives want the recommendation first. Engineers want the architecture first. Researchers want the findings first.

Specify length per section, not just total. "Bottom Line: 2-3 sentences. Analysis: 3 paragraphs. Next Steps: 3-5 items" allocates Claude's attention correctly.

Constrain the format where it matters. If you want prose, say "write in prose" — otherwise Claude defaults to bullet points. If you want a table, specify column names.

Name sections descriptively. "Analysis" is vague. "Competitive Assessment" or "Root Cause Analysis" tells Claude what belongs there.

---

## Step 5: Select Quality Control

Quality control additions are layered on top of the standard quality checks (accuracy, completeness, assumptions, pushback permission, actionability).

### Quality Control Decision Tree

```
1. Always include the standard quality checks:
   - Accuracy: Verify claims against available evidence
   - Completeness: Address all dimensions of the task
   - Assumptions: Make assumptions explicit
   - Pushback: Challenge flawed premises before proceeding
   - Actionability: Ensure recommendations can be acted on

2. Add task-specific quality checks based on domain:
   → Strategic work → Internal consistency check (recommendations
     don't contradict each other)
   → Technical work → Edge case identification (at least two failure
     modes addressed)
   → Research work → Source discrimination (not all sources treated
     as equally reliable)
   → Creative work → Distinctiveness check (output is not generic /
     could-apply-to-anyone)
   → Financial work → Assumption transparency (all numbers sourced
     or labeled as estimates)
   → Advisory work → Agreeableness counter (challenge flawed premises
     before proceeding)

3. Add behavioral countermeasures based on likely tendencies:
   → Task invites agreement with user's framing → Add pushback permission
   → Task invites hedging (ambiguous evidence, contested topic) → Add
     decisiveness instruction
   → Task is long-form → Add length constraint and verbosity counter
   → Task could produce lists → Add prose instruction if prose is
     more appropriate
```

---

## Domain Specialization Routing

The core catalog (8 identity approaches, 18 reasoning variants, 10 output formats) handles most tasks. Route to domain-specific approaches only when the task requires depth the core catalog cannot provide.

For a summary of what each domain pack adds and when to route there, see `references/domain-pack-index.md`.

### When Core Approaches Are Sufficient

- The task fits cleanly into one of the eight task categories above
- The deliverable matches one of the ten output formats
- The analytical depth needed is general, not domain-specialized
- The audience does not require domain-specific terminology or conventions

### When Domain Specialization Adds Value

- The task requires specialized identity framing (e.g., SRE engineer, M&A advisor, policy analyst) that the core approaches approximate but don't fully capture
- The reasoning method needs domain-specific analytical steps (e.g., due diligence methodology, threat modeling, systematic review protocol)
- The deliverable follows a domain convention (e.g., RFC, ADR, policy brief, content brief) not covered by the core output formats
- The task's failure modes require domain-specific behavioral countermeasures

### Domain Routing Signals

- Consulting, M&A, corporate strategy, board-level decisions → Business Strategy pack
- Reliability engineering, security, technical leadership, engineering deliverables → Software Engineering pack
- Content creation, editorial, copywriting, messaging → Content & Communications pack
- Quantitative analysis, policy research, investigation, systematic review → Research & Analysis pack
- Agent system design, tool interfaces, context architecture, multi-agent systems → Agentic & Context pack

---

## Examples

### Example 1: Simple Task

User says: "Write a professional email declining a vendor's proposal."

Selection:
- Task category: Operational (simple communication task)
- Complexity: Simple — needs 2-3 layers, not the full treatment
- Identity: Communications Strategist (light version — brief role statement for professional communication)
- Reasoning: None needed — a brief inline instruction ("Be direct but courteous. Lead with the decision.") suffices
- Output: Custom — email structure with tone guidance
- Quality control: None beyond defaults
- Domain specialization: Not needed

### Example 2: Medium Task

User says: "Evaluate three cloud providers for our migration."

Selection:
- Task category: Comparative / Decision with Technical elements
- Complexity: Medium — needs 4-5 layers
- Identity: Technical Architect
- Reasoning: Vendor / Tool Selection
- Output: Decision Matrix
- Quality control: Standard + "Distinguish between vendor claims and demonstrated capabilities"
- Domain specialization: Software Engineering pack would add depth if available, but core approaches handle this adequately

### Example 3: Complex Task

User says: "Develop a market entry strategy for our AI product in the healthcare vertical."

Selection:
- Task category: Strategic / Advisory (primary) with Research elements (secondary)
- Complexity: Complex — full 5 layers plus quality control additions
- Identity: Strategic Advisor
- Reasoning: Market & Competitive Strategy with Resource Allocation elements
- Output: Strategic Memo
- Quality control: Standard + internal consistency check + pushback permission + agreeableness counter
- Domain specialization: Business Strategy pack would add depth (specialized identity, due diligence reasoning, market entry output format)

---

## Troubleshooting

**Selection feels uncertain between two identity approaches.** Build a hybrid. Domain intersections produce distinctive thinking. Use the custom template to combine elements from both.

**Task doesn't fit any reasoning family.** Check whether the task is actually two tasks. If it genuinely spans categories, combine reasoning approaches (keeping to 5-7 total steps). If it's a novel task shape, build custom reasoning by identifying the 5-6 analytical steps that would produce the best output.

**Output format is too rigid for the deliverable.** Use the custom output template. The named formats are starting points — adjust section names, lengths, and constraints to fit the actual deliverable.

**Everything points to domain specialization but no domain pack is available.** The core approaches still work — they produce competent output without the domain-specific depth. Note in your delivery that a domain-specialized version would add value.
