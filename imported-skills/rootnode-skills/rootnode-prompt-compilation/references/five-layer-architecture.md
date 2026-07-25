# Five-Layer Architecture Reference

Detailed descriptions, templates, ready-to-use approaches, and design principles for each layer of the prompt architecture. Consult this when you need layer-specific guidance beyond what the core workflow provides.

## Table of Contents

1. Layer 1 — Identity
2. Layer 2 — Objective
3. Layer 3 — Context (includes Context Engineering Toolkit)
4. Layer 4 — Reasoning
5. Layer 5 — Output
6. Quality Control (cross-cutting)
7. Assembly Principles
8. Global Layer Interaction (Project Mode)

---

## Layer 1 — Identity

**Purpose:** Defines the expert role Claude adopts, which shapes depth, vocabulary, reasoning style, and what Claude treats as obvious vs. requiring explanation.

### Why Identity Matters

Claude calibrates responses based on the expertise it embodies. A "senior systems architect" produces different reasoning than a "technical writer" on the same topic — not just in tone, but in what gets analyzed, what assumptions are made, and what gets flagged as important.

### Template

```xml
<role>
You are a [SENIORITY LEVEL] [EXPERT ROLE] with deep expertise in [DOMAIN 1], [DOMAIN 2], and [DOMAIN 3].

You approach problems using [REASONING STYLE — e.g., structured analysis, first-principles thinking, empirical evidence].

You prioritize [KEY VALUES — e.g., practical implementability over theoretical elegance, clarity over completeness].
</role>
```

### Calibration Notes

- **Seniority matters.** "Senior" or "world-class" produces more nuanced, qualified analysis. "Junior" produces more explanatory, step-by-step output. Match seniority to the audience.
- **Multiple domains create intersection thinking.** A "data scientist with supply chain expertise" reasons differently than either role alone.
- **Values shape tradeoffs.** Stating what the role prioritizes prevents Claude from optimizing for the wrong dimension.

### Ready-to-Use Identity Approaches

**Strategic Advisor:**
```xml
<role>
You are a senior strategy consultant who has spent 15 years advising Fortune 500 companies on operational transformation. You think in frameworks, pressure-test assumptions, and always connect recommendations to measurable business outcomes. You are direct and do not pad analysis with unnecessary caveats.
</role>
```

**Technical Architect:**
```xml
<role>
You are a principal software architect specializing in distributed systems and cloud infrastructure. You evaluate solutions against scalability, maintainability, and operational cost. You prefer proven patterns over novel approaches unless the novel approach has a clear, quantifiable advantage.
</role>
```

**Research Synthesist:**
```xml
<role>
You are a senior research analyst trained in evidence synthesis. You distinguish between strong evidence and weak evidence, identify gaps in available data, and present findings with appropriate confidence levels. You never overstate what the evidence supports.
</role>
```

**Educator / Explainer:**
```xml
<role>
You are an expert educator who specializes in making complex topics accessible without sacrificing accuracy. You use concrete examples, analogies, and progressive complexity — starting simple and building up. You check for understanding by anticipating common misconceptions.
</role>
```

**Custom Identity Template:**
When no predefined role fits, build a custom identity:
```
[SENIORITY] [ROLE] with expertise in [DOMAINS].
Approaches problems by [REASONING STYLE].
Prioritizes [VALUE 1] over [VALUE 2].
[ONE BEHAVIORAL SENTENCE].
```

---

## Layer 2 — Objective

**Purpose:** Defines the task precisely enough that success can be evaluated. A good objective removes ambiguity about what "done" looks like.

### The Objective Clarity Test

Before using an objective, ask: "Could two different people read this and produce substantially different outputs?" If yes, it needs refinement.

**Weak:** "Analyze our marketing strategy."
**Strong:** "Identify the three highest-leverage changes to our current content marketing strategy that could increase qualified lead generation within 90 days, given our constraint of a two-person content team."

### Template

```xml
<objective>
Your task is to [SPECIFIC ACTION VERB] a [DELIVERABLE TYPE] that [DEFINES SUCCESS CRITERIA].

Focus on [PRIMARY DIMENSION] while accounting for [SECONDARY CONSTRAINTS].

The output will be used by [AUDIENCE] to [WHAT THEY'LL DO WITH IT].
</objective>
```

### Key Elements

- **Action verb:** analyze, design, evaluate, synthesize, compare, recommend, draft, debug. Avoid vague verbs like "explore" or "think about."
- **Success criteria:** what makes the output good vs. mediocre. Include whenever possible.
- **Audience:** who will read this shapes depth, jargon level, and what needs explaining.
- **Constraints:** what boundaries exist (time, budget, team size, technical stack, etc.).

---

## Layer 3 — Context

**Purpose:** Provides the background information Claude needs to produce relevant, grounded output. Specific context produces specific output. Vague context produces generic output.

### What to Include

- **Situational context:** What is happening, what led to this point, what is at stake.
- **Constraints and boundaries:** Budget, timeline, team, technical limitations, regulatory requirements.
- **Prior decisions:** What is already decided or tried, so Claude does not re-litigate settled questions.
- **Data and reference material:** Numbers, documents, prior analysis — the more specific, the better.

### Template

```xml
<context>
Background:
[Describe the situation, what is happening, and why this task matters now.]

Constraints:
[List real-world limitations — budget, timeline, team size, technical stack, regulatory, etc.]

Prior decisions:
[What has already been decided. What has been tried and failed. What is off the table.]

Key data:
[Relevant numbers, benchmarks, or reference points.]
</context>
```

### Context Engineering Toolkit

Three tools for ensuring context quality.

#### Tool 1: Context Elicitation Checklist

Scan for the task category and include every element available. Not all are required — every element included makes the output more specific.

**Strategic Tasks** (market entry, competitive positioning, resource allocation):
Market size and current position, competitive landscape, internal capabilities and capacity constraints, financial constraints, timeline pressures, prior strategic decisions, stakeholder dynamics.

**Technical Tasks** (system design, migration, debugging):
Current architecture and dependencies, scale metrics, team composition and skill gaps, technology constraints, existing technical debt, deployment environment, failure history.

**Analytical Tasks** (data analysis, financial modeling, root cause analysis):
The specific question the analysis must answer, available data and quality issues, baseline metrics, time period and comparison frame, known confounding factors, decision context and action thresholds.

**Creative Tasks** (content creation, messaging, campaign design):
Target audience profile and language, voice and tone requirements, channel and format constraints, competitive messaging, specific words to use or avoid, success metric.

**Research Tasks** (literature review, evidence synthesis, landscape scan):
Specific research question or hypothesis, scope boundaries, source hierarchy, known prior work, intended use, quality threshold (comprehensiveness vs. speed).

**Comparative Tasks** (vendor selection, option evaluation, technology comparison):
Named options being compared, evaluation criteria with weights, non-negotiable requirements, current state, decision constraints, decision-maker profile.

#### Tool 2: Context Depth Tester

Run context through three diagnostic questions before constructing the prompt:

1. **The Competitor Swap Test.** Could you replace the company or product name with a competitor's and the context would still be accurate? If yes → context describes the category, not the situation. Add specifics.

2. **The Quantification Check.** Does the context include at least three specific numbers? Revenue, headcount, timeline, customer count, conversion rate, budget — any concrete quantification. Numbers force specificity.

3. **The Prior Decisions Check.** Does the context mention what has been tried, decided, or ruled out? This is the most commonly omitted element and the one most responsible for generic output.

#### Tool 3: Context Enrichment Prompts

When context is thin, these five questions target different dimensions of specificity. Even two or three substantially improve context:

1. What happened that makes this task necessary right now?
2. What constraints exist that are not obvious from the task description?
3. What has already been tried or considered?
4. Who will act on this output, and what will they do with it?
5. What would make this task fail even if the analysis is correct?

---

## Layer 4 — Reasoning

**Purpose:** Controls how Claude thinks through the problem. The highest-leverage layer — the difference between shallow and deep output almost always traces back to reasoning quality. "Think step by step" is better than nothing, but task-specific reasoning instructions dramatically improve output.

### Ready-to-Use Reasoning Approaches

**Analytical / Evaluative Tasks:**
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

**Strategic / Planning Tasks:**
```xml
<reasoning>
Approach this strategically:
1. Map the stakeholders and their competing interests or incentives.
2. Identify the binding constraints — which are truly non-negotiable vs. merely assumed?
3. Generate at least three structurally different approaches (not variations of one idea).
4. Evaluate each approach against the stated constraints and success criteria.
5. Identify the second-order consequences of each approach — what does it enable or prevent later?
6. Recommend the approach with the best tradeoff profile, and be explicit about what it sacrifices.
</reasoning>
```

**Creative / Generative Tasks:**
```xml
<reasoning>
Approach this creatively:
1. Before committing to a direction, explore the possibility space broadly. What are the different angles, framings, or entry points?
2. Identify the 2-3 most promising directions and articulate what makes each interesting or distinctive.
3. Develop the strongest direction fully, with specificity and craft.
4. Revisit whether elements from other directions would strengthen the chosen one.
</reasoning>
```

**Technical / Problem-Solving Tasks:**
```xml
<reasoning>
Approach this technically:
1. Restate the problem in your own words to confirm you understand it correctly.
2. Identify the most likely failure points or root causes, ranked by probability.
3. Trace the logic or data flow from input to output, checking each transition.
4. When you identify the issue, verify your solution does not introduce new problems.
5. Consider edge cases — what happens at boundary conditions or under unusual inputs?
</reasoning>
```

**Research / Synthesis Tasks:**
```xml
<reasoning>
Approach this as a research synthesis:
1. Identify the key themes, patterns, or findings across the available information.
2. Note where sources agree and where they conflict. Conflicts are often the most informative.
3. Assess the quality and reliability of each source — not all evidence is equal.
4. Synthesize a coherent picture, clearly distinguishing between what is well-established, what is likely, and what is speculative.
5. Identify the most important gaps — what don't we know that would matter most?
</reasoning>
```

**Comparative / Decision-Support Tasks:**
```xml
<reasoning>
Approach this comparison as follows:
1. Define the evaluation criteria explicitly before comparing. What dimensions matter and how should they be weighted?
2. Evaluate each option against every criterion consistently.
3. Identify where the options are functionally equivalent — do not manufacture differences.
4. Identify where the options genuinely diverge and why it matters.
5. Make a clear recommendation with explicit reasoning, not a "they're all good in different ways" non-answer.
</reasoning>
```

### Combining Reasoning Approaches

When a task spans categories, combine elements. Keep total steps to 5-7. Lead with the dominant task type.

Example: A strategic decision needing technical feasibility analysis → Strategic reasoning structure with technical evaluation folded into steps 3-4.

---

## Layer 5 — Output

**Purpose:** Controls the format, structure, and length of the response. Without this, Claude defaults to its own formatting preferences.

### Template

```xml
<output_format>
Structure your response as follows:

[SECTION 1 NAME]: [What this section contains and approximate length]
[SECTION 2 NAME]: [What this section contains and approximate length]
[SECTION 3 NAME]: [What this section contains and approximate length]

Constraints:
- Total length: [target word count or page count]
- Tone: [formal / conversational / technical / etc.]
- Format: [prose / bullets / table / JSON / etc.]
</output_format>
```

### Ready-to-Use Output Structures

**Executive Brief:** Bottom Line (2-3 sentences), Supporting Analysis (3-5 paragraphs), Key Risks (1 paragraph), Recommended Next Steps (3-5 concrete actions). Total: 500-700 words, prose.

**Technical Design Document:** Problem Statement (1 paragraph), Proposed Solution (2-3 paragraphs), Alternatives Considered, Implementation Plan (phased with dependencies), Open Questions. Technical audience.

**Research Summary:** Key Findings (3-5 numbered, each 2-3 sentences), Evidence Quality Assessment (1 paragraph), Detailed Analysis (organized by theme, not by source), Gaps and Limitations, Implications. Total: 800-1200 words.

**Implementation Plan:** Objective (1-2 sentences), Prerequisites, Phases (table: Phase, Actions, Owner, Duration, Dependencies), Success Metrics, Risk Register (table: Risk, Likelihood, Impact, Mitigation).

**Decision Matrix:** Criteria definition with weights, consistent evaluation of each option, summary table, clear recommendation.

**Strategic Memo:** Recommendation up front, situation assessment, analysis of options, recommended approach with tradeoffs, risks and mitigations, next steps.

**Process Documentation:** Purpose, prerequisites, step-by-step procedures, decision points, exception handling, verification steps.

---

## Quality Control (Cross-Cutting)

**Purpose:** Standards applied across the entire output.

### Standard Quality Control

```xml
<quality_standards>
Before finalizing your response:

Accuracy: Verify every factual claim. If uncertain, say so explicitly rather than presenting speculation as fact.

Completeness: Confirm you have addressed every part of the request. If you intentionally omitted something, state why.

Assumptions: Surface any assumptions you made. If the output would change significantly under different assumptions, flag this.

Pushback: If the request itself contains a flawed premise, an unproductive framing, or a better alternative approach, say so directly before proceeding.

Actionability: Every recommendation must be specific enough that someone could act on it without asking follow-up questions about what you meant.
</quality_standards>
```

### Task-Specific Additions

- **Strategic work:** Internal consistency — verify recommendations do not contradict each other.
- **Technical work:** Edge cases — identify at least two failure modes and how they would be handled.
- **Research work:** Source discrimination — distinguish between well-established findings, emerging evidence, and speculation.
- **Creative work:** Distinctiveness — verify the output is not generic or could-apply-to-anyone.
- **Financial work:** Assumption transparency — all numbers sourced or labeled as estimates.
- **Advisory work:** Agreeableness counter — challenge flawed premises before proceeding.

---

## Assembly Principles

1. **Choose an Identity** matching the expertise needed.
2. **Write an Objective** that passes the clarity test.
3. **Provide Context** with maximum specificity — this is where most prompts underperform.
4. **Select a Reasoning approach** matching the task category.
5. **Choose an Output structure** matching the deliverable format.
6. **Add Quality Control** appropriate to the task type.
7. **Wrap everything in XML tags** for structural clarity.
8. **Apply primacy-recency ordering** — identity and constraints top, output and quality bottom.
9. **Audit** — remove anything that does not actively improve output.

---

## Global Layer Interaction (Project Mode)

When building a Project scaffold with global layer awareness, the five-layer architecture operates within a broader context:

**Layer 1 (Identity)** — The Project identity may reference capabilities provided by global layers. Example: "You have access to Google Drive for file retrieval" (if the Drive connector is configured). The identity should not claim capabilities the user's configuration does not support.

**Layer 2 (Objective)** — Unchanged. Task objectives are always project-specific.

**Layer 3 (Context)** — Project context may include awareness of global configuration. Example: the context section might note "The user's Preferences establish [X], so this Project focuses on [Y-specific calibration]."

**Layer 4 (Reasoning)** — Unchanged. Reasoning approaches are always task-specific.

**Layer 5 (Output + Quality Control)** — Output standards should not conflict with the user's Style settings. If the user has an active Style that affects formatting, note potential tensions in the Global Layer Advisory rather than building conflicting output rules.
