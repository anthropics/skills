---
name: rootnode-domain-content-communications
description: >-
  Specialized prompt-building methodology for content and communications tasks.
  Provides 11 tested approaches (3 identity, 4 reasoning, 4 output) for writing,
  editing, content strategy, copywriting, audience analysis, editorial evaluation,
  cross-channel adaptation, and persuasion design. Use when building a Claude prompt
  or system prompt for content creation, editorial workflows, or communications tasks.
  Trigger on: "build a prompt for writing," "prompt for content strategy," "prompt for
  copywriting," "prompt for blog posts," "prompt for email sequences," "system prompt
  for editorial," "prompt for messaging framework," "content brief prompt," "prompt for
  audience analysis," "prompt that produces better content." Do NOT use for writing
  content directly — this Skill builds prompts that produce better content. Do NOT use
  for evaluating or scoring existing prompts — use rootnode-prompt-validation if available.
  Do NOT use for general prompt compilation — use rootnode-prompt-compilation if available.
license: Apache-2.0
metadata:
  author: rootnode
  version: "1.1"
  original-source: "DOMAIN_PACK_CONTENT_COMMUNICATIONS.md"
---

# Content & Communications Prompt Methodology

> **Calibration:** Tier 1, Opus-primary. See repository README for model compatibility.

Build Claude prompts that produce high-quality content — articles, copy, content strategy, messaging frameworks, email sequences, and editorial evaluations. This Skill provides tested identity, reasoning, and output approaches tuned for content and communications work.

**This Skill builds prompts, not content.** Use it when you need a system prompt or structured prompt that will reliably produce good content from Claude. If you need to write content directly, you do not need this Skill — you need a writer.

## When to Use This Skill

Use when the task is building a Claude prompt for any of these content domains:

- **Long-form writing** — articles, blog posts, guides, whitepapers, reports, essays
- **Content strategy** — editorial calendars, channel strategy, content programs, measurement frameworks
- **Conversion copywriting** — ad copy, landing pages, email copy, CTAs, social posts, product descriptions
- **Audience analysis** — audience profiling, segmentation, information needs mapping
- **Editorial evaluation** — content review, quality assessment, draft feedback
- **Cross-channel adaptation** — reshaping content across formats and audiences
- **Persuasion design** — landing pages, sales content, fundraising appeals, policy arguments
- **Content specifications** — content briefs, messaging frameworks, email sequences

## How to Use This Skill

**Step 1: Identify the content task category.** Use the selection tables below to choose the right identity, reasoning, and output approaches.

**Step 2: Assemble the prompt.** Combine the selected identity (Layer 1), reasoning approach (Layer 3), and output specification (Layer 4) into a structured prompt. Use XML tags to separate layers clearly.

**Step 3: Add behavioral countermeasures.** Content prompts are especially susceptible to five Claude tendencies — see the Behavioral Countermeasures section below. Add the relevant countermeasures to the prompt's quality control layer.

**Step 4: Add task-specific context.** Include audience details, brand voice guidelines, competitive context, or channel constraints that the prompt needs to produce relevant content.

---

## Identity Selection

Choose one identity approach for the prompt. The identity sets Claude's expertise orientation.

| Task Type | Identity Approach | When to Use |
|---|---|---|
| Articles, guides, whitepapers, reports, essays | Writer / Editor | Producing or refining long-form content for publication |
| Editorial calendars, channel strategy, content programs | Content Strategist | Designing content systems — what to create, for whom, on which channels |
| Ad copy, landing pages, email copy, CTAs, social | Copywriter | Short-form content designed to drive a specific action |

**Decision logic:**
1. Is the deliverable a finished piece of content? → Writer / Editor
2. Is the deliverable a plan for content? → Content Strategist
3. Is the deliverable short-form content designed to drive action? → Copywriter

### Writer / Editor

Use for prompts that produce or refine long-form content — articles, blog posts, guides, reports, essays, whitepapers. This identity optimizes for engagement, clarity, and persuasion in a publishing context.

```xml
<role>
You are a senior writer and editor with deep experience producing clear, engaging long-form content for professional audiences. You write tight, structured prose that earns the reader's attention and keeps it — every paragraph advances the piece, every sentence earns its place.

You edit ruthlessly. You cut filler, tighten transitions, strengthen verbs, and eliminate hedging language that dilutes the argument. You know the difference between being thorough and being long. A 1,000-word piece that says something clearly beats a 2,500-word piece that says the same thing with padding.

You match voice and register to the audience and publication context. An executive-facing whitepaper reads differently from a developer blog post, which reads differently from a thought-leadership essay. You adapt without losing clarity or substance.
</role>
```

**Failure modes:** Can push Claude toward overly polished prose that feels corporate — smooth but forgettable. If the output reads like a press release, add to the prompt: *"Write with a distinct point of view. Take a position, use concrete examples, and write sentences that could not be swapped between this piece and a competitor's without anyone noticing."* Also watch for Claude defaulting to listicle structure (numbered tips, subheaded sections) when sustained argument would be stronger. Add: *"This piece should read as a cohesive argument or narrative, not as a collection of subsections. Use transitions, not subheads, to guide the reader."*

### Content Strategist

Use for prompts that design content programs — determining what content to create, for which audiences, on which channels, at what frequency, measured by what outcomes.

```xml
<role>
You are a senior content strategist who designs content programs that drive measurable business outcomes. You think in systems: what content serves which audience at which stage, distributed through which channels, measured by which metrics. You do not design content for its own sake — every piece in the program exists because it serves a specific audience need at a specific point in their journey.

You are rigorous about channel fit. The same message needs different formats for different channels — what works as a long-form blog post does not work as a LinkedIn post or a sales email. You design content that is native to its channel, not repurposed without adaptation.

You measure content by its business impact, not by vanity metrics. Traffic without engagement is noise. Engagement without conversion is entertainment. You design content programs where each metric connects to a business outcome you can defend.
</role>
```

**Failure modes:** Can produce strategies that are ambitious but under-resourced — recommending cadence requiring a team of five when the team is two. Add team size and production capacity context. Also defaults to B2B SaaS content patterns (blog → ebook → webinar → demo funnel) regardless of business model. For non-SaaS businesses, add explicit business model and audience behavior context.

### Copywriter

Use for prompts that produce short-form content designed to drive a specific action — ad copy, landing pages, email subject lines, CTAs, social posts, product descriptions, sales collateral.

```xml
<role>
You are a senior copywriter with deep experience in direct response and conversion-focused writing. You write copy that earns attention in the first line and drives action by the last. Every word has a job — if it is not advancing the reader toward the desired action, it is costing you their attention.

You understand that great copy is built on audience insight, not clever wordplay. You start with what the reader wants, what they fear, and what is stopping them — then you write copy that addresses those realities, not copy that talks about the product's features.

You write in the reader's language, not the company's language. You are specific rather than aspirational. "Save 4 hours per week on invoicing" beats "Transform your financial workflow." You test your copy by asking: would a real person say this out loud? If not, it is too corporate.
</role>
```

**Failure modes:** Can push Claude toward aggressive marketing language — urgency triggers, scarcity claims, hype. For technical, executive, or B2B audiences, add: *"This audience responds to substance, not urgency. Build the case with specifics and evidence."* Also produces copy that is punchy but vague — strong rhythm without specific substance. Add: *"Every sentence must communicate a specific, concrete benefit or fact."*

---

## Reasoning Selection

Choose one or two reasoning approaches for the prompt. See `references/reasoning-approaches.md` for complete approach specifications.

| Task Type | Reasoning Approach | When to Use |
|---|---|---|
| Audience profiling, segmentation, needs mapping | Audience Analysis | Primary deliverable is audience understanding, or audience insight is weak |
| Content review, quality assessment, draft feedback | Editorial Judgment | Evaluating existing content for quality, clarity, effectiveness |
| Reshaping content across formats or audiences | Content Adaptation | Core message exists; challenge is translation across contexts |
| Landing pages, sales content, action-driving content | Persuasion Architecture | Content must move reader toward specific action or belief change |

**Decision logic:**
1. Do you need to understand the audience before creating content? → Start with Audience Analysis
2. Are you evaluating existing content? → Editorial Judgment
3. Are you translating content across channels? → Content Adaptation
4. Is the content designed to drive a specific action? → Persuasion Architecture

Approaches can combine: Audience Analysis + Persuasion Architecture is a strong pairing for conversion-focused content where audience insight is weak. Editorial Judgment + Content Adaptation pairs well for adapting content while improving quality. Limit combined approaches to two — more creates competing analytical frameworks.

---

## Output Selection

Choose one output specification for the prompt. See `references/output-formats.md` for complete format specifications.

| Deliverable | Output Format | When to Use |
|---|---|---|
| Published long-form web content | Blog Post / Article | Informational, thought leadership, or educational content for web |
| Writer specification document | Content Brief | Strategic doc that tells a writer what to create |
| Cross-channel messaging reference | Messaging Framework | How to talk about a product/company/initiative across all channels |
| Multi-email campaign | Email Sequence | Progressive multi-touch communication toward a specific action |

**Decision logic:**
1. Is the deliverable published content for external audiences? → Blog Post / Article
2. Is the deliverable a specification for content someone else will write? → Content Brief
3. Is the deliverable a reference document for consistent messaging? → Messaging Framework
4. Is the deliverable a sequence of emails with a progressive arc? → Email Sequence

---

## Behavioral Countermeasures

Content and communications prompts are especially susceptible to five Claude tendencies. Add the relevant countermeasures to any prompt built with this Skill.

### Corporate Voice Default

Claude's default writing voice for professional content is smooth, formal, and forgettable — the voice of a committee-written press release. Add to prompts that produce content:

*"Write with a specific, recognizable voice. If this piece could have been written by any company in the industry, the voice is too generic. Take a position. Use concrete language. Write sentences that a reader would remember."*

### Excessive Hedging in Persuasive Content

When writing copy or persuasive content, Claude adds qualifiers that undermine the message — "this could potentially help" instead of "this will help." Add to prompts for persuasive or conversion content:

*"Write with conviction. If you believe the claim, state it directly. Save hedging for genuinely uncertain claims, not for every assertion. Persuasive copy that hedges is just information."*

### Listicle Default

Claude gravitates toward numbered lists and subheaded sections when continuous narrative would be more engaging. Add to prompts for articles, essays, or thought leadership:

*"Write in connected prose, not a list. Build an argument that flows from paragraph to paragraph. Use transitions, not subheads, as the structural device. Lists are appropriate only when the content is genuinely a set of parallel items."*

### Feature-First Messaging

When writing about products or services, Claude describes features rather than starting with the audience's problem. Add to any prompt involving product or service content:

*"Start with the reader's problem, not the product's features. The reader cares about their outcome — the product is the means, not the message. Lead with what changes for the reader, not what the product does."*

### Filler Openings

Claude opens content with generic scene-setters ("In today's rapidly evolving landscape...") that waste the reader's attention. Add to any content-producing prompt:

*"Open with the most specific, interesting, or surprising thing you have to say. Delete any opening sentence that could apply to any article on any topic. The first sentence earns or loses the reader."*

---

## Quality Checks for Content Prompts

When building prompts with this Skill, verify these content-specific quality criteria are addressed in the prompt:

- **Audience specificity:** The prompt defines a specific audience. If the audience could be "anyone interested in this topic," the targeting is too broad and the content will be too generic.
- **Competitor swap test:** Positioning and key messages in the prompt must be true of the specific product/company and false of closest competitors. If a competitor's name could be substituted without the messaging seeming wrong, it is too generic.
- **Evidence over assertion:** The prompt instructs Claude to support claims with specific proof points — data, examples, case studies. Unsupported superlatives ("industry-leading," "best-in-class") are noise, not persuasion.
- **Voice consistency:** The prompt specifies a consistent voice and register. If no voice is specified, Claude defaults to corporate-neutral.
- **CTA clarity:** For action-driving content, the prompt specifies a single, clear desired action. Ambiguous CTAs produce ambiguous results.

---

## Troubleshooting

**Content sounds generic and corporate.** The prompt is missing voice specification and audience detail. Add a specific voice description ("authoritative but conversational, like a respected industry practitioner talking to peers") and concrete audience context.

**Content leads with features, not reader benefits.** Add the Feature-First Messaging countermeasure and restructure the prompt to specify the reader's problem before describing the product.

**Content is a listicle when it should be an argument.** Add the Listicle Default countermeasure. Also check whether the output specification is encouraging list structure — if so, switch to the Blog Post / Article format with the subhead restriction.

**Messaging framework is full of aspirational language.** Add the competitor swap test instruction explicitly: *"Apply the competitor swap test to every value proposition: if a competitor's name could be substituted without the messaging seeming wrong, rewrite until the messaging is true of this product and false of the closest alternative."*

**Email sequence feels repetitive.** Each email follows the same structure. Add: *"Each email must have a structurally different approach to advancing the reader. One might lead with a customer story, another with a surprising statistic, another with a direct question."*

**Content brief is too vague to guide a writer.** Add: *"The brief must be specific enough that two different writers would produce substantially similar pieces — same angle, same key points, same audience register."*

For deeper prompt evaluation methodology, see the `rootnode-prompt-validation` Skill if available. For general prompt construction beyond content domains, see `rootnode-prompt-compilation` if available.
