# Executive Formats

Output format specifications for deliverables targeting senior leadership, decision-makers, and project stakeholders. Each format includes the complete XML specification, per-section guidance, and watch-for notes on Claude's common failure modes.

---

## Table of Contents

- [Executive Brief](#executive-brief)
- [Strategic Memo](#strategic-memo)
- [Stakeholder Update](#stakeholder-update)

---

## Executive Brief

**Use when:** The audience is senior leadership who need to make a decision or understand a situation quickly. The key principle: lead with the answer, then support it.

**Audience:** C-suite, VPs, board members, senior decision-makers.

**Length:** 500-800 words.

### Format Specification

```xml
<output_format>
Structure as an executive brief:

Bottom Line: (2-3 sentences) The answer, recommendation, or key finding. State it directly — this is what the reader came for.

Supporting Analysis: (3-5 paragraphs) The evidence and reasoning behind the bottom line. Each paragraph should advance a distinct point. Write in prose.

Key Risks: (1 paragraph) What could go wrong, what is uncertain, and what to watch for.

Recommended Next Steps: (3-5 items, each one sentence) Concrete actions, each with a clear owner or ownership category.

Total length: 500-800 words. Prioritize clarity and decisiveness over completeness.
</output_format>
```

### Watch For

**Buried recommendation.** Claude may bury the recommendation in the analysis rather than stating it upfront in the Bottom Line. If the Bottom Line reads as a preview ("this brief examines...") rather than a conclusion ("we should do X because Y"), add this countermeasure: *"The Bottom Line must contain your actual recommendation or conclusion, not a description of what the brief covers."*

**Vague next steps.** Each step should pass the test: "Could someone act on this tomorrow?" If next steps are aspirational rather than concrete, add: *"Each next step must specify a concrete action, who owns it, and a timeframe."*

---

## Strategic Memo

**Use when:** You need to make a case for a strategic direction, policy change, or significant decision. Longer and more substantive than an Executive Brief — this is for decisions that need a full argument, not just a recommendation.

**Audience:** Decision-making audience — executives, steering committees, boards.

**Length:** 1000-1500 words.

### Format Specification

```xml
<output_format>
Structure as a strategic memo:

Recommendation: (1 paragraph) The proposed course of action and its expected impact. State the recommendation before the argument.

Context: (2-3 paragraphs) The situation that makes this decision necessary now. What has changed, what is at stake, and what happens if we do nothing?

Analysis: (3-5 paragraphs) The reasoning supporting the recommendation. Address the strongest counterarguments directly — a memo that ignores obvious objections loses credibility. Use evidence and specifics, not assertions.

Alternatives Considered: (1-2 paragraphs) What other approaches were evaluated and why they are less attractive. This demonstrates rigor and preempts "but what about..." responses.

Implementation Considerations: (1-2 paragraphs) Key requirements, risks, and sequencing for execution. Not a full plan, but enough to show the recommendation is feasible.

Ask: (1 paragraph) What specific decision, approval, or resource is being requested.

Total length: 1000-1500 words. Write in a tone appropriate for the decision-making audience.
</output_format>
```

### Watch For

**Neutral analysis instead of argument.** Claude may write the Analysis section as a neutral assessment rather than as a case supporting the recommendation. A strategic memo has a point of view — the analysis should build the argument, not just lay out the facts. If the analysis reads like a research summary, add this countermeasure: *"The analysis should build the case for the recommendation. Present evidence and reasoning that supports the proposed course of action. Address counterarguments to strengthen the case, not to equivocate."*

**Missing the Ask.** Claude sometimes wraps up with a summary instead of a clear ask. The Ask section must specify what decision, approval, or resource is being requested — not restate the recommendation.

---

## Stakeholder Update

**Use when:** You need to communicate progress, status, or results to stakeholders who need to stay informed but are not doing the work.

**Audience:** Project sponsors, cross-functional partners, management. People familiar with the project who need status, not context.

**Length:** 200-400 words. Stakeholder updates that require scrolling are stakeholder updates that don't get read.

### Format Specification

```xml
<output_format>
Structure as a stakeholder update:

Status: (1 sentence) Overall status — on track, at risk, or off track. State it upfront.

Key Progress: (3-5 items, each 1-2 sentences) What has been accomplished since the last update. Focus on outcomes and milestones, not activities.

Upcoming: (3-5 items, each 1-2 sentences) What is planned next and expected timelines.

Blockers or Risks: (if any — omit if none) What is blocking progress or creating risk. For each, state what help is needed and from whom.

Metrics: (if applicable) The 2-4 numbers that tell the story. Include trend direction (up/down/flat) and whether the trend is on target.

Total length: 200-400 words. Stakeholder updates that require scrolling are stakeholder updates that don't get read.
</output_format>
```

### Watch For

**Excessive background context.** Claude may pad the update with context and background that the stakeholder already knows. These updates should assume familiarity with the project. If the output includes excessive framing, add this countermeasure: *"The audience is already familiar with this project. Do not include background context. Focus exclusively on what has changed since the last update."*

**Activities instead of outcomes.** Key Progress should report what was achieved, not what was done. "Completed migration of 3 million records with zero data loss" is an outcome. "Worked on data migration tasks this week" is an activity.
