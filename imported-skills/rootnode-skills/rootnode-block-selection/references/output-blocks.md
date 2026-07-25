# Output Format Approaches

Ten tested output formats for Claude prompts. Each controls WHAT the deliverable looks like — structure, sections, length, and format. Without explicit format guidance, Claude defaults to its own preferences, which often means too-long prose with too many bullet points.

Select the format matching the deliverable type. Customize section names, lengths, and constraints to the situation. If no format fits, use the custom template at the bottom.

---

## Contents

1. Executive Brief
2. Technical Design Document
3. Research Summary
4. Implementation Plan
5. Decision Matrix
6. Competitive Analysis
7. Post-Mortem / Retrospective
8. Stakeholder Update
9. Strategic Memo
10. Process Documentation
11. Building Custom Output Formats

---

## 1. Executive Brief

**Use when:** The audience is senior leadership who need to make a decision or understand a situation quickly. Lead with the answer, then support it.

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

**Watch for:** Claude may bury the recommendation in the analysis rather than stating it upfront. If the Bottom Line reads as a preview ("this brief examines...") rather than a conclusion ("we should do X because Y"), add: *"The Bottom Line must contain your actual recommendation or conclusion, not a description of what the brief covers."* Also watch for vague Next Steps — each should pass the test: "Could someone act on this tomorrow?"

---

## 2. Technical Design Document

**Use when:** Proposing a technical solution that will be reviewed by engineers and technical leaders. Optimized for clarity of architectural decisions and tradeoffs.

```xml
<output_format>
Structure as a technical design document:

Problem Statement: (1 paragraph) What problem this design solves, why it matters, and what constraints bound the solution.

Proposed Solution: (2-4 paragraphs) The architecture, key components, and data flow. Describe the system top-down or trace the primary user flow. Include pseudocode or data schemas where they add clarity.

Key Design Decisions: (1-2 paragraphs per decision) For each major architectural choice, state what was decided, what alternatives were considered, and why this approach was chosen. This is the most important section.

Implementation Approach: (table or phased list) How this would be built — phases, dependencies, and rough sequencing. Not a project plan, but enough to assess feasibility.

Open Questions: (numbered list) Anything unresolved that needs input before proceeding. For each, state the question, who should answer it, and the decision's impact.

Write for a technical audience. Prioritize precision over accessibility.
</output_format>
```

**Watch for:** Claude may describe the system in abstract terms without getting concrete about data structures, API contracts, or component boundaries. For more detail, add: *"Include specific details: data models, API signatures, or interface contracts for the key components."* For a senior audience, add: *"Focus on architectural decisions and tradeoffs. Omit implementation details below the component level."*

---

## 3. Research Summary

**Use when:** Presenting findings from research, analysis, or investigation. Organized by insight, not by source.

```xml
<output_format>
Structure as a research summary:

Key Findings: (3-5 numbered findings, each 2-3 sentences) The most important discoveries or conclusions, in order of significance. Each finding should be a complete, actionable insight — not a topic label.

Evidence Assessment: (1 paragraph) How strong is the underlying evidence? Where is it robust and where is it thin? Are there notable methodological limitations?

Detailed Analysis: (organized by theme, 2-3 paragraphs per theme) The supporting analysis, organized by topic or theme — never by source. Each theme section should synthesize across sources.

Gaps and Limitations: (1 paragraph) What the available information does not tell us. What additional data or research would strengthen the conclusions?

Implications: (1-2 paragraphs) What these findings mean for the decision or situation at hand. Connect the research to action.

Total length: 800-1200 words.
</output_format>
```

**Watch for:** Claude may organize the Detailed Analysis by source instead of by theme. Reinforce with: *"Organize all analysis by theme or question, never by source."* Also watch for Key Findings that are too vague — "Customer preferences are changing" is a topic, not a finding. "Customers under 35 prefer X over Y by a 2:1 ratio" is a finding.

---

## 4. Implementation Plan

**Use when:** A plan for executing a project, initiative, or change. Emphasis on sequencing, dependencies, and measurable progress.

```xml
<output_format>
Structure as an implementation plan:

Objective: (1-2 sentences) What this plan achieves and the timeline.

Prerequisites: (brief list) What must be true before starting. Include decisions that need to be made, resources that need to be secured, and dependencies that must be resolved.

Phases: Present as a table with columns: Phase | Key Actions | Duration | Dependencies | Success Criteria. Each phase should be a meaningful milestone, not just a time period. 3-6 phases is typical.

Risk Register: Present as a table with columns: Risk | Likelihood (H/M/L) | Impact (H/M/L) | Mitigation. Include 3-5 material risks, not an exhaustive list.

Resource Requirements: (1 paragraph) What people, budget, and tools are needed, with any assumptions about availability.

Be specific about durations and dependencies. A plan without timelines is a wish list.
</output_format>
```

**Watch for:** Claude may produce phases that are too high-level ("Phase 1: Planning and Discovery") or too detailed. The right granularity: someone could read a phase and know what work needs to happen, who needs to be involved, and how to tell when it's done. Also watch for success criteria that are restated actions ("Success: complete the migration") rather than measurable outcomes ("Success: all data migrated with <0.1% discrepancy, latency under 200ms").

---

## 5. Decision Matrix

**Use when:** Structured comparison of options against defined criteria. The output should make tradeoffs visible and support a clear recommendation.

```xml
<output_format>
Structure as a decision matrix:

Decision Context: (1 paragraph) What decision is being made, why it matters, and what constraints apply.

Evaluation Criteria: (brief descriptions) List each criterion with a one-sentence definition and its relative weight (critical / important / nice-to-have). 4-7 criteria is typical.

Comparison Matrix: Present as a table with options as rows and criteria as columns. Use a consistent rating scale (e.g., Strong / Adequate / Weak, or 1-5) with brief justifications in each cell — not just scores.

Analysis: (2-3 paragraphs) Interpret the matrix. Where do options clearly separate? Where are they essentially equivalent? What single factor most differentiates the top options?

Recommendation: (1 paragraph) A clear recommendation with the primary reasoning. If two options are very close, state what additional information would break the tie.

Write the matrix for a decision-maker who will scan the table first and read the analysis only if they need more detail.
</output_format>
```

**Watch for:** Claude may create a matrix where every option scores "Adequate" on most criteria, making the comparison useless. Push for differentiation: *"If two options are essentially equivalent on a criterion, mark them both as equivalent and focus your analysis on the criteria where they genuinely differ."*

---

## 6. Competitive Analysis

**Use when:** Assessing the competitive landscape around a product, company, or market position.

```xml
<output_format>
Structure as a competitive analysis:

Market Overview: (1 paragraph) The market being analyzed, its size or trajectory, and why competitive positioning matters now.

Competitive Landscape: (1 paragraph per competitor, covering 3-5 key competitors) For each: their market position, key strengths, notable weaknesses, and recent strategic moves. Focus on what matters to your competitive position — not a comprehensive company profile.

Comparative Position: A table or structured comparison showing how the subject compares to competitors on the 3-5 most important competitive dimensions.

Competitive Advantages: (1-2 paragraphs) Where the subject has a durable edge. Be specific about what makes the advantage defensible.

Competitive Vulnerabilities: (1-2 paragraphs) Where the subject is at risk. Be equally specific and direct.

Strategic Implications: (1 paragraph) What this competitive picture means for strategy. What should the subject do, avoid, or watch for?

Total length: 800-1200 words. Be direct about weaknesses — a competitive analysis that only sees strengths is useless.
</output_format>
```

**Watch for:** Claude may be reluctant to state clear competitive vulnerabilities, especially if the context implies you are the subject. Add: *"Be equally direct about vulnerabilities as you are about advantages. A competitive analysis that minimizes weaknesses is dangerous."*

---

## 7. Post-Mortem / Retrospective

**Use when:** Analyzing what happened after a project, incident, or initiative — what worked, what didn't, and what to do differently.

```xml
<output_format>
Structure as a post-mortem:

Summary: (2-3 sentences) What happened, when, and what the impact was. Lead with facts, not narrative.

Timeline: A brief chronological sequence of the key events. Include only the events that matter for understanding what happened and why.

Root Cause Analysis: (2-3 paragraphs) What caused the outcome. Distinguish between the triggering event and the underlying conditions that allowed it to happen. Go deeper than the first explanation.

What Worked: (1-2 paragraphs) What went well or mitigated the impact. Post-mortems that are only about failure miss the chance to reinforce good practices.

What Failed: (1-2 paragraphs) What broke down, and why. Be specific and blameless — focus on systems, processes, and decisions, not individuals.

Action Items: (numbered list, 3-7 items) Concrete changes to prevent recurrence. Each item should have: what will change, who owns it, and a target date.

Write in a blameless, learning-focused tone. The goal is improvement, not accountability.
</output_format>
```

**Watch for:** Claude may produce a root cause analysis that is too shallow (stopping at "we didn't test enough" rather than asking why testing was insufficient). Pair this with the Root Cause Diagnosis reasoning approach for depth. Also watch for vague action items — each must be concrete and assignable.

---

## 8. Stakeholder Update

**Use when:** Communicating progress, status, or results to stakeholders who need to stay informed but aren't doing the work.

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

**Watch for:** Claude may pad the update with context and background that the stakeholder already knows. Add: *"The audience is already familiar with this project. Do not include background context. Focus exclusively on what has changed since the last update."*

---

## 9. Strategic Memo

**Use when:** Making a case for a strategic direction, policy change, or significant decision. Longer and more substantive than an executive brief — for decisions that need a full argument.

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

**Watch for:** Claude may write the Analysis section as a neutral assessment rather than as a case supporting the recommendation. A strategic memo has a point of view — the analysis should build the argument. If the analysis reads like a research summary, add: *"The analysis should build the case for the recommendation. Address counterarguments to strengthen the case, not to equivocate."*

---

## 10. Process Documentation

**Use when:** Documenting a workflow, procedure, or operational process that others will follow. Optimized for clarity and usability by someone executing the process.

```xml
<output_format>
Structure as process documentation:

Purpose: (1-2 sentences) What this process achieves and when to use it.

Scope: (1-2 sentences) What this process covers and what it explicitly does not cover.

Prerequisites: (brief list) What must be in place before starting — access, tools, information, or prior steps completed.

Steps: Numbered sequence. Each step should include: the action to take (specific and unambiguous), who takes it, and the expected result. Group steps into phases if the process has natural stages. For decision points, specify the criteria for each path.

Exception Handling: How to handle the most common things that go wrong. Cover 2-4 common exceptions — not every possible error.

Ownership: Who maintains this process and how often it should be reviewed.

Write for someone executing the process for the first time. Every step must be specific enough to follow without asking clarifying questions.
</output_format>
```

**Watch for:** Claude may write steps that are too high-level ("Configure the system appropriately") or too detailed for the audience. The right level: someone familiar with the tools but new to this specific process could follow each step. Also watch for missing decision points — if a step requires judgment ("if the data looks correct"), specify what "correct" means.

---

## 11. Building Custom Output Formats

When no format fits, build one using this template:

```xml
<output_format>
Structure your response as follows:

[SECTION 1 — name and what it contains]: (length guidance)
[SECTION 2 — name and what it contains]: (length guidance)
[SECTION 3 — name and what it contains]: (length guidance)

Constraints:
- Total length: [word count or page count]
- Tone: [formal / direct / conversational / technical]
- Format: [prose / table / numbered list — specify per section if mixed]
- Audience: [who will read this and what they need from it]
</output_format>
```

**Design principles:**

**Lead with what the reader wants most.** Executives want the recommendation first. Engineers want the architecture first. Researchers want the findings first. Put the highest-value section at the top.

**Specify length per section, not just total.** "500 words" tells Claude the total budget but not how to allocate it. "Bottom Line: 2-3 sentences. Analysis: 3 paragraphs. Next Steps: 3-5 items." tells Claude how much attention each section deserves.

**Constrain the format where it matters.** If you want prose, say "write in prose" — otherwise Claude defaults to bullet points. If you want a table, say "present as a table with columns: X, Y, Z" — otherwise Claude may use bullets where a table would be clearer.

**Name sections descriptively.** "Analysis" is vague. "Competitive Assessment" or "Root Cause Analysis" tells Claude what kind of analysis belongs there. Section names are implicit instructions.
