# Operational Formats

Output format specifications for deliverables involving project execution planning and incident or project analysis. Each format includes the complete XML specification, per-section guidance, and watch-for notes on Claude's common failure modes.

---

## Table of Contents

- [Implementation Plan](#implementation-plan)
- [Post-Mortem / Retrospective](#post-mortem--retrospective)

---

## Implementation Plan

**Use when:** You need a plan for executing a project, initiative, or change. Emphasis on sequencing, dependencies, and measurable progress.

**Audience:** Project owners, team leads, sponsors — people who need to understand what happens when, what depends on what, and how to tell if things are on track.

**Length:** Variable — driven by project complexity. The Phases table is the core; supporting sections should be concise.

### Format Specification

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

### Watch For

**Phases too high-level or too detailed.** Claude may produce phases that are so high-level they are not actionable ("Phase 1: Planning and Discovery") or so detailed they belong in a task tracker. The right granularity is: someone could read a phase and know what work needs to happen, who needs to be involved, and how to tell when it is done.

**Restated actions instead of measurable success criteria.** Watch for success criteria that just repeat the phase actions ("Success: complete the migration") rather than specifying measurable outcomes ("Success: all data migrated with <0.1% discrepancy, latency under 200ms"). Add if needed: *"Success Criteria must be measurable outcomes, not restated actions. Each criterion should answer: how would an observer confirm this phase is complete?"*

**Missing dependencies.** Claude may list phases sequentially without identifying which phases genuinely depend on previous ones versus which could run in parallel. Push for explicit dependency mapping.

**Incomplete prerequisites.** Claude often lists technical prerequisites but misses organizational ones — decisions that need to be made, approvals needed, or stakeholder alignment required before work can begin.

---

## Post-Mortem / Retrospective

**Use when:** You need to analyze what happened after a project, incident, or initiative — what worked, what did not, and what to do differently.

**Audience:** The team involved, management, and anyone who needs to learn from the experience. The tone must be blameless and learning-focused.

**Length:** Variable — typically 600-1000 words. The Root Cause Analysis should be the longest section.

### Format Specification

```xml
<output_format>
Structure as a post-mortem:

Summary: (2-3 sentences) What happened, when, and what the impact was. Lead with facts, not narrative.

Timeline: A brief chronological sequence of the key events. Include only the events that matter for understanding what happened and why — not every detail.

Root Cause Analysis: (2-3 paragraphs) What caused the outcome. Distinguish between the triggering event and the underlying conditions that allowed it to happen. Go deeper than the first explanation.

What Worked: (1-2 paragraphs) What went well or mitigated the impact. This matters — post-mortems that are only about failure miss the chance to reinforce good practices.

What Failed: (1-2 paragraphs) What broke down, and why. Be specific and blameless — focus on systems, processes, and decisions, not individuals.

Action Items: (numbered list, 3-7 items) Concrete changes to prevent recurrence or improve outcomes next time. Each item should have: what will change, who owns it, and a target date.

Write in a blameless, learning-focused tone. The goal is improvement, not accountability.
</output_format>
```

### Watch For

**Shallow root cause analysis.** Claude may produce a root cause analysis that stops at the surface level ("we didn't test enough") rather than asking why testing was insufficient (staffing? process? tooling? culture?). If the RCA lacks depth, pair this format with a root cause reasoning methodology. Add if needed: *"For the Root Cause Analysis, apply 'five whys' thinking — trace each cause back to the systemic condition that produced it. Stop when you reach something the team has the power to change."*

**Vague action items.** Action items should be concrete changes, not aspirations. "Improve our testing process" is an aspiration. "Add integration tests for payment flows to the CI pipeline by March 15, owned by [role]" is a concrete change. Each action item must specify: what will change, who owns it, and a target date.

**Missing What Worked section.** Claude may focus exclusively on failures. The What Worked section is critical — it identifies practices worth reinforcing and prevents post-mortems from becoming demoralizing exercises.

**Blame language.** Despite the explicit blameless instruction, Claude may introduce language that implies individual fault. Watch for phrases like "the engineer failed to" or "the team neglected to" and push toward systemic framing: "the process did not include" or "the system lacked safeguards for."
