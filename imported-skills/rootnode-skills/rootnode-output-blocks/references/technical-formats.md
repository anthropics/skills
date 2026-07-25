# Technical Formats

Output format specifications for deliverables targeting engineers, technical reviewers, and process executors. Each format includes the complete XML specification, per-section guidance, and watch-for notes on Claude's common failure modes.

---

## Table of Contents

- [Technical Design Document](#technical-design-document)
- [Process Documentation](#process-documentation)

---

## Technical Design Document

**Use when:** You need to propose a technical solution that will be reviewed by engineers and technical leaders. Optimized for clarity of architectural decisions and tradeoffs.

**Audience:** Engineers, tech leads, architects, technical decision-makers.

**Length:** Variable — driven by the complexity of the design. Typically 1000-2500 words for a focused component design; longer for system-level proposals.

### Format Specification

```xml
<output_format>
Structure as a technical design document:

Problem Statement: (1 paragraph) What problem this design solves, why it matters, and what constraints bound the solution.

Proposed Solution: (2-4 paragraphs) The architecture, key components, and data flow. Use a clear structure — describe the system top-down or trace the primary user flow. Include pseudocode or data schemas where they add clarity.

Key Design Decisions: (1-2 paragraphs per decision) For each major architectural choice, state what was decided, what alternatives were considered, and why this approach was chosen. This is the most important section — reviewers need to evaluate your reasoning, not just your conclusion.

Implementation Approach: (table or phased list) How this would be built — phases, dependencies, and rough sequencing. Not a project plan, but enough to assess feasibility.

Open Questions: (numbered list) Anything unresolved that needs input before proceeding. For each, state what the question is, who should answer it, and what the decision's impact is.

Write for a technical audience. Prioritize precision over accessibility.
</output_format>
```

### Watch For

**Abstract descriptions without concrete details.** Claude may describe the system in abstract terms without getting concrete about data structures, API contracts, or component boundaries. If the design feels like a high-level pitch rather than an architectural proposal, add this countermeasure: *"Include specific details: data models, API signatures, or interface contracts for the key components. The design should be precise enough that an engineer could begin implementation from it."*

**Too much implementation detail for a senior audience.** Conversely, if the audience is more senior, add: *"Focus on architectural decisions and tradeoffs. Omit implementation details below the component level."*

**Weak Key Design Decisions section.** Claude may state what was decided without explaining what alternatives were considered or why they were rejected. This section is the core of the document — if it reads as a list of choices without tradeoff analysis, push for deeper reasoning.

---

## Process Documentation

**Use when:** You need to document a workflow, procedure, or operational process that others will follow. Optimized for clarity and usability by someone executing the process.

**Audience:** Anyone executing the process for the first time. Write so that someone familiar with the tools but new to this specific process could follow each step.

**Length:** Variable — driven by process complexity. Prioritize completeness over brevity for process docs.

### Format Specification

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

### Watch For

**Wrong level of granularity.** Claude may write steps that are too high-level ("Configure the system appropriately") or too detailed ("Click the blue button in the upper right corner of the screen, then select..."). The right level is: someone familiar with the tools but new to this specific process could follow each step.

**Missing decision points.** If a step requires judgment ("if the data looks correct"), specify what "correct" means. Every conditional in the process should have explicit criteria for each path.

**No exception handling.** Claude may produce a happy-path-only document. The Exception Handling section is critical for production processes — push for the 2-4 most common failure modes and their resolutions.
