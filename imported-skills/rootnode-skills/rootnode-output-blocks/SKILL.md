---
name: rootnode-output-blocks
description: >-
  Tested output format specifications for Claude prompts. Use when the user
  wants a specific deliverable structure — retrieving, reviewing,
  customizing, or building output formatting. Trigger on: "give me the
  Executive Brief format," "show me the output template for," "I need the
  Decision Matrix structure," "show me available output formats," "build a
  custom output format for." Provides 10 ready-to-use structures (executive
  briefs, technical designs, research summaries, implementation plans,
  decision matrices, competitive analyses, post-mortems, stakeholder updates,
  strategic memos, process documentation) plus a custom template, with
  per-section length guidance and format constraints tested against Claude
  formatting defaults. If unsure which format fits, use
  rootnode-block-selection first if available. Do NOT use for evaluating
  existing prompts (use rootnode-prompt-validation if available) or choosing
  reasoning/identity approaches (use rootnode-block-selection if available).
license: Apache-2.0
metadata:
  author: rootnode
  version: "1.1"
  original-source: "BLOCK_LIBRARY_OUTPUT.md"
---

# Output Format Selection for Claude Prompts

> **Calibration:** Tier 1, Opus-primary. See repository README for model compatibility.

Tested output format specifications that control what Claude's deliverable looks like — structure, sections, length, and format. Without an explicit output format, Claude defaults to its own formatting preferences, which often means overlong prose with excessive bullet points.

## When to Use This Skill

Use this Skill when you need to:
- Choose an output format for a Claude prompt you are building
- Structure a deliverable (brief, memo, plan, analysis, etc.)
- Design a custom output format for a deliverable type not covered here
- Fix output quality problems caused by missing or vague format instructions

This Skill provides the format specification (Layer 5 of a well-structured prompt). It does not cover identity, reasoning methodology, or quality control — for those, see rootnode-block-selection or rootnode-prompt-compilation if available.

## Quick-Reference: Deliverable Type → Format

| You need... | Use this format | Reference file |
|---|---|---|
| A decision or recommendation for senior leadership | Executive Brief | references/executive-formats.md |
| A strategic argument or policy position for decision-makers | Strategic Memo | references/executive-formats.md |
| A progress report or status update for stakeholders | Stakeholder Update | references/executive-formats.md |
| An architecture proposal or RFC for technical reviewers | Technical Design Document | references/technical-formats.md |
| A workflow, runbook, or SOP for process executors | Process Documentation | references/technical-formats.md |
| Evidence synthesis or research findings | Research Summary | references/analytical-formats.md |
| A structured comparison of options against criteria | Decision Matrix | references/analytical-formats.md |
| A market positioning or competitor assessment | Competitive Analysis | references/analytical-formats.md |
| A project plan with phases, dependencies, and timelines | Implementation Plan | references/operational-formats.md |
| An incident analysis or project retrospective | Post-Mortem / Retrospective | references/operational-formats.md |
| Something not listed above | Build a custom format (see below) | — |

**Selection principle:** Match the format to the audience and their primary question. Executives ask "what should we do?" → Executive Brief or Strategic Memo. Engineers ask "how does this work?" → Technical Design Document. Operators ask "what do I do next?" → Process Documentation or Implementation Plan. Analysts ask "what did we find?" → Research Summary.

## How to Use a Format Specification

Each format in the reference files includes:
1. **Use-when guidance** — the scenario and audience it fits
2. **Complete XML specification** — copy directly into your prompt's output layer
3. **Per-section length guidance** — word counts, sentence counts, or item counts for each section
4. **Watch-for notes** — Claude's common failure modes with that format and specific countermeasure language to add

To apply a format: copy the `<output_format>` XML block into your prompt. Customize section names and lengths to your situation. Remove sections that are not relevant. The specifications are tested starting points — adjust to match what your audience actually needs.

## Critical: Controlling Claude's Formatting Defaults

Claude has strong formatting tendencies that output specifications must actively manage:

**Bullet point overuse.** Claude defaults to bullet points for almost everything. If you want prose, say "write in prose" explicitly in the relevant section. If you want a table, say "present as a table with columns: X, Y, Z."

**Length inflation.** Claude tends to write longer than necessary. Per-section length guidance (e.g., "2-3 sentences" or "1 paragraph") is more effective than total word counts alone. Specify both when possible.

**Burying the lead.** Claude often builds up to its conclusion rather than leading with it. Executive-facing formats (Executive Brief, Strategic Memo, Stakeholder Update) all specify lead-with-the-answer structure — enforce this explicitly if Claude reverts.

**Hedging on assessments.** In formats requiring judgment (Competitive Analysis, Decision Matrix, Post-Mortem), Claude may soften findings. The watch-for notes in each format specification include countermeasure language to add when this happens.

## Building Custom Output Formats

When no existing format fits, use this template:

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

### Design Principles for Custom Formats

**Lead with what the reader wants most.** Executives want the recommendation first. Engineers want the architecture first. Researchers want the findings first. Put the highest-value section at the top.

**Specify length per section, not just total.** "500 words" tells Claude the total budget but not how to allocate it. "Bottom Line: 2-3 sentences. Analysis: 3 paragraphs. Next Steps: 3-5 items." tells Claude how much attention each section deserves.

**Constrain the format where it matters.** If you want prose, say "write in prose" — otherwise Claude defaults to bullet points. If you want a table, say "present as a table with columns: X, Y, Z" — otherwise Claude may use bullets where a table would be clearer.

**Name sections descriptively.** "Analysis" is vague. "Competitive Assessment" or "Root Cause Analysis" tells Claude what kind of analysis belongs there. Section names are implicit instructions.

## Reference Files

This Skill includes four reference files with complete format specifications. Read the relevant file when you need the full XML specification, section details, and watch-for guidance for a specific format:

- **references/executive-formats.md** — Executive Brief, Strategic Memo, Stakeholder Update. Read when the deliverable targets senior leadership, decision-makers, or project stakeholders.
- **references/technical-formats.md** — Technical Design Document, Process Documentation. Read when the deliverable targets engineers, technical reviewers, or process executors.
- **references/analytical-formats.md** — Research Summary, Decision Matrix, Competitive Analysis. Read when the deliverable involves evidence synthesis, structured comparison, or market assessment.
- **references/operational-formats.md** — Implementation Plan, Post-Mortem / Retrospective. Read when the deliverable involves project execution planning or incident/project analysis.

## Troubleshooting

**Output ignores the format specification.** The format block may be positioned too late in the prompt. Place the `<output_format>` block after the identity and reasoning instructions but before any input data. Claude processes instructions with a primacy-recency bias — format instructions buried after long input sections lose influence.

**Sections are the right structure but wrong length.** Add explicit per-section length constraints if you only specified a total word count. "Total length: 800 words" gives Claude a budget; "Key Findings: 3-5 items, each 2-3 sentences. Analysis: 2-3 paragraphs per theme." tells Claude how to allocate it.

**Claude adds sections not in the specification.** Add a constraint: "Use only the sections specified above. Do not add additional sections, appendices, or disclaimers."

**Format works for simple inputs but breaks on complex ones.** The format may need more sections or different length guidance for complex inputs. Consider whether the task actually needs a different format rather than a stretched version of the current one.

**Domain-specific deliverables not covered here.** For specialized formats (investment cases, RFCs, ADRs, content briefs, policy briefs, literature reviews), domain-specific output formats exist in the rootnode domain Skills if available. This Skill covers domain-agnostic formats that work across contexts.
