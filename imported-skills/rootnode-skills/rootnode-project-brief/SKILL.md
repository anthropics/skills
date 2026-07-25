---
name: rootnode-project-brief
description: >-
  Generates a structured Project Brief — a comprehensive markdown document
  that extracts goals, architecture, knowledge file inventory, Custom
  Instructions summary, Memory contents, current state, ecosystem position,
  and key decisions from a Claude Project. Briefs serve as uploadable context
  documents: add one to any other Project for immediate deep awareness of the
  source Project's purpose, architecture, and progress. Use when user says
  "create a brief," "brief this project," "extract project context,"
  "generate a project summary for another project," "I need to share this
  project's context," "prepare this project for cross-project reference," or
  "document this project." Also use when the user is preparing to work across
  Projects and needs portable context. Do NOT use for session handoffs,
  project audits, or Memory optimization (use rootnode-session-handoff,
  rootnode-project-audit, or rootnode-memory-optimization respectively, if
  available).
license: Apache-2.0
metadata:
  author: rootnode
  version: "1.0.1"
  original-source: "Seed-project methodology synthesis"
---

# Project Brief Builder

> **Calibration:** Tier 1, Opus-primary. See repository README for model compatibility.

You generate Project Briefs — structured markdown documents that capture everything another Project needs to understand about a source Project. A brief is not a session summary or a project audit. It is a portable context artifact: upload it to any other Project and that Project immediately has deep awareness of the source Project's purpose, architecture, current state, and ecosystem position.

Briefs are consumed as knowledge files in receiving Projects. Every token matters — a 5,000-token brief in a project with 60,000 tokens of knowledge files is fine, but the same brief in a small project would dominate the context budget. Target 2,000–6,000 tokens. Be dense and structured, not verbose.

## Critical: Extraction, Not Fabrication

Every fact in the brief must come from an observable source — Custom Instructions, knowledge files, Memory entries, project file listings, or user-provided context. When information is not available for a section, mark it "Not available — {reason}" rather than inferring. A brief with gaps is more valuable than a brief with fabricated detail.

## Critical: Complete File Output

Always output the complete brief as a single markdown document. Never partial sections or diffs. The brief must be directly uploadable to another Project as a knowledge file.

---

## Generate Brief

Produce a portable, structured brief that captures the source Project's identity, architecture, current state, ecosystem position, and key decisions — every fact traceable to an observable source, every gap explicitly marked, total token budget 2,000–6,000. The method that reliably gets there: inventory the project's layers, assess its ecosystem position, assess its health, assemble against the template, then validate-and-deliver. The extraction-not-fabrication and complete-file-output rules above are hard gates inside this pipeline.

When the user asks to create a brief for the current Project:

**Step 1 — Inventory project layers.** Systematically examine every available layer:

1. **Custom Instructions.** Read the full system prompt. Extract: identity and purpose statement, scope boundaries, operational modes, key behavioral rules, output standards, and the knowledge file routing guide (which files exist and when each is consulted).

2. **Knowledge files.** Build a complete inventory. Use the project file listing for filenames and sizes. For each file, extract its purpose and content type (behavioral instructions vs. reference material) using the CI routing descriptions and, where necessary, file content. Produce a 1-2 sentence summary per file.

3. **Project Memory.** Read all Memory entries. Categorize: orientation facts (identity, role, phase), state tracking (current work, recent decisions), behavioral preferences, and active constraints.

4. **Skills and connectors.** Note installed Skills relevant to this project and any CI routing instructions that reference them. Note configured MCP connectors and how the project uses them.

5. **Active session context (optional).** If the current conversation contains important context not yet in Memory or knowledge files — active decisions, in-progress work, recent pivots — capture these with a staleness warning ("Current as of {date}, from conversation context — may not persist").

**Step 2 — Assess ecosystem position.** Determine how this project relates to the user's broader project portfolio:

- What does this project produce that other projects consume? (Artifacts, decisions, methodology, shared files)
- What does this project consume from other projects? (Shared files, briefs, strategic direction, upstream outputs)
- Which projects are upstream (this project depends on them)?
- Which projects are downstream (they depend on this project)?
- What is this project's contribution to the user's overall strategic objectives?

If an ecosystem map, project registry, or equivalent cross-project document is available in context, use it to validate and enrich the assessment. If not, derive what is possible from the project's own context and Memory. Mark inferred relationships as inferred.

**Step 3 — Assess project health.** Capture key health indicators:

- **Context budget:** Full-context or RAG mode? Approximate knowledge file token count. Any context pressure symptoms?
- **Architecture quality:** Any visible structural issues (mixed behavioral/referential content, orphan files, oversized CI)? Is the CI well-structured?
- **Currency:** When were key files last updated? Is Memory current? Any staleness indicators?
- **Completeness:** Known gaps, planned but unbuilt components, documented future work?

**Step 4 — Assemble the brief.** Produce a structured markdown document following the template in references/brief-template.md. All eight sections are mandatory. Mark sections "Not available — {reason}" when data cannot be extracted.

**Step 5 — Validate and deliver.**

1. **Token check.** Estimate the brief's token count (character count ÷ 4 as rough estimate). If it exceeds 6,000 tokens, flag this and offer to compress non-critical sections. Identify which sections carry the most weight and which can be tightened.
2. **Completeness check.** Every section populated or explicitly marked with reason for absence.
3. **Accuracy check.** Cross-reference extracted facts against source material. No detail that cannot be traced to an observable source.
4. **Freshness markers.** Generated date present. Staleness warnings on any session-context items.
5. **File naming.** Recommend a project-coded filename like `{prefix}_PROJECT_BRIEF.md` (e.g., `support_PROJECT_BRIEF.md`, `analytics_PROJECT_BRIEF.md`). A project prefix lets receiving Projects route to the correct brief explicitly when cross-project context is needed.

Deliver the complete brief as a downloadable markdown file.

---

## Validate Existing Brief

When the user has an existing brief and wants to check it against the current project state:

1. Read the existing brief in full.
2. Inventory the current project state using the same extraction process as Generate Step 1.
3. Compare section by section. Flag: outdated information, missing new components, changed architecture, shifted priorities, new ecosystem relationships.
4. Produce a staleness report organized by section, with specific update recommendations for each stale item.
5. If updates are substantial (3+ sections stale), offer to regenerate the full brief. Output the complete updated document — not diffs applied to the old version.

---

## RAG Mode Handling

When operating in a project with many knowledge files (RAG mode), the brief builder cannot reliably extract full content from every knowledge file — retrieval returns chunks, not complete files.

Handle this gracefully:

- Use the project file listing (filenames and sizes) as the authoritative inventory for the Knowledge Files table.
- Use CI routing descriptions as the primary source for file purposes and content types.
- Supplement with retrieved chunks where available, but note "Content summary based on partial retrieval" for files where only fragments were accessible.
- State clearly in the brief's header: "Generated in retrieval mode — knowledge file content summaries may be incomplete. Verify against source files for full accuracy."

Do not fabricate file content summaries from filenames alone. A row with "Purpose: See CI routing description" is better than an invented summary.

---

## Token Budget Guidance

Briefs are consumed as knowledge files in receiving Projects. Token discipline matters.

| Project Complexity | Target Brief Length | Guidance |
|--------------------|-------------------|----------|
| Simple (1-3 KFs, short CI) | 1,500–2,500 tokens | Keep all sections concise. Section 4 (Architecture) drives most length — keep KF summaries to one sentence each. |
| Moderate (4-8 KFs, structured CI) | 2,500–4,500 tokens | Standard detail level. Full KF inventory table. Architecture summary captures key structural decisions. |
| Complex (9+ KFs, rich CI, multiple modes) | 4,000–6,000 tokens | Maximum detail. May need to compress Section 6 (Key Decisions) to top 3 most impactful. Flag token count. |

If a brief exceeds 6,000 tokens, the primary compression targets are: Section 4 Architecture Summary (tighten CI summary, shorten KF content descriptions), Section 6 Key Decisions (reduce to top 3), and Section 8 Cross-Reference (keep only active references). Do not compress Sections 1-3 or 5 — these carry the highest context-per-token value for receiving Projects.

---

## Examples

### Example 1: Generate Brief for Active Project

**Input:** "Create a brief for this project."

**Actions:**
1. Read CI — extract identity, scope, modes, behavioral rules, KF routing.
2. List all knowledge files from project file listing. Retrieve content summaries via CI descriptions and file access.
3. Read Memory entries — categorize orientation, state, preferences, constraints.
4. Note relevant Skills and connectors.
5. Assess ecosystem position from available cross-project context.
6. Assess project health — context mode, architecture quality, currency.
7. Assemble all eight sections following the template.
8. Validate token count, completeness, accuracy. Deliver as downloadable markdown.

**Result:** Complete brief (2,000–6,000 tokens) as a markdown file named `{code}_PROJECT_BRIEF.md`.

### Example 2: Validate Stale Brief

**Input:** User uploads an existing brief and asks "Is this still accurate?"

**Actions:**
1. Read the existing brief.
2. Inventory current project state.
3. Compare section by section — flag that Phase has advanced from 14 to 17, two new KFs added, one KF removed, Memory updated with new constraints.
4. Produce staleness report with specific update recommendations per section.
5. Offer to regenerate since 4+ sections need updates.

**Result:** Staleness report identifying specific changes, followed by regenerated brief if requested.

---

## When to Use This Skill

**Use when:**
- Creating a portable context document for cross-project reference
- Preparing to share project context with another Project
- Documenting a project's architecture and current state for reference
- Updating a previously generated brief after project changes
- Validating whether an existing brief is still current

**Do NOT use when:**
- Wrapping up a session for continuation in the same project → rootnode-session-handoff if available
- Diagnosing or scoring project quality → rootnode-project-audit if available
- Rebalancing Memory, CI, and knowledge file content → rootnode-memory-optimization if available
- Analyzing context budget health → rootnode-context-budget if available

---

## Troubleshooting

**Brief is too long (>6,000 tokens).** Compress Architecture Summary (tighten CI description, shorten KF summaries) and Key Decisions (top 3 only). Do not compress Identity, Scope, Current State, or Ecosystem Position — these are highest value.

**Cannot access knowledge file contents.** Project is in RAG mode. Use CI routing descriptions for file purposes. Note partial retrieval in the brief header. Do not fabricate content summaries.

**Ecosystem position is thin.** No ecosystem map, registry, or cross-project context available. Derive what is possible from the project's own CI and Memory. Mark ecosystem section as "Derived from project-internal context only — verify against full portfolio view."

**Brief conflicts with session handoff.** These are different artifacts. A session handoff captures temporal work state for continuation in the same project. A brief captures structural project identity for cross-project reference. If both are needed in the same session, produce them as separate documents.
