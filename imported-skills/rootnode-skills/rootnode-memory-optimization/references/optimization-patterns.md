# Optimization Patterns

Trimming patterns for knowledge files and cross-layer alignment patterns for resolving misplaced content. Used during Stage 3 of the optimization pipeline. Each pattern includes detection criteria and before/after examples.

---

## Knowledge File Trimming Patterns

### Pattern 1: Vision/Mission Compression

**Detection:** A knowledge file opens with a multi-paragraph project vision or mission statement that duplicates what Custom Instructions and/or Memory already provide.

**Why it's trimmable:** Memory now carries the project's identity and orientation. Custom Instructions carry the behavioral architecture. A knowledge file restating "what this project is" wastes tokens on content the user already anchored in higher-priority layers.

**Action:** Replace the multi-paragraph vision with a one-line pointer.

**Before:**
```
## Project Vision
root.node is a modular prompt engineering system designed to make Claude
measurably better at complex tasks. It provides reusable building blocks —
identity, reasoning, and output specifications — that compose into tested,
high-performance prompts. The system is built for practitioners who need
Claude to produce professional-quality output consistently...
[3-4 more paragraphs]
```

**After:**
```
## Project Vision
Defined in Custom Instructions and Memory. This file tracks [specific purpose of this file].
```

### Pattern 2: Component Description Compression

**Detection:** A knowledge file contains paragraph-length descriptions of other project files, duplicating the Custom Instructions' knowledge file guide.

**Why it's trimmable:** The CI's knowledge file guide already tells Claude what each file does and when to read it. Paragraph-level descriptions in a knowledge file force Claude to read the same routing information twice.

**Action:** Replace paragraph descriptions with a component index — one line per file (filename + single-sentence purpose).

**Before:**
```
## System Components

### PROMPT_COMPILER.md
The Prompt Compiler is the primary tool for building new Claude prompts.
It implements a four-stage pipeline (Parse, Select, Construct, Validate)
that transforms task descriptions into optimized prompts using the 5-layer
architecture. The Compiler supports three modes: Prompt Mode for standalone
prompts, Project Mode for full Claude Project scaffolds...
[similar blocks for 10+ other files]
```

**After:**
```
## Component Index
- PROMPT_COMPILER.md — Four-stage prompt compilation pipeline
- AUDIT_FRAMEWORK.md — Six-dimension Project scoring rubric
- OPTIMIZATION_REFERENCE.md — Structural fix patterns and behavioral countermeasures
[one line per file]
```

### Pattern 3: Completed Phase Archival

**Detection:** Build history or phase records contain detailed entries for fully completed, non-controversial phases. The phases involved straightforward execution without significant tradeoffs or reusable lessons.

**Why it's trimmable:** Phase records that document routine completion ("Phase 5: Built the five domain packs") add token cost without adding decision-making value. Phases that involved tradeoffs or produced reusable patterns retain value.

**Action:** Compress routine phase entries to one line. Keep detailed entries for phases with decision rationale, tradeoffs, or reusable patterns.

**Before:**
```
### Phase 5: Domain Pack Build
Built the five domain packs (Business Strategy, Software Engineering,
Content & Communications, Research & Analysis, Agentic & Context).
Each pack contains 11-12 approaches across identity, reasoning, and output
categories. The packs are self-contained units that function independently
of the core block libraries. Build was straightforward — followed the
established pattern from the core libraries.
Duration: 2 sessions.
```

**After:**
```
- Phase 5: Built five domain packs (11-12 approaches each). Straightforward.
```

**Keep detailed when:** The phase involved architectural tradeoffs (e.g., "decided to inline identity approaches rather than reference core libraries"), produced patterns reused later, or documented failures worth avoiding.

### Pattern 4: Redundant State Tracking

**Detection:** A knowledge file tracks "current state" information — current phase, file counts, active constraints — that Memory now handles as always-loaded orientation.

**Why it's trimmable:** State tracking in a knowledge file is searched on demand. The same information in Memory is loaded every conversation. If Memory carries the current state, the knowledge file copy is redundant.

**Action:** Remove state tracking from the knowledge file. Verify Memory carries each piece of state information before removing it.

**Before:**
```
## Current State
- Phase: 3 (Burn-in)
- Knowledge files: 11 of 12 ceiling
- Active constraint: No new knowledge files until file count resolved
- Deferred: Context engineering section expansion (post-burn-in)
```

**After:**
Remove the section entirely — all four facts should be Memory edits.

**Caution:** Verify each fact IS in Memory before removing from the knowledge file. The knowledge file entry is the fallback if Memory doesn't have it yet.

### Pattern 5: Cross-File Deduplication

**Detection:** The same fact, decision, or content appears in both an institutional memory file (build_context.md) AND another knowledge file.

**Why it's trimmable:** Duplication across knowledge files means Claude may encounter conflicting versions if one is updated and the other isn't. Identify the authoritative location and keep only that copy.

**Action:** Identify which file is the authoritative source for the content. Keep it there. Remove it from the other file or replace with a one-line pointer.

**Before:**
```
[In build_context.md]
The system uses a 5-layer architecture: Identity, Objective, Context,
Reasoning, Output + Quality Control...

[In MASTER_FRAMEWORK.md]
The system uses a 5-layer architecture: Identity, Objective, Context,
Reasoning, Output + Quality Control...
```

**After:**
```
[In build_context.md]
5-layer architecture defined in MASTER_FRAMEWORK.md.

[In MASTER_FRAMEWORK.md — unchanged, authoritative source]
The system uses a 5-layer architecture: Identity, Objective, Context,
Reasoning, Output + Quality Control...
```

---

## Cross-Layer Alignment Patterns

### Pattern A: Orientation in Knowledge Files → Memory

**Detection:** Current phase, active constraints, key decisions, or file count limits buried inside a knowledge file where they're only discovered if Claude searches that file.

**Why it's misaligned:** These are high-frequency orientation facts that every conversation benefits from. Searching for them on demand means some conversations start without critical context.

**Migration action:**
1. Identify the orientation fact in the knowledge file
2. Write a Memory edit (concise, self-contained, non-behavioral, under 500 characters)
3. Compress or remove the knowledge file section (pointer or index entry replaces the full content)

**Example:**
- Knowledge file says: "The project is currently in Phase 3 (Burn-in). During burn-in, no new features are added — only fixes, calibration, and stress testing."
- Memory edit: "Project is in Phase 3 (burn-in): no new features — only fixes, calibration, and stress testing."
- Knowledge file replacement: "Current phase tracked in Memory."

### Pattern B: Behavioral Rules in Knowledge Files → Custom Instructions

**Detection:** "Always do X" or "Never do Y" statements in knowledge files. Procedural instructions, formatting requirements, or behavioral constraints living outside the CI.

**Why it's misaligned:** Custom Instructions are always-loaded behavioral architecture. Behavioral rules in knowledge files are only enforced when Claude searches that file. Rules that should apply to every conversation need always-loaded placement.

**Migration action:**
1. Identify the behavioral rule in the knowledge file
2. Add to Custom Instructions in the appropriate section (output standards, behavioral constraints, or mode definitions)
3. Remove from the knowledge file or replace with a pointer: "Behavioral rule defined in Custom Instructions."

**Example:**
- Knowledge file says: "When producing updated files, always output the complete file. Never output diffs or partial sections."
- Custom Instructions addition: Add to output standards section: "When producing updated files, always output the complete file as a single, separately copyable unit. Never output diffs, patches, or partial sections."
- Knowledge file replacement: "Complete-file-output rule defined in Custom Instructions."

### Pattern C: Reference Material in Custom Instructions → Knowledge File

**Detection:** Data tables, extended examples, framework descriptions, or multi-paragraph explanations in the Custom Instructions. CI has become bloated with reference-depth content.

**Why it's misaligned:** Custom Instructions are always-loaded. Every token in CI is consumed in every conversation regardless of relevance. Reference material that's only needed in specific conversations belongs in a knowledge file where it's searched on demand.

**Migration action:**
1. Identify the reference content in CI
2. Move to an existing knowledge file or create a new one
3. Replace in CI with a routing instruction: "For [topic], see [filename]."
4. Output the complete updated Custom Instructions if the user requests them

**Example:**
- CI contains a 20-row table mapping error codes to fix procedures
- Move the table to a reference knowledge file (e.g., error-codes.md)
- CI replacement: "For error code resolution, see error-codes.md."

### Pattern D: Reference Material in Memory → Knowledge File

**Detection:** Multi-sentence explanations, procedural content, or detailed rationale crammed into Memory edits. The 500-character limit is being forced to hold reference-depth content.

**Why it's misaligned:** Memory is for concise orientation facts. When a Memory edit is straining against the character limit to explain a procedure or justify a decision, the content belongs in a knowledge file. Memory should hold a one-line pointer; the knowledge file holds the depth.

**Migration action:**
1. Identify the over-stuffed Memory edit
2. Move the detailed content to a knowledge file
3. Replace the Memory edit with a concise orientation pointer

**Example:**
- Memory edit (493 characters): "The system uses progressive disclosure architecture where SKILL.md bodies contain core instructions under 500 lines and reference files in the references/ directory contain detailed documentation, extended examples, and pattern libraries that Claude loads on demand to minimize context consumption..."
- Replacement Memory edit: "Skills use progressive disclosure: core instructions in SKILL.md, detailed docs in references/ files loaded on demand."
- Knowledge file gets the full architectural description.
