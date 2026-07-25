# Conversion Guide: root.node → Claude Skills

This guide maps root.node architectural concepts to their Claude Skills equivalents and provides conversion patterns for each component category.

---

## Concept Mapping

| root.node Concept | Skills Equivalent | Conversion Notes |
|---|---|---|
| Block | Skill (or section within a Skill) | Blocks under ~500 tokens that pair together → merge into one Skill. Blocks over ~5000 tokens → split into SKILL.md + references/. |
| Block Library | Skill with references/ directory | The library's selection guidance becomes the SKILL.md body; individual block documentation moves to references/. |
| Domain Pack | One Skill per pack | Each domain pack is self-contained. The pack's Compiler integration section becomes inline guidance within the Skill. |
| Knowledge File | Reference file in references/ | Long-form documentation moves to references/. Short, actionable guidance stays in SKILL.md body. |
| Custom Instructions | SKILL.md body (core instructions) | The Compiler and Optimizer system prompts decompose into multiple Skills, each handling a distinct workflow stage. |
| Compiler Pipeline | Multiple coordinating Skills | The four-stage pipeline (Parse → Select → Construct → Validate) cannot be a single Skill — too long. Split into methodology Skill + block selection Skill + validation Skill. |
| Optimizer Pipeline | Multiple coordinating Skills | Same pattern. Audit framework Skill + anti-pattern detection Skill + behavioral tuning Skill + memory optimization Skill. |
| Behavioral Countermeasure | Inline instruction within relevant Skill | Do not create a standalone "countermeasures" Skill. Inline the relevant countermeasures into each Skill where they apply. Exception: the behavioral tuning Skill, which needs the full countermeasure catalog because its purpose IS behavioral diagnosis. |
| Prompt Scorecard | Section within validation Skill | The six-dimension scoring rubric stays together as a single tool. |
| Project Scorecard | Core of the audit Skill | The six-dimension project scoring rubric is the primary deliverable of the project-audit Skill. |
| Worked Example | Example section in SKILL.md or reference file | Short examples (input → output) inline in SKILL.md. Full worked examples move to references/. |
| Quality Gate | Checklist section in SKILL.md | Convert to actionable verification steps at the end of the Skill's workflow. |

---

## Component Conversion Patterns

These are the five structural patterns for converting root.node components into Skills. Apply the appropriate pattern based on the component type.

### Pattern 1: Pipeline Decomposition

**Applies to:** Compiler Pipeline, Optimizer Pipeline, or any multi-stage workflow exceeding ~5000 tokens.

**Structure:** Split the pipeline into multiple Skills, each handling a distinct concern. Each Skill gets its own activation context and description triggers.

**Decision logic:**
- Identify the pipeline's distinct concerns (e.g., scoring vs. detecting patterns vs. tuning behavior vs. rebalancing layers).
- Each concern with a distinct activation context becomes its own Skill.
- Shared methodology that multiple Skills need is inlined in each (standalone-first), not centralized.
- Cross-Skill coordination happens through soft pointers and additive composition, not dependencies.

**Example — Optimizer decomposition:**
The Optimizer's four concerns (scoring projects, detecting anti-patterns, tuning behavior, rebalancing context layers) have distinct activation contexts. "Why is Claude so verbose?" needs behavioral tuning, not the full scorecard. Separate Skills activate more precisely. Each inlines the narrow slice of shared methodology it needs (e.g., the audit Skill inlines reconstruction principles rather than deferring to the behavioral tuning Skill).

**Example — Compiler decomposition:**
Same reasoning. "Review my prompt" needs validation, not the full compilation pipeline. "What reasoning approach should I use?" needs block selection, not assembly instructions. The compilation Skill, block selection Skill, and validation Skill each handle a distinct phase of the workflow.

### Pattern 2: Block Library Conversion

**Applies to:** Identity Block Library, Reasoning Block Library, Output Block Library, or any collection of related templates/approaches.

**Structure:** One Skill per library. SKILL.md contains selection guidance (decision trees, routing tables). Individual block/template documentation moves to references/.

**Decision logic:**
- Individual blocks are too small for standalone Skills (~200-500 tokens each) and their activation contexts overlap heavily.
- One Skill per library gives Claude a single entry point per selection decision.
- References/ files group blocks by affinity (e.g., strategic identities together, analytical reasoning together) so Claude reads only the relevant subset.
- Each library Skill is a self-contained catalog — no cross-references between identity, reasoning, and output libraries.
- Forward pointers to the router Skill (rootnode-block-selection) differentiate catalog retrieval from cross-category routing.

**Reference file organization:**
- Group by affinity, not alphabetically. Blocks sharing failure modes or usage patterns go together.
- Each reference file contains complete template text (XML blocks, format specifications) — these are the core IP users paste into prompts.
- Include usage guidance and failure modes alongside each template.

### Pattern 3: Domain Pack Conversion

**Applies to:** Domain-specific methodology packs (Business Strategy, Software Engineering, Content & Communications, Research & Analysis, Agentic & Context).

**Structure:** One Skill per pack, fully self-contained. SKILL.md contains selection guidance, all identity templates (inlined), and behavioral countermeasures. References/ contain reasoning approaches and output formats.

**Decision logic:**
- Domain packs have distinct activation contexts — a user working on M&A analysis doesn't need software engineering blocks.
- Each domain pack inlines its own identity approaches (3 per pack) rather than referencing core library Skills. The standalone constraint wins over duplication cost.
- Each pack includes its own selection guidance, behavioral countermeasures, and quality checks as a self-contained unit.
- Reference file names are standardized: `reasoning-approaches.md`, `output-formats.md`.
- A user installing only one domain pack gets the full domain methodology without needing core libraries.

**Critical negative triggers for domain packs:**
- Software Engineering: "Do NOT use for general coding help, writing code, or debugging" — without this, any engineering query overtriggers.
- Content & Communications: "Do NOT use for writing content directly — this Skill builds prompts that produce better content."
- Agentic & Context: "Design agent behavior, not use agents" — distinguish designing agent systems from using Claude as an agent.

### Pattern 4: Scorecard/Rubric Conversion

**Applies to:** Prompt Scorecard, Project Scorecard, or any multi-dimension evaluation framework.

**Structure:** The scoring rubric stays together as a single Skill. Anchored criteria (1-5 scales) inline in SKILL.md body — they are the core methodology. Extended diagnostic tools and symptom maps move to references/.

**Decision logic:**
- Scoring dimensions are interdependent — splitting them across Skills loses the holistic evaluation.
- The 1-5 anchoring criteria must be inline (they define the methodology's scoring standard).
- Diagnostic question banks, symptom-fix maps, and diagnostic flows can be reference files.

### Pattern 5: New Methodology Skill

**Applies to:** Skills designed from scratch (not converted from existing root.node files), such as rootnode-memory-optimization.

**Structure:** Standard SKILL.md + references/ structure. Design specification is the input, not an existing source file.

**Decision logic:**
- Set `metadata.original-source: "NEW"` for traceability.
- Follow the same build pipeline — no conversion shortcuts just because there's no source file.
- Platform terminology exceptions apply when the Skill operates ON Claude Projects features (Memory, Custom Instructions, knowledge files).
- Composition testing is especially important — new Skills must route cleanly alongside the existing inventory.

---

## Content Adaptation Patterns

### Stripping root.node Internal Language

| Original (root.node) | Adapted (Skills) |
|---|---|
| "Select the Strategic Advisor identity block" | "Use the Strategic Advisor approach" |
| "Consult the Block Library for options" | "See references/identity-blocks.md for available approaches" |
| "The Compiler's Parse stage extracts..." | "Start by extracting from the task description..." |
| "This block addresses the Kitchen Sink anti-pattern" | "This methodology avoids the common failure of overloading a prompt with unnecessary instructions" |
| "Per the Optimization Notes..." | "Claude tends to..." |
| "The seed project demonstrates..." | [Remove — not relevant outside root.node] |
| "Route to the relevant Domain Pack" | "For deeper specialization, see references/domain-packs.md" |

### Preserving Countermeasures

Behavioral countermeasures should be inlined where they apply, not referenced as external instructions. Example:

**Original (root.node — separate countermeasure section):**
```
<behavioral_calibration>
Anti-verbosity: Match response length to task complexity.
</behavioral_calibration>
```

**Adapted (Skills — inline within instructions):**
```markdown
## Critical: Output Length
Match response length to the complexity of the finding. A simple
anti-pattern detection needs 2-3 sentences, not two paragraphs.
When scoring dimensions, state the score, the evidence, and the
fix — nothing else.
```

### Tone Calibration in Produced Skill Content

When converting root.node content into Skill prose, apply the "explain the why" calibration (canonical: `root_AGENT_ENVIRONMENT_ARCHITECTURE.md §4.11`). The principle: use imperative voice where the constraint genuinely warrants it; use reasoned voice where reasoning carries equal or greater force. Source content authored under earlier conventions sometimes leans on imperative-without-rationale ("MUST not skip step 3", "ALWAYS verify before completion") in places where the reasoning would carry more weight. Convert with judgment, not mechanically.

**When imperative voice is correct (preserve as-is):**

- Spec compliance constraints — "the description field MUST be ≤ 1024 characters" (the spec is the authority).
- Safety boundaries — "NEVER push to main without explicit authorization" (the boundary is the authority).
- Irreversible operations — "do NOT force-push to shared branches" (the cost of model rationalization exceeds the cost of false-positive halts).
- Reserved-word constraints — "name MUST NOT use 'claude' or 'anthropic'" (the platform rejects these regardless of reasoning).

**When reasoned voice is correct (rewrite source content):**

- Procedural guidance — "verify before reporting completion because untested claims compound across sessions" (rather than "ALWAYS verify").
- Decision rubrics — "prefer routing-surface SKILL.md sections because procedural depth in SKILL.md duplicates references" (rather than "ALWAYS keep SKILL.md as routing surface").
- Design recommendations where multiple reasonable choices exist.
- Tradeoff explanations and edge-case handling.

**Anti-pattern: caps-everywhere.** Source root.node content sometimes uses "MUST," "ALWAYS," "NEVER" formatted in caps for emphasis. Inline-converting this to Skill content produces a standing context where every instruction reads as non-negotiable — which dilutes the actual non-negotiables. The model loses the signal that distinguishes a hard constraint from a strong recommendation. Calibrated voice produces more reliable compliance because the model can verify the reasoned grounding against the situation it is in.

**Conversion rule.** When inlining source content, ask per instruction: is this a spec constraint or safety boundary, or is it procedural guidance? Apply the corresponding voice. Substantive claims unchanged; only surface phrasing.

The calibration is permitted within methodology preservation per `root_SKILL_BUILD_DISCIPLINE.md §7.2` (tone calibration is a within-warrant change). Successor Skill builds may apply this rewrite without invoking Gate 2 — the underlying claim is preserved, only the voice changes.

---

## Description Field Templates

Use these templates as starting points. Customize per Skill.

### Optimizer Skills Template
```
[What it does — specific methodology]. Use when evaluating, auditing,
diagnosing, or improving an existing Claude Project. Trigger on: [3-5
specific phrases]. Also use when [implicit trigger contexts].
```

### Compiler Skills Template
```
[What it does — specific methodology]. Use when building, designing,
creating, or structuring a Claude prompt or system prompt from a task
description. Trigger on: [3-5 specific phrases]. Also use when
[implicit trigger contexts].
```

### Block Library Skills Template
```
[What it provides — selection guidance + tested approaches]. Use when
the user wants a specific [identity/reasoning/output] template —
retrieving, reviewing, customizing, or building. Trigger on: [3-5
specific phrases]. If user is unsure which fits, use
rootnode-block-selection first.
```

### Domain Pack Skills Template
```
Specialized [domain] prompt methodology for Claude. Provides [N]
tested approaches for [specific task types within domain]. Use when
building prompts for [domain-specific tasks]. Trigger on: [3-5
domain-specific phrases].
```

### Skill Builder Template
```
[What it does — packaging methodology]. Use when building, converting,
reviewing, or revising Skills. Trigger on: [build/convert/review
phrases]. Do NOT use for [prompt compilation / project auditing /
methodology design].
```

---

## Standalone-First Composition

Every Skill must deliver its complete value when installed alone. Where Skills share underlying methodology, each inlines the narrow slice it needs rather than referencing another Skill. Cross-Skill references are permitted only as soft pointers ("for deeper specialization, see X if available") that add value when both Skills are present but whose absence never degrades the installing Skill's functionality. No Skill may fail, produce incomplete output, or defer a user request because another Skill is not installed.

**Duplication tolerance:** When the standalone constraint requires inlining shared methodology, prefer inlining the narrow slice each Skill needs over creating a dependency. A few hundred tokens of duplicated guidance across Skills is acceptable. A Skill that fails or produces incomplete output when installed alone is not.

**Composition benefit:** When multiple Skills are installed, they compose additively — each adds its specialized depth. The audit Skill identifies that Behavioral Calibration scores low; if the behavioral tuning Skill is also active, the user can then request deep countermeasure work. This is additive composition, not a dependency chain.

**Illustrative examples:**
- Optimizer Skills (T1): Each fully self-contained. The project-audit Skill inlines reconstruction principles rather than deferring to behavioral tuning. The memory-optimization Skill inlines its layer placement framework rather than deferring to project-audit.
- Domain Packs (T4): Highest duplication cost, but standalone wins. Each domain pack inlines its own identity approaches rather than referencing core library Skills. A user installing only the business strategy pack gets the full domain methodology without needing core libraries.
- Router/Catalog differentiation: The block-selection Skill (router) uses choosing/comparing trigger language. Library Skills (catalogs) use retrieving/customizing language. Forward pointers create clean handoff without dependency.
