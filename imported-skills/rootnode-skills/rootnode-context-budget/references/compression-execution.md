# Compression Execution

Guidance for recommending and executing compression within a context budget optimization. Contains the Content-Type Classification, compression tiers, MCP overhead estimation detail, compression sequencing, the Diminishing Returns Checkpoint, and the RAG-Acceptance Decision Point.

## Table of Contents

1. [Content-Type Classification](#content-type-classification)
2. [Compression Tiers](#compression-tiers)
3. [MCP Overhead Estimation](#mcp-overhead-estimation)
4. [Budget-Constrained Projects](#budget-constrained-projects)
5. [Sequencing Compression Rounds](#sequencing-compression-rounds)
6. [Diminishing Returns Checkpoint](#diminishing-returns-checkpoint)
7. [RAG-Acceptance Decision Point](#rag-acceptance-decision-point)

---

## Content-Type Classification

Before recommending compression depth for any file, classify its content:

**Type A — Prose and Narrative (high yield, low risk):** Design rationale, process documentation, strategic context, onboarding guides, explanatory notes, methodology descriptions, meeting summaries, project histories. This content compresses well because the essential information can be restated in fewer words without losing meaning.

**Type B — Precision Reference (low yield, high risk):** API endpoint specifications, database schemas with field enumerations, configuration syntax with exact parameter names, test payloads with exact assertion values, legal citation tables, code snippets and expression syntax, data dictionaries, compliance matrices, protocol specifications. This content resists compression because the exact details — field names, parameter values, syntax patterns — ARE the content.

**Classification rules:**
- Classify at the file level AND at the section level. A file may be 60% Type A / 40% Type B.
- When a file is mixed, state the distribution (e.g., "~60% Type A / ~40% Type B") and apply compression targets to the Type A portions only.
- When in doubt: "If I summarized this section in half the words, would the user still be able to execute their task with the same precision?" If no, it is Type B.
- The transition from Type A targets to Type B targets in an optimization plan is the mandatory checkpoint boundary.

**Connection to scoring:** Content-type classification integrates with Dimension 4 (Degradation Severity) in the evaluation rubric. A file scoring high on Degradation Severity specifically because its content is precision reference (Type B) should not receive aggressive compression even if its Token Cost score would normally trigger it. See the Compression Risk Assessment in `evaluation-rubric.md`.

---

## Compression Tiers

When recommending compression, provide a safest-to-most-aggressive approach:

1. **Safe (10–20% savings):** Remove redundant examples, trim verbose explanations, consolidate repeated guidance.
2. **Moderate (20–40% savings):** Restructure for density, replace narrative with tables or structured lists, remove background context Claude does not need at runtime.
3. **Aggressive (40–60% savings):** Rewrite from scratch for maximum density, keeping only instructions and decision criteria. Risks losing nuance.

These percentages apply to Type A content. Type B content has significantly lower compressibility and higher risk. See the Compression Risk Assessment in `evaluation-rubric.md` for content-type-adjusted targets.

Always note what is at risk with each compression level. The user decides how aggressive to go.

---

## MCP Overhead Estimation

MCP overhead depends on the loading mode configured for each connector. Three patterns exist:

**Always-loaded** (full schemas every turn): The complete tool definition — name, description, parameters, types — is injected into the system prompt on every turn. Overhead: ~3K tokens for simple connectors (2–3 tools) to ~15K+ for complex ones (20+ tools).

**Deferred / load-as-needed** (catalog entry only): Tools are listed by name and brief description (~40–60 tokens each) in a lightweight catalog. Full schemas load on demand via `tool_search` when Claude determines a tool is needed. The deferred infrastructure adds a flat ~5–7K tokens regardless of connector count — an ~85% reduction versus always-loaded. This is the standard mode in claude.ai.

**Hybrid** (some tools always-loaded, rest deferred): Some connectors load primary tools with full schemas while deferring the rest. Overhead is the sum of always-loaded schemas plus the shared deferred catalog cost.

**Determining loading mode:** Cannot be determined from `ls -la` or the project UI. Two approaches: (1) examine the system prompt in a live conversation for full tool schemas vs. deferred catalog entries, or (2) ask the user whether their connectors are set to "load as needed."

**Dynamic overhead:** When `tool_search` activates a deferred tool mid-conversation, the full schema enters context for that turn and may persist. A session that activates 5+ different deferred tools sees MCP overhead grow by ~3–8K over baseline. Tool results also accumulate. Conversation runway estimates reflect baseline (static) overhead; actual runway depends on tool activation patterns.

**User asks whether disabling unused MCPs would help.** Two answers. With deferred loading: minimal benefit (~40–60 tokens per connector). Not worth the inconvenience. With always-loaded: meaningful benefit (~3K–15K each). Worth doing for connectors with no functional role.

---

## Budget-Constrained Projects

When a project is in Tier 3 (50K–66K tokens) and needs to stay in full-context:

- Every file consuming >25% of the ~66,500 budget (~16K+ tokens) should be evaluated for splitting or aggressive compression regardless of other scores.
- Skill migration is the highest-leverage move: relocating a 10K-token behavioral file to a Skill saves 10K tokens AND improves content fidelity (Skills load completely when triggered vs. partial retrieval).
- When knowledge file optimization is exhausted and the project is still Tier 3: evaluate whether remaining content could move to Memory (orientation-level facts), CI (behavioral rules), or session-specific uploads (per-conversation reference material).

---

## Sequencing Compression Rounds

Execute compression in rounds, ordered by content type:

1. **Phase 1 — Type A targets.** Compress all files identified as predominantly Type A (>70% prose/narrative) in the optimization plan. Execute one file per round. Checkpoint after every round.
2. **Checkpoint boundary.** After all Type A targets are complete, run a full Diminishing Returns Checkpoint before proceeding. This is the mandatory assessment point — do not cross from Type A to Type B targets without it.
3. **Phase 2 — Type B targets (if proceeding).** Only if the checkpoint recommends continuing. Apply conservative compression targets only to the Type A portions within mixed files. Do not compress Type B content.

Never interleave Type A and Type B targets. Front-loading Type A work maximizes savings before hitting the quality floor.

---

## Diminishing Returns Checkpoint

Run this assessment after every compression round. It is mandatory — do not skip it even when the next target appears straightforward.

**Five-point evaluation:**

1. **Progress:** How many tokens saved so far? What percentage of the gap has been closed?
2. **Remaining gap:** How many tokens remain to reach the target?
3. **Content type of next targets:** Predominantly Type A, Type B, or mixed? If Type B, what specific precision content is at risk?
4. **Quality cost assessment:** What specific content, data structures, or specifications would be at risk? Is the quality cost proportionate to the savings?
5. **Alternative path:** Would accepting RAG mode and optimizing retrieval quality produce a better outcome than continuing?

**Checkpoint output format:**
```
## Compression Checkpoint — Round [N]

Cumulative savings: ~[X]K tokens ([Y]% of gap closed)
Remaining gap: ~[Z]K tokens to ~66.5K threshold
Next targets: [file names] — [Type A / Type B / mixed]

Quality cost of continuing: [specific risks]
Recommendation: [CONTINUE / STOP / REASSESS]
Rationale: [why]
```

**Stopping criteria — recommend STOP when:**
- Remaining targets are predominantly Type B (>70% precision reference)
- Projected savings per file have dropped below ~750 tokens
- Quality cost of next compression would degrade a core project function
- Cumulative savings have closed >80% of gap and remaining gap is <3K tokens

**Continuing criteria — recommend CONTINUE when:**
- Remaining targets are predominantly Type A with >1K tokens of projected savings each
- Quality cost assessment shows low-risk content (redundant examples, verbose explanations)
- Gap is large enough that stopping would leave the project well into retrieval mode

---

## RAG-Acceptance Decision Point

When the Diminishing Returns Checkpoint recommends STOP or REASSESS, present the RAG-Acceptance Decision:

```
## RAG-Acceptance Decision

Current state: ~[X]K tokens (down from ~[Y]K). [Z]K remaining to threshold.
Compression completed: [N] rounds, [M]K tokens saved.
Remaining targets: [files] — predominantly Type B.

**Option A — Continue compressing:**
- Target: [next file]
- Projected savings: ~[S]K tokens
- Quality risk: [specific content at risk]
- Likelihood of reaching threshold: [assessment]

**Option B — Accept RAG mode and optimize retrieval quality:**
- Current retrieval quality issues: [from RAG Quality Checklist or quick assessment]
- Available improvements: [behavioral separation, routing guidance, chunk coherence]
- Projected retrieval quality after optimization: [assessment]

**Recommendation:** [Option A or B with rationale]
```

**RAG acceptance is not a failure state.** Reaching this decision point means the high-value compressions have been completed. The remaining gap exists because the project contains precision reference content that earns its token cost. Accepting retrieval mode and optimizing for retrieval quality is the right engineering decision when the alternative is degrading precision content.

**Post-acceptance guidance:** If the user accepts RAG mode, shift focus to the RAG Quality Checklist in `evaluation-rubric.md`. The compressions already completed may have improved retrieval quality (smaller, more focused files produce better chunks). Build on that foundation with behavioral separation, routing accuracy, and chunk coherence improvements.
