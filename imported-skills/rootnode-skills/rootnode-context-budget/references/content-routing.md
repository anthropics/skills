# Content Routing Framework

Determines the optimal storage and access pattern for knowledge file content. The Content-Type Classification (Type A/B in `compression-execution.md`) determines *how aggressively to compress* content staying in knowledge files. This framework determines *where content should live* — whether it should stay in knowledge files at all.

## Table of Contents

1. [Category 1 — Behavioral / Instructional Content](#category-1--behavioral--instructional-content)
2. [Category 2 — Strategic / Analytical Content](#category-2--strategic--analytical-content)
3. [Category 3 — Structured Reference Data WITH MCP Access](#category-3--structured-reference-data-with-mcp-access)
4. [Category 4 — Structured Reference Data WITHOUT MCP Access](#category-4--structured-reference-data-without-mcp-access)
5. [Integration with Type A/B Classification](#integration-with-type-ab-classification)
6. [Content Routing Output Format](#content-routing-output-format)

---

## Category 1 — Behavioral / Instructional Content

Content that shapes Claude's behavior: rules, constraints, frameworks, response patterns, workflow instructions, output formatting directives.

**Optimal location:** Always-present layers — Custom Instructions, Memory, or Tier 1 knowledge file with explicit CI routing.

**Why:** Behavioral content must passively shape every response. In RAG mode, behavioral rules embedded in knowledge files load only when retrieval happens to match them to a query — rules that should always apply become intermittent. This is the highest-impact retrieval quality issue.

**Action:** Relocate to CI or Memory. If it must stay in a knowledge file, ensure Tier 1 classification and explicit CI routing.

**Never:** Place in an external store. Behavioral content behind a tool call means Claude has to decide to look up its own instructions before following them.

---

## Category 2 — Strategic / Analytical Content

Content that provides reasoning context: positioning analysis, opportunity matrices, design rationale, strategic frameworks, cross-entity pattern analysis, decision logic.

**Optimal location:** Knowledge file (full-context preferred, RAG-tolerant if well-structured).

**Why:** Strategic content benefits from passive awareness — it subtly shapes recommendations without requiring an explicit lookup. When a user asks "how should we price this job," competitive positioning should inform the answer without Claude deciding to look up competitive intelligence first.

**RAG tolerance:** Moderate to high, IF sections are self-contained. Strategic content chunks reasonably well because each section (e.g., an opportunity matrix) is a complete analytical unit. The RAG Quality Checklist techniques (behavioral separation, chunk coherence, routing accuracy) apply here.

**Action:** Compress Type A portions. Optimize for chunk coherence if RAG is accepted. Keep in knowledge files.

**Not a data split candidate:** This content is not structured, not queryable by key, and not meaningfully storable in rows and columns. Its value is contextual and analytical.

---

## Category 3 — Structured Reference Data WITH MCP Access

Content with a natural key-value or tabular structure (competitor profiles, pricing tables, keyword volumes with search metrics, zip code tiers with demographics, inventory records, configuration tables) where a queryable external store is available via MCP.

**Optimal location:** External store (Airtable, Notion, PostgreSQL, or custom database) queryable via MCP.

### Why This Is Strictly Better Than RAG for Structured Data

- **Deterministic retrieval.** A database query returns exactly what was asked for, every time. RAG retrieval of the same structured data is non-deterministic — the same question on two different turns may retrieve different chunks.
- **Structural integrity.** RAG chunks tables destructively. It might return rows 1–15 but not 16–34, or the pricing column but not the service column that gives context. A database query returns complete records with all fields.
- **Field-level operations.** "Show me all HIGH threat competitors sorted by review count" is a trivial database query and an impossible RAG retrieval. The retrieval system does not understand field-level filters, sorts, or aggregations.
- **Permanent budget relief.** Every token moved to an external store is headroom that never needs to be managed again. Compression saves tokens once; the data split saves them permanently and the data can grow without affecting the knowledge file budget.
- **Living data.** Knowledge file data is a snapshot. External store data stays current because updating a single record is low-friction. The data becomes an operational asset, not just a document.

### Data Split Pattern

**Action:** Migrate structured data to the external store. Retain strategic and analytical content derived from that data in the knowledge file (e.g., keep the opportunity matrix, migrate the individual competitor records). Add a routing note to the knowledge file indicating where the structured data lives and how to query it.

### MCP Infrastructure Assessment

When recommending a data split, assess the available MCP infrastructure:

**Pre-built MCP connector (Anthropic's Airtable, Notion, etc.):** Available immediately but creates dependency on infrastructure the user does not control. Connector reliability, query capabilities, and long-term availability are outside the user's influence. Suitable for proof-of-concept or when no custom infrastructure exists.

**Custom MCP server with backend adapter pattern:** The user controls the tool interface. If the backend store changes, the adapter swaps but Claude's tool calls remain identical. Higher initial investment but provides interface stability, reliability controls (retry logic, caching, structured error responses), and compounds across all data splits. Recommended when the user has or is building custom MCP infrastructure.

**The skill should ask:** "Do you have a custom MCP server, or would this use a pre-built connector?" The recommendation and risk assessment differ based on the answer.

### Fallback Pattern

The knowledge file retains all strategic intelligence derived from the structured data. If MCP is unreachable, Claude still has the analytical layer (opportunity matrices, response frameworks, strategic patterns). Only specific record lookups degrade. Claude should inform the user that the data store is unreachable and either use web search as a degraded lookup or ask the user to check directly.

### Retrieval Quality Tradeoff

Full-context mode provides passive awareness of all details — data subtly shapes every response without an explicit lookup. MCP query requires active lookup — Claude must decide to query, formulate the right request, and integrate the result.

For most conversations, the pattern-level awareness preserved in the knowledge file's strategic sections is what drives good recommendations. Specific detail lookups (a competitor's exact pricing, a zip code's demographic breakdown) are the ~10% case where the active query matters.

**State this tradeoff explicitly** so the user can make an informed decision. The data split is not "moving data out" — it is restructuring access patterns to match how each content type is actually used.

---

## Category 4 — Structured Reference Data WITHOUT MCP Access

Same data types as Category 3, but no external store infrastructure is available. No MCP connector for a suitable database. No custom MCP server.

**Optimal location:** Knowledge file with RAG optimization (fallback path).

**Why this is the fallback, not the preferred path:** RAG retrieval of structured data has the limitations described in Category 3 (non-deterministic, chunks destructively, cannot filter/sort/aggregate). But when no external store is accessible, the knowledge file is the only option.

**Action:** Apply RAG optimization techniques: chunk coherence (keep tables intact within sections), routing accuracy (CI maps task types to the file containing the data), pool cleanliness (no stale or duplicate structured data).

### Structural Opportunity Flag

When the skill detects Category 4 content, it should note the structural limitation in the optimization plan:

> "This file contains structured reference data ([description]) that would benefit from a queryable external store via MCP. No suitable MCP connector is currently available. RAG optimization applied as fallback. This content type is non-deterministically retrieved and cannot support field-level queries in the current architecture. Consider connecting a database MCP (Airtable, Notion) or implementing a custom MCP server to unlock the data split pattern for this content — this would provide deterministic retrieval, permanent token budget relief, and a live-updateable data asset."

This flag transforms the skill from a cleanup tool into an architectural advisor. It identifies the structural opportunity even when it cannot execute it today, and gives the user a clear path to resolve it when ready.

---

## Integration with Type A/B Classification

Type A/B and Category 1–4 operate at different layers and are complementary:

- **Type A** (prose, narrative) maps to **Categories 1 and 2** based on whether the content is behavioral or analytical.
- **Type B** (precision reference) maps to **Categories 3 or 4** based on whether the content is structured/tabular (benefiting from a queryable store) or precision-but-not-tabular (configuration syntax, code snippets, legal citations — these stay in knowledge files regardless).

Apply both classifications: Type A/B to determine compression depth for content staying in knowledge files, and Category 1–4 to determine whether content should stay in knowledge files at all.

---

## Content Routing Output Format

For each file where content classification identifies mixed categories, include in the optimization plan:

```
**Content Routing: [file name]**
— Category 1 (behavioral): [X]% → Relocate to CI/Memory
— Category 2 (strategic): [Y]% → Retain in KF (compress Type A portions)
— Category 3 (structured, MCP available): [Z]% → Migrate to [store] via [MCP type]
— Category 4 (structured, no MCP): [W]% → RAG-optimize in KF (flag opportunity)
— Net KF reduction: ~[S]K tokens
— Compound benefit: [queryable, updateable, feeds other systems, permanent budget relief]
```

For files that are entirely one category, the routing is simpler — just the action and rationale. The detailed breakdown is most valuable for mixed-content files where different portions route to different storage layers.
