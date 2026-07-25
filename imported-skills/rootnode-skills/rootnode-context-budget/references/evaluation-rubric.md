# Evaluation Rubric

Detailed scoring criteria for the Full Budget Audit (Mode 2). Contains six evaluation dimensions, the tier decision matrix, compression risk assessment, and the RAG Quality Checklist.

## Table of Contents

1. [Six Evaluation Dimensions](#six-evaluation-dimensions)
2. [Tier Decision Matrix](#tier-decision-matrix)
3. [Compression Risk Assessment](#compression-risk-assessment)
4. [RAG Quality Checklist](#rag-quality-checklist)
5. [RAG Quality Optimization Principles](#rag-quality-optimization-principles)

---

## Six Evaluation Dimensions

Score each knowledge file on these six dimensions using a 1–5 scale. Ground every score in specific evidence — quote file names, section headers, or content patterns. Never assign scores based on assumptions about what a file "probably" contains.

### Dimension 1: Cross-Reference Density

*How many other files or Custom Instructions sections reference this file?*

| Score | Criteria |
|:-----:|----------|
| **1** | No references from any other file or CI. The file is an island. |
| **2** | Referenced by 1 other file or a single CI routing instruction. Minimal integration. |
| **3** | Referenced by 2–3 other files or multiple CI routing instructions. Moderate integration. |
| **4** | Referenced by 4+ files or serves as a routing hub in CI. High integration — removing this file would require updating multiple other files. |
| **5** | Central hub file. Referenced by most other files and CI. The project's architecture depends on this file's presence. |

**Evidence examples:** "CI routes to this file for 3 task types." "Files X, Y, and Z all contain pointers to this file." "No other file mentions this file by name."

### Dimension 2: Behavioral vs. Referential

*Does this file contain rules/instructions that shape Claude's behavior, or reference information that Claude consults?*

| Score | Criteria |
|:-----:|----------|
| **1** | Pure reference — data tables, historical records, raw content. Contains no instructions, directives, or behavioral rules. |
| **2** | Primarily reference with a few embedded instructions (e.g., "when presenting this data, use tables"). |
| **3** | Mixed — substantial behavioral rules and substantial reference content coexist in the same file. This is often a structural smell (Monolith anti-pattern). |
| **4** | Primarily behavioral — rules, constraints, workflow instructions with some supporting examples or reference data. |
| **5** | Pure behavioral — the file is entirely instructions, constraints, and directives. No reference data. |

**Scoring note:** Files scoring 4–5 are high-priority for always-present context (CI, Memory, or Tier 1 knowledge file). In retrieval mode, behavioral files are unreliable because they only load when matched to a query — behavioral rules should be in layers that are always present.

### Dimension 3: Query Frequency

*How often is this file consulted across typical conversations?*

| Score | Criteria |
|:-----:|----------|
| **1** | Rarely or never consulted. Content is outdated, or the file addresses edge cases that arise less than 5% of conversations. |
| **2** | Consulted in a narrow set of conversations — maybe 10–20% of typical sessions. Specialized reference for uncommon tasks. |
| **3** | Consulted in a moderate share of conversations — roughly 30–50%. Relevant to one of several common task types. |
| **4** | Consulted in most conversations — 60–80%. Contains content relevant to the project's primary workflows. |
| **5** | Consulted in nearly every conversation — 90%+. Core reference that is relevant regardless of the specific task. |

**Evidence examples:** "This file contains onboarding procedures — relevant only when setting up new users (~10% of conversations)." "This file defines the project's output format standards — consulted on every deliverable."

### Dimension 4: Degradation Severity

*What happens if this file is not loaded into context?*

| Score | Criteria |
|:-----:|----------|
| **1** | No noticeable degradation. Output quality and accuracy are unaffected. |
| **2** | Minor quality reduction. Claude produces slightly less specialized output but still meets the user's needs. |
| **3** | Moderate degradation. Claude misses domain-specific nuances, uses generic approaches where specialized ones exist, or produces output that requires manual correction on specific points. |
| **4** | Significant degradation. Claude cannot perform one or more core project functions correctly. Output requires substantial revision or the user must manually supply the missing context. |
| **5** | Critical failure. The project's primary purpose cannot be fulfilled without this file. Claude produces incorrect, unsafe, or fundamentally misaligned output. |

**Evidence examples:** "Without this file, Claude uses generic formatting instead of the project's branded template — moderate degradation." "This file contains the compliance rules — without it, output could violate regulatory requirements — critical failure."

### Dimension 5: Token Cost

*How large is this file relative to the total budget?*

| Score | Criteria |
|:-----:|----------|
| **1** | Under 2% of total knowledge file tokens. Negligible budget impact. |
| **2** | 2–5% of total. Small but measurable. |
| **3** | 5–10% of total. Meaningful budget consumer. Compression worth evaluating. |
| **4** | 10–20% of total. Major budget consumer. Must justify its size against the value it provides. |
| **5** | Over 20% of total. Dominant file. Almost certainly a compression or restructuring candidate regardless of other scores. |

**Scoring note:** A file scoring 5 on Token Cost but also 5 on Degradation Severity is a compression candidate, not a removal candidate. The goal is to reduce its token cost while preserving the content that drives its high degradation score.

### Dimension 6: Cross-File Dependency Density

*How much does this file depend on content in other files to be useful?*

| Score | Criteria |
|:-----:|----------|
| **1** | Fully self-contained. Makes no reference to other knowledge files. Can be understood and used in complete isolation. |
| **2** | Minimal dependency. References 1 other file for supplementary context that is not essential. |
| **3** | Moderate dependency. References 2–3 other files. Some content assumes the reader has context from those files. |
| **4** | High dependency. References 4+ files or contains instructions that only make sense if another specific file is present. Fragile if any dependency is absent. |
| **5** | Entangled. Tightly coupled with multiple other files. Content is distributed across files in a way that requires all to be present for any to be useful. Strong consolidation signal. |

**Scoring note:** High scores on Dimension 6 create fragility in retrieval mode — if the retrieval system loads this file but not its dependencies, Claude gets partial context that may be worse than no context. Files scoring 4–5 are either consolidation candidates (merge with dependencies) or Tier 1 candidates (ensure they always load together).

---

## Tier Decision Matrix

After scoring all six dimensions, apply this matrix to assign each file to a placement tier.

### Tier 1 — Must Keep in Context

Assign Tier 1 when ANY of the following are true:
- Degradation Severity ≥ 4 AND Query Frequency ≥ 3
- Behavioral score ≥ 4 (behavioral content must be always-present, especially in retrieval mode)
- Cross-Reference Density = 5 (hub file — removing it cascades)
- The file is the sole source of content critical to the project's primary purpose

### Tier 3 — Archive or Remove

Assign Tier 3 when ANY of the following are true:
- Query Frequency ≤ 2 AND Degradation Severity ≤ 2
- Token Cost ≥ 4 AND Degradation Severity ≤ 2 (large file, low impact if absent)
- Content is demonstrably stale (references outdated versions, deprecated processes, or superseded decisions)
- Content is duplicated in another file or in Custom Instructions

### Tier 2 — Optimize or Relocate

Assign Tier 2 when the file does not meet Tier 1 or Tier 3 criteria. These files have value but their current form, size, or placement may not be optimal.

### Tiebreaker Logic

When dimension scores create conflicting signals:

**High Degradation + Low Frequency:** The file is critical when needed but rarely needed. Consider: Can CI routing ensure it loads when relevant? If yes, Tier 2 with a routing optimization note. If no (retrieval mode makes selective loading unreliable), Tier 1.

**High Token Cost + High Degradation:** Tier 1 with a compression recommendation. The content must stay, but it should cost fewer tokens. Before recommending compression depth, check the file's content-type distribution: if the high Degradation Severity score is driven by Type B precision content (schemas, configurations, test payloads, data dictionaries), compression targets should be conservative or zero — the precision content IS the reason the file is high-degradation. See the Compression Risk Assessment below for content-type-adjusted targets. Apply compression guidance from SKILL.md.

**High Cross-File Dependency + Moderate Other Scores:** If the dependent files are Tier 1, this file is likely Tier 1 (it completes a critical cluster). If the dependent files are Tier 2/3, this file is a consolidation candidate — merge with its dependencies or restructure to reduce coupling.

**High Behavioral Score + Low Query Frequency:** Behavioral content should be in always-present layers regardless of query frequency. Recommend relocation to Custom Instructions or Memory rather than keeping as a knowledge file. Tier 2 with relocation action.

---

## Compression Risk Assessment

This table bridges file-level scoring to compression execution. After scoring a file on six dimensions and classifying its content type (see Content-Type Classification in SKILL.md), use this table to determine the appropriate compression approach. This prevents the scoring system from recommending aggressive compression that the execution guidance would then have to override — the override happens at the scoring stage instead.

| Content-Type Distribution | Compression Approach | Max Recommended Reduction | Notes |
|---|---|---|---|
| >70% Type A (prose/narrative) | Aggressive compression safe | 50–60% | Standard compression tiers apply. Low quality risk. |
| 50–70% Type A / 30–50% Type B | Moderate compression, targeted | 30–40% overall | Compress Type A portions only. Isolate and preserve Type B sections. State which sections are compression-resistant and why. |
| 30–50% Type A / 50–70% Type B | Conservative compression only | 15–25% overall | Compress only clearly redundant Type A content (duplicate examples, verbose explanations). Leave Type B sections untouched. Flag the file for the Diminishing Returns Checkpoint. |
| >80% Type B (precision reference) | Do not compress | 0% | The file's token cost is the cost of the precision content it contains. Flag for RAG-acceptance evaluation if the file is a major budget consumer. Consider structural alternatives: splitting into smaller focused files for better retrieval chunking, relocating to a Skill (if the content is a standalone methodology), or accepting the token cost as justified. |

**Connection to Dimension 4 (Degradation Severity):** When a file scores high on both Token Cost (Dimension 5) and Degradation Severity (Dimension 4), the tiebreaker logic assigns Tier 1 with a compression recommendation. If the high Degradation Severity is driven by Type B content — meaning the file is critical precisely because it contains precision reference that Claude needs exactly as written — then compression is not the right optimization lever. The Compression Risk Assessment overrides the generic compression recommendation: a >80% Type B file scoring Token Cost = 5 and Degradation Severity = 5 stays as-is. Evaluate other optimization paths instead: archiving Tier 3 files elsewhere in the project, relocating behavioral content to CI/Memory, or accepting RAG mode.

**Mixed-content files:** For files with significant Type A and Type B content, recommend section-level compression rather than file-level. Identify the Type A sections by name and provide compression targets for those sections specifically. Explicitly state that the Type B sections (identify them by name) are compression-resistant and should be preserved as-is.

---

## RAG Quality Checklist

For projects in retrieval mode. Run this checklist during a Full Budget Audit (Step 7). Score each item pass/fail with specific evidence.

### Item 1: Behavioral Separation

**Check:** Are behavioral rules (instructions, constraints, directives) separated from reference content (data, examples, documentation)?

**Pass criteria:** Behavioral content is in Custom Instructions, Memory, or clearly separated knowledge files that are identified as behavioral in CI routing. Reference content is in separate files.

**Fail indicators:** Knowledge files mix behavioral rules with reference data. Behavioral content is embedded in the middle of reference documents. CI does not distinguish behavioral files from reference files in routing.

**Why it matters:** In retrieval mode, behavioral rules embedded in reference files load only when the retrieval system happens to match them to a query. Rules that should always apply become intermittent. This is the single highest-impact retrieval quality issue.

**Fix:** Extract behavioral content from knowledge files. Place in Custom Instructions (if structural/always-apply rules), Memory (if orientation-level facts and preferences), or a dedicated behavioral knowledge file explicitly routed in CI.

### Item 2: File Granularity

**Check:** Are knowledge files sized and scoped for effective retrieval chunking?

**Pass criteria:** Each file addresses a single coherent topic. Files are between ~2K and ~30K tokens. No file tries to cover multiple unrelated subjects.

**Fail indicators:** Files over ~40K tokens (retrieval chunks from these are often too broad). Files covering multiple unrelated topics (retrieval may surface irrelevant sections). Very small files under ~200 tokens (content may be too thin to produce useful retrieved chunks).

**Why it matters:** Retrieval quality depends on chunk relevance. Large multi-topic files produce chunks that partially match many queries but fully match none. Small single-fact files waste retrieval slots.

**Fix:** Split large multi-topic files by subject. Merge very small related files. Target one coherent subject per file at 2K–30K tokens.

### Item 3: Routing Accuracy

**Check:** Does CI provide clear routing guidance that helps the retrieval system (or Claude's own judgment) identify which file to consult for which tasks?

**Pass criteria:** CI includes routing instructions that map task types to specific knowledge files. Routing uses descriptive language matching the content of each file.

**Fail indicators:** CI lists files with inventory descriptions ("This project contains X.md, Y.md, Z.md") instead of routing guidance ("Consult X.md when the user asks about pricing or competitive positioning"). No routing instructions at all — Claude must guess which file is relevant.

**Why it matters:** In retrieval mode, the search query determines which chunks load. Poor routing guidance means Claude formulates vague searches that return low-relevance chunks.

**Fix:** Add explicit routing instructions to CI: for each knowledge file, specify the task types and query patterns that should trigger consultation.

### Item 4: Self-Contained Sections

**Check:** Are knowledge file sections understandable when retrieved in isolation (without surrounding context)?

**Pass criteria:** Each major section includes enough context to be useful standalone. Sections do not rely on earlier sections for critical definitions or context. Acronyms and domain terms are defined at point of use or in a brief header.

**Fail indicators:** Sections reference "the above" or "as mentioned earlier." Critical context is in a file header that may not be retrieved with a later section. Sections use undefined acronyms or jargon introduced elsewhere in the file.

**Why it matters:** Retrieval mode may load section 4 of a file without sections 1–3. If section 4 depends on context from section 1, the retrieved content is incomplete or misleading.

**Fix:** Add brief context headers to major sections. Define key terms at first use within each section. Replace "as mentioned above" references with inline context.

### Item 5: Chunk Coherence

**Check:** Does the file structure align with likely retrieval boundaries?

**Pass criteria:** Related content is grouped together. Information that must be used together (e.g., a rubric and its scoring criteria) is in the same section. Headers and structure create natural chunk boundaries.

**Fail indicators:** Related content is split across distant sections of the same file. Tables are separated from their explanatory context. Instructions and their examples are in different sections that may chunk separately.

**Why it matters:** Retrieval systems chunk by structural boundaries (headers, paragraphs). If a rubric's criteria are in one section and its scoring guidance in another, a query about scoring may retrieve only half the needed content.

**Fix:** Co-locate related content. Keep rubrics with their scoring criteria. Keep instructions with their examples. Use headers to create logical chunk boundaries.

### Item 6: Retrieval Pool Cleanliness

**Check:** Is the retrieval pool free of content that degrades search relevance?

**Pass criteria:** No stale, outdated, or superseded content in knowledge files. No duplicate content across files. No placeholder or template content that matches queries but provides no value.

**Fail indicators:** Files contain outdated versions alongside current versions. Multiple files contain similar content (retrieval returns duplicates, wasting slots). Template or boilerplate content matches queries but adds no useful information.

**Why it matters:** Every irrelevant chunk that retrieval returns displaces a relevant one. Stale and duplicate content pollutes the retrieval pool and reduces the quality of every search.

**Fix:** Remove outdated content. Deduplicate across files. Remove placeholder and template content that is not actively used.

### Item 7: Index File Pattern

**Check:** For projects where retrieval quality suffers because Claude cannot efficiently navigate the knowledge base — regardless of file count — is there an index or routing file that helps Claude navigate?

**Pass criteria:** A lightweight index file exists that maps topics to files without duplicating content. CI references the index file as a first-consult resource. The index is under ~2K tokens.

**Fail indicators:** No index file and CI provides no routing guidance. An "index" file that duplicates substantial content from other files (increasing retrieval noise). An index file that is itself large (defeating the purpose of a lightweight routing aid).

**Why it matters:** In retrieval-mode projects, Claude may not know which file to search for a given topic. A lightweight index file provides a routing map that improves first-query accuracy.

**Fix:** Create a concise index file mapping topics, task types, and key terms to specific knowledge files. Keep it under ~2K tokens. Reference it in CI as the first resource to consult for routing decisions.

---

## RAG Quality Optimization Principles

Five principles for optimizing retrieval quality, referenced when the feasibility assessment determines retrieval quality optimization is the right strategy.

### Principle 1: Behavioral Content Belongs in Always-Present Layers

Rules, constraints, and behavioral instructions must be in Custom Instructions, Memory, or dedicated always-loaded files — never embedded in reference files where retrieval makes their loading intermittent. This is the single highest-leverage optimization for retrieval-mode projects.

### Principle 2: One Topic Per File, Sized for Chunking

Each knowledge file should address a single coherent subject at 2K–30K tokens. This creates retrieval chunks that are relevant when matched and complete enough to be useful. Multi-topic files produce partial matches; micro-files waste retrieval slots.

### Principle 3: Self-Contained Sections Over Cross-References

Within each file, major sections should be understandable in isolation. Define terms at point of use. Include enough context that a retrieved section does not require surrounding sections. Cross-file references should add value when available but not be required for the section to be useful.

### Principle 4: Clean Retrieval Pool

Remove stale, duplicate, and placeholder content. Every chunk in the retrieval pool should be current, unique, and genuinely useful if retrieved. Irrelevant chunks displace relevant ones.

### Principle 5: Explicit Routing Guidance

Custom Instructions should map task types to knowledge files with descriptive routing language. In retrieval mode, Claude's search queries are influenced by the task framing — good routing guidance produces better searches. An index file provides an additional routing layer for large knowledge bases.
