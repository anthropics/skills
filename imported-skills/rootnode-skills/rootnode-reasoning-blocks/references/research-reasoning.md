# Research / Synthesis Reasoning Approaches

Three approaches for tasks that require processing information sources into coherent analysis. Each addresses a different research orientation: deep evidence integration, broad domain mapping, or structured comparison against a target state.

---

## Evidence Synthesis

**Use when:** You have multiple sources of information and need to produce a coherent, evidence-grounded analysis that goes beyond summarizing each source individually.

```xml
<reasoning>
Approach this synthesis as follows:
1. Identify the key themes, patterns, or findings that emerge across the available information. Organize by theme, not by source.
2. Note where sources agree and where they conflict. Conflicts are often the most informative — they may indicate nuance, changing conditions, or differences in methodology.
3. Assess the quality and reliability of each source. Not all evidence is equal — consider methodology, recency, potential bias, and whether the source is primary or secondary.
4. Synthesize a coherent picture that integrates the strongest evidence. Clearly distinguish between what is well-established, what is likely, and what is speculative.
5. Identify the most important gaps — what do we not know that would matter most for the decision at hand?
</reasoning>
```

### Usage Guidance

Use for literature reviews, research summaries, competitive intelligence synthesis, due diligence research, policy analysis, and any task where multiple information sources need to become a single coherent analysis. The key differentiator is organizing by theme (not by source) and discriminating by evidence quality.

### Failure Modes

- **Equal-weight treatment:** Claude may give equal weight to all sources rather than discriminating by quality. If the sources vary significantly in reliability, add specific guidance: "Prioritize [primary research / peer-reviewed sources / first-party data] over [secondary analysis / opinion / anecdotal reports]."
- **Source-by-source summarization:** Despite the theme-based instruction, Claude may fall back to summarizing each source in sequence. If the output reads as "Source A says... Source B says..." rather than integrated analysis, reinforce: "Organize by finding, not by source. Each section should draw from multiple sources."

### When to Modify

For synthesis with a specific decision context, add a final step: "State the implications of this synthesis for [the specific decision]." For synthesis of quantitative data specifically, add guidance on handling conflicting numbers: "When sources report different figures, note the range and assess which methodology is most reliable."

---

## Landscape Scan

**Use when:** You need a broad overview of a domain — what exists, who the players are, what the trends are — rather than a deep dive into a specific question. Distinct from evidence synthesis because the goal is breadth and orientation, not depth and conclusion.

```xml
<reasoning>
Approach this landscape scan as follows:
1. Define the boundaries of the landscape. What is in scope and what is adjacent-but-out-of-scope? Without boundaries, landscape scans expand indefinitely.
2. Map the major categories or segments within the landscape. What are the natural groupings that help organize a complex space?
3. For each segment, identify: the key players or approaches, the current state of maturity, and the direction of movement (growing, stable, declining, or consolidating).
4. Identify the cross-cutting trends that affect multiple segments — these are often more important than developments within any single segment.
5. Highlight the 2-3 most significant developments or emerging patterns that the audience should pay attention to. Not everything in the landscape is equally important.
</reasoning>
```

### Usage Guidance

Use for market landscape overviews, technology surveys, competitive landscape mapping, ecosystem analysis, and any task where the goal is orientation rather than deep analysis. The approach produces a structured map with prioritized highlights rather than an exhaustive catalog.

### Failure Modes

- **Flat, unprioritized output:** Claude may produce a comprehensive but undifferentiated landscape scan where everything gets equal treatment. Step 5 pushes for prioritization, but if the output still lacks a point of view, add: "After mapping the landscape, identify the 2-3 findings that are most significant for [our specific situation/decision]. Not everything you map is equally important — tell me what matters most."
- **Indefinite expansion:** Without clear boundaries, Claude may keep adding adjacent areas. Step 1 mitigates this, but reinforce with specific scope constraints if the output is too broad.

### When to Modify

For landscapes that require competitive positioning analysis (not just mapping), add Market & Competitive Strategy steps from `strategic-reasoning.md` after the mapping is complete. For landscapes with a specific decision context, add a final step: "Given this landscape, what are the implications for [our specific situation]?"

---

## Gap Analysis

**Use when:** The task involves comparing a current state against a desired state and identifying what's missing. Distinct from general analysis because the framing is explicitly comparative — what exists vs. what should exist.

```xml
<reasoning>
Approach this gap analysis as follows:
1. Define the desired state precisely. What does "good" look like in concrete, measurable terms? Vague target states produce vague gap analyses.
2. Assess the current state with equal precision. Use the same dimensions and metrics as the desired state to make comparison direct.
3. Identify the gaps — where does current state fall short of desired state? Size each gap: is it a minor shortfall or a fundamental absence?
4. Prioritize the gaps by impact: which gaps, if closed, would produce the most significant improvement? Not all gaps are equally important.
5. For each priority gap, identify the most likely root cause of the gap and what it would take to close it (effort, time, resources, prerequisites).
6. Distinguish between gaps that can be closed incrementally and gaps that require a step change. This affects the implementation approach.
</reasoning>
```

### Usage Guidance

Use for maturity assessments, capability gap analysis, compliance gap analysis, skills gap analysis, process improvement identification, and any task where the fundamental question is "where do we fall short and what should we do about it?" The approach forces precision on both the current and target states before identifying gaps.

### Failure Modes

- **Irrelevant gaps:** Claude may identify gaps that are real but irrelevant to the current situation's priorities. Add context about strategic priorities so the gap analysis stays focused on what matters.
- **Vague target states:** If the desired state isn't well-defined in the prompt, Claude may invent one that sounds reasonable but doesn't match the actual goal. When using this approach, always provide a clear definition of the target state or ask Claude to define it explicitly before proceeding to gap identification.

### When to Modify

For gap analyses that lead to resource allocation decisions, combine step 5 with Resource Allocation from `strategic-reasoning.md` to ensure the gap-closing plan accounts for resource constraints. For technical gaps specifically, add: "For each technical gap, distinguish between capability gaps (we don't know how), capacity gaps (we don't have enough resources), and architectural gaps (the current system can't support this)."
