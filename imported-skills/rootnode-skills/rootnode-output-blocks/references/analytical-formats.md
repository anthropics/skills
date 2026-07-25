# Analytical Formats

Output format specifications for deliverables involving evidence synthesis, structured comparison, and market assessment. Each format includes the complete XML specification, per-section guidance, and watch-for notes on Claude's common failure modes.

---

## Table of Contents

- [Research Summary](#research-summary)
- [Decision Matrix](#decision-matrix)
- [Competitive Analysis](#competitive-analysis)

---

## Research Summary

**Use when:** You need to present findings from research, analysis, or investigation. Organized by insight, not by source.

**Audience:** Decision-makers or colleagues who need to understand what the evidence says. Not the researchers themselves.

**Length:** 800-1200 words.

### Format Specification

```xml
<output_format>
Structure as a research summary:

Key Findings: (3-5 numbered findings, each 2-3 sentences) The most important discoveries or conclusions, in order of significance. Each finding should be a complete, actionable insight — not a topic label.

Evidence Assessment: (1 paragraph) How strong is the underlying evidence? Where is it robust and where is it thin? Are there notable methodological limitations?

Detailed Analysis: (organized by theme, 2-3 paragraphs per theme) The supporting analysis, organized by topic or theme — never by source. Each theme section should synthesize across sources to build understanding.

Gaps and Limitations: (1 paragraph) What the available information does not tell us. What additional data or research would strengthen the conclusions?

Implications: (1-2 paragraphs) What these findings mean for the decision or situation at hand. Connect the research to action.

Total length: 800-1200 words.
</output_format>
```

### Watch For

**Analysis organized by source instead of theme.** Claude may organize the Detailed Analysis by source (summarizing Source A, then Source B) rather than by theme. If this happens, add this countermeasure: *"Organize all analysis by theme or question, never by source. Each section should draw from multiple sources to build a complete picture of that theme."*

**Vague findings.** Key Findings should be specific and actionable. "Customer preferences are changing" is a topic label, not a finding. "Customers under 35 prefer X over Y by a 2:1 ratio" is a finding. If findings are too vague, add: *"Each Key Finding must be a specific, falsifiable claim — not a topic label or general observation."*

**Missing Evidence Assessment.** Claude may skip straight from findings to analysis without evaluating the quality of the underlying evidence. This section is what distinguishes a rigorous summary from a credulous one.

---

## Decision Matrix

**Use when:** You need a structured comparison of options against defined criteria. The output should make the tradeoffs visible and support a clear recommendation.

**Audience:** Decision-makers who need to see how options compare and understand the tradeoffs.

**Length:** Variable — driven by the number of options and criteria. Typically 600-1000 words plus the comparison table.

### Format Specification

```xml
<output_format>
Structure as a decision matrix:

Decision Context: (1 paragraph) What decision is being made, why it matters, and what constraints apply.

Evaluation Criteria: (brief descriptions) List each criterion with a one-sentence definition and its relative weight (critical / important / nice-to-have). 4-7 criteria is typical.

Comparison Matrix: Present as a table with options as rows and criteria as columns. Use a consistent rating scale (e.g., Strong / Adequate / Weak, or 1-5) with brief justifications in each cell — not just scores.

Analysis: (2-3 paragraphs) Interpret the matrix. Where do options clearly separate? Where are they essentially equivalent? What single factor most differentiates the top options?

Recommendation: (1 paragraph) A clear recommendation with the primary reasoning. If two options are very close, state what additional information would break the tie.

Write the matrix for a decision-maker who will scan the table first and read the analysis only if they need more detail.
</output_format>
```

### Watch For

**Undifferentiated scoring.** Claude may create a matrix where every option scores "Adequate" on most criteria, making the comparison useless. Push for differentiation with this countermeasure: *"If two options are essentially equivalent on a criterion, mark them both as equivalent and focus your analysis on the criteria where they genuinely differ."*

**Criteria chosen to favor a particular option.** The criteria should reflect what actually matters for the decision, not be reverse-engineered from a preferred conclusion. Scrutinize the criteria list for balance.

**Scores without justification.** The Comparison Matrix should include brief justifications in each cell, not just ratings. A score of "Weak" without explanation gives the decision-maker no basis for agreement or disagreement.

---

## Competitive Analysis

**Use when:** You need to assess the competitive landscape around a product, company, or market position.

**Audience:** Strategy teams, product leaders, executives making competitive positioning decisions.

**Length:** 800-1200 words.

### Format Specification

```xml
<output_format>
Structure as a competitive analysis:

Market Overview: (1 paragraph) The market being analyzed, its size or trajectory, and why competitive positioning matters now.

Competitive Landscape: (1 paragraph per competitor, covering 3-5 key competitors) For each: their market position, key strengths, notable weaknesses, and recent strategic moves. Focus on what they do that matters to your competitive position — not a comprehensive company profile.

Comparative Position: A table or structured comparison showing how the subject compares to competitors on the 3-5 most important competitive dimensions.

Competitive Advantages: (1-2 paragraphs) Where the subject has a durable edge. Be specific about what makes the advantage defensible, not just what's currently good.

Competitive Vulnerabilities: (1-2 paragraphs) Where the subject is at risk. Be equally specific and direct.

Strategic Implications: (1 paragraph) What this competitive picture means for strategy. What should the subject do, avoid, or watch for?

Total length: 800-1200 words. Be direct about weaknesses — a competitive analysis that only sees strengths is useless.
</output_format>
```

### Watch For

**Reluctance to state vulnerabilities.** Claude may be reluctant to state clear competitive vulnerabilities, especially if the context implies the user is the subject being analyzed. Add this countermeasure: *"Be equally direct about vulnerabilities as you are about advantages. A competitive analysis that minimizes weaknesses is dangerous — it prevents the team from addressing real threats."*

**Company profiles instead of competitive intelligence.** The Competitive Landscape section should focus on what each competitor does that matters to the user's competitive position — not a general overview of each company. If the section reads like Wikipedia summaries, add: *"For each competitor, focus exclusively on their strengths, weaknesses, and moves that directly affect our competitive position."*

**Missing Comparative Position table.** Claude may skip the structured comparison and write everything in prose. The table is critical — it is the section decision-makers scan first. If missing, explicitly request: *"Include a comparison table with competitors as rows and competitive dimensions as columns."*
