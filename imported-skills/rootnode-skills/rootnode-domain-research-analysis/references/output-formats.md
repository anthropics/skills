# Output Structures for Research & Analysis

Complete output structure specifications for research and analysis prompts. Each structure includes the full XML code block to paste into your prompt, usage guidance, and failure mode warnings.

**Table of Contents:**
- [Policy Brief](#policy-brief)
- [Data Analysis Report](#data-analysis-report)
- [Literature Review](#literature-review)
- [Briefing Document](#briefing-document)

---

## Policy Brief

**Use when:** You need a short, evidence-based document that recommends a specific action or decision to a policymaker or organizational leader. The format specifically bridges research findings to a policy choice, maintaining explicit connection between evidence and recommendation.

**Distinct from:** Executive Brief (which presents analysis and recommendations broadly) — this format is grounded in evidence assessment. Distinct from Strategic Memo (which argues for a strategic direction) — this format is grounded in evidence assessment rather than strategic logic.

**Target length:** 600-900 words.

```xml
<output_format>
Structure as a policy brief:

Issue Statement: (2-3 sentences) What decision needs to be made, why it matters, and why it needs to be made now.

Recommendation: (1 paragraph) The recommended course of action, stated directly. The reader should know what you are proposing before reading the supporting evidence.

Evidence Base: (3-4 paragraphs) The research findings that support the recommendation. Organize by strength of evidence, not by source. For each major finding, note the quality of the underlying evidence (strong, moderate, or limited). Where findings conflict, present both sides and explain which the weight of evidence favors.

Implementation Considerations: (1-2 paragraphs) What is required to implement the recommendation — resources, timeline, stakeholder buy-in, potential obstacles. This is where organizational reality meets the evidence-based recommendation.

Risks and Limitations: (1 paragraph) What could go wrong, what the evidence does not address, and what assumptions the recommendation rests on. Include at least one scenario where the recommendation fails and what the fallback would be.

Alternative Approaches: (1 paragraph) Other options that were considered and why they are not recommended. Brief but fair — the decision-maker should see that alternatives were genuinely evaluated.

Total length: 600-900 words. Policy briefs must be concise enough that the decision-maker will read the entire document. If the evidence requires more extensive treatment, reference supporting documents rather than expanding the brief.
</output_format>
```

**Watch for:** Claude may produce briefs where the recommendation and the evidence are disconnected — the evidence section reviews findings, but the recommendation does not clearly follow from the specific findings presented. If the logical chain from evidence to recommendation is unclear, add: *"Each element of the recommendation must trace to a specific finding in the evidence section. If a recommendation cannot be supported by the presented evidence, it should be flagged as a judgment call rather than an evidence-based conclusion."*

**Also watch for:** Claude hedging the recommendation so heavily that the decision-maker receives analysis rather than a recommendation. If the brief reads as "here are the considerations" rather than "here is what you should do," add: *"State a clear, specific recommendation. Uncertainty about details does not prevent you from recommending a direction."*

---

## Data Analysis Report

**Use when:** You need a structured presentation of quantitative findings — what was analyzed, how, what the results show, and what they mean. Use this when the audience needs to evaluate the analytical rigor, not just the conclusions.

**Distinct from:** Research Summary (which synthesizes across multiple sources) — this presents the findings of a specific analytical exercise. Distinct from Executive Brief (which leads with the recommendation) — this leads with methodology and findings, with interpretation following.

**Target length:** 700-1200 words, proportional to analytical complexity.

```xml
<output_format>
Structure as a data analysis report:

Executive Summary: (2-3 sentences) The key finding and its implication. A reader who reads only this should know the bottom line.

Analysis Objective: (1 paragraph) What question this analysis answers, why it matters, and what data was used. Include the time period, data source, and any relevant scope limitations.

Methodology: (1-2 paragraphs) How the analysis was conducted. What metrics were computed, what comparisons were made, what groupings or filters were applied. Sufficient detail that another analyst could replicate the approach. Proportional to the complexity of the analysis — a simple trend analysis needs one sentence on method, not a paragraph.

Key Findings: (3-5 findings, each 2-4 sentences) The most important results, presented in order of significance. Each finding states what was observed, the magnitude of the effect, and the confidence level. Findings are statements of fact from the data, not interpretations.

Interpretation and Implications: (2-3 paragraphs) What the findings mean for the original question. Connect the data to decisions or actions. This is where analytical judgment enters — clearly distinguished from the factual findings above.

Limitations: (1 paragraph) What the analysis cannot tell us. Limitations of the data source, methodology, or scope that the reader should consider when weighing the findings. Be specific — "more data would help" is not a limitation; "the sample does not include customers acquired after the pricing change, which limits our ability to assess its impact on new acquisition" is.

Total length: 700-1200 words depending on analytical complexity. The report should be proportional to the analysis — a simple metric review does not need 1,200 words; a multi-variable analysis might.
</output_format>
```

**Watch for:** Claude may invent specific numbers, percentages, or statistical results when the context does not provide actual data. If the analysis is based on described data rather than provided data, add: *"Work only with the specific numbers provided. Where data is described qualitatively but not quantified, state what analysis you would run and what result would be meaningful — do not fabricate specific figures."*

**Also watch for:** The Interpretation section simply restating the findings in different words rather than adding analytical value. If the interpretation feels redundant, add: *"The interpretation must add insight beyond the findings. What do the findings mean when considered together? What is the 'so what' for the decision at hand? If the interpretation just restates the findings, it is not doing its job."*

---

## Literature Review

**Use when:** You need a formal review of a body of evidence on a specific topic, organized by theme and assessed for quality. Use this when the audience needs to understand the full landscape of evidence, not just the conclusions.

**Distinct from:** Research Summary (which is shorter and focused on implications for a specific decision) — this is a comprehensive survey of what is known, how strong the evidence is, and where the gaps are.

**Target length:** 1200-2000 words. Comprehensive without being exhaustive.

```xml
<output_format>
Structure as a literature review:

Introduction: (1-2 paragraphs) The topic under review, why it matters, and the scope of the review — what types of evidence were included, what was excluded, and what time period was covered. State the organizing question that this review answers.

Thematic Sections: (2-4 themes, each 2-3 paragraphs) Organize the evidence by theme, not by source. Each section covers a major aspect of the topic, synthesizes findings across sources, notes where evidence converges or conflicts, and assesses the overall strength of evidence for that theme. Within each theme, cite specific sources to support claims but do not structure the section around individual sources.

Evidence Quality Assessment: (1-2 paragraphs) An overall assessment of how strong the evidence base is. What types of evidence dominate (experimental, observational, case study, expert opinion)? How consistent are the findings? Where is the evidence robust enough to support confident conclusions, and where is it too thin or too conflicted?

Gaps and Future Directions: (1 paragraph) What important questions remain unanswered? Where would additional research have the most impact on understanding or decision-making?

Conclusions: (1-2 paragraphs) What the body of evidence collectively supports. State conclusions with calibrated confidence — distinguish between what the evidence strongly supports, what it suggests, and what remains uncertain.

Total length: 1200-2000 words. A literature review should be comprehensive without being exhaustive — cover the major findings and debates, not every study ever conducted. Prioritize quality of synthesis over quantity of sources cited.
</output_format>
```

**Watch for:** Claude may produce literature reviews that are really annotated bibliographies — summarizing each source in turn rather than synthesizing across sources by theme. If the output follows a "Source A found X, Source B found Y" structure, the fundamental instruction is being violated. Reinforce with: *"Never organize a section around a single source. Every paragraph should synthesize findings from multiple sources. If a finding comes from only one source, note this as a limitation rather than dedicating a paragraph to that source."*

**Also watch for:** Claude inventing citations or studies. A literature review depends on real sources. If the context does not provide specific sources, add: *"Review only sources provided in the context. Do not fabricate studies, authors, or findings. If the available sources are insufficient for a comprehensive review, state what additional evidence would be needed."*

---

## Briefing Document

**Use when:** You need to prepare someone to walk into a meeting, negotiation, or decision with comprehensive background knowledge on a topic. This is designed for action-readiness — it includes not just what is known, but what the key tensions are, what stakeholders' positions are, and what questions are likely to come up.

**Distinct from:** Research Summary (which synthesizes evidence toward conclusions) — this prepares someone for a new engagement. Distinct from Stakeholder Update (which reports progress) — this gets someone up to speed for action.

**Target length:** 800-1500 words. Readable in under 10 minutes.

```xml
<output_format>
Structure as a briefing document:

Situation Overview: (2-3 paragraphs) What is happening, why it matters, and what the current state of play is. Write for someone who knows the general domain but not the specifics of this situation. Provide enough context that they could walk into a room and understand the conversation immediately.

Key Stakeholders and Positions: (1 paragraph per stakeholder or group, for 2-4 stakeholders) Who are the major players, what are their positions, and what are their underlying interests? For each, note what they are likely to push for and what they would resist. This section prepares the reader for the interpersonal dynamics, not just the substantive issues.

Critical Facts and Data: (2-3 paragraphs or a concise table) The specific data points, findings, precedents, or facts that are most likely to shape the discussion. Curated and prioritized — not a data dump, but the ten things you would write on a notecard if you could only bring ten things into the room.

Unresolved Questions and Tensions: (1-2 paragraphs) What is not yet decided, what is contested, and where the key disagreements lie. For each tension, briefly note the strongest argument on each side. This section prepares the reader for the debate, not just the facts.

Potential Questions and Suggested Responses: (3-5 questions, each with a 2-3 sentence suggested response) The most likely questions the reader will face, with clear, defensible answers. These are not scripted talking points — they are substantive responses that demonstrate command of the material.

Total length: 800-1500 words. The briefing must be readable in under 10 minutes — the reader may be reviewing it immediately before the meeting. Every sentence should contribute to their preparedness. Cut everything that does not help them perform in the room.
</output_format>
```

**Watch for:** Claude may produce briefing documents that are comprehensive on the substance but miss the interpersonal dynamics — describing the topic thoroughly but not preparing the reader for the human elements of the meeting. If the Key Stakeholders section is thin or generic, add: *"For each stakeholder, describe their position with enough specificity that the reader could predict their likely objections and questions. Generic descriptions ('they are concerned about cost') are insufficient — state what specific cost concerns, why they hold that position, and what would address it."*

**Also watch for:** The Suggested Responses being too cautious or noncommittal. If the reader needs to project confidence, add: *"Suggested responses should be direct and substantive — the kind of answer that earns respect in the room. Hedged, diplomatic non-answers undermine the reader's credibility."*
