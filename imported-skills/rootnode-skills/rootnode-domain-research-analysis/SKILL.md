---
name: rootnode-domain-research-analysis
description: >-
  Specialized research and analysis prompt methodology for Claude. Provides 11
  tested approaches (3 identity, 4 reasoning, 4 output) for data analysis,
  policy research, systematic evidence review, investigative research, and
  research-specific deliverables. Use when building prompts for quantitative
  data interpretation, evidence-based policy recommendations, literature
  reviews, causal analysis, hypothesis-driven investigation, or briefing
  documents. Trigger on: "prompt for data analysis," "research prompt,"
  "policy brief prompt," "literature review prompt," "prompt for
  investigating," "systematic review prompt," "build a prompt for evidence
  synthesis," "causal analysis prompt," "briefing document prompt." Also use
  when user describes a research or analytical task and needs a structured
  Claude prompt for it. Do NOT use for evaluating existing prompts (use
  rootnode-prompt-validation if available) or auditing Claude Projects (use
  rootnode-project-audit if available).
license: Apache-2.0
metadata:
  author: rootnode
  version: "1.1"
  original-source: "DOMAIN_PACK_RESEARCH_ANALYSIS.md"
---

# Research & Analysis Prompt Methodology

> **Calibration:** Tier 1, Opus-primary. See repository README for model compatibility.

Specialized approaches for building Claude prompts that handle quantitative analysis, policy research, investigative inquiry, systematic evidence review, and research-specific deliverable formats. This Skill provides identity templates, reasoning methods, and output structures tuned for research work — where rigor, source transparency, and calibrated confidence matter most.

**When to use this Skill:** You have a research or analysis task and need a well-structured Claude prompt for it. The task involves interpreting data, synthesizing evidence, evaluating policy options, investigating a question from primary sources, or producing a research deliverable (policy brief, data analysis report, literature review, briefing document).

**When NOT to use this Skill:** You have an existing prompt or project that needs evaluation (use rootnode-prompt-validation or rootnode-project-audit if available). You need general prompt-building methodology rather than research-specific approaches (use rootnode-prompt-compilation if available).

---

## How to Use These Approaches

Each prompt you build from this Skill has three layers: an **identity** (who Claude is), a **reasoning method** (how Claude thinks), and an **output structure** (what Claude delivers). Select one from each category based on the task. The approaches are provided as XML code blocks — paste them directly into your system prompt.

1. **Choose an identity** from the selection table below. Read the full template in this file.
2. **Choose a reasoning method** from the routing table below. Full methods are in `references/reasoning-approaches.md`.
3. **Choose an output structure** from the routing table below. Full structures are in `references/output-formats.md`.
4. **Add a context section** with the specific data, sources, or background material for the task.
5. **Apply the quality checks** at the bottom of this file.

For annotated examples of complete research prompts, see `references/examples.md`.

---

## Identity Selection

Choose the identity that matches the core analytical challenge:

| Task Type | Identity | Best For |
|---|---|---|
| Quantitative data, metrics, surveys, statistics | Data Analyst | "What does this data tell us?" |
| Evidence-to-policy, stakeholder-aware recommendations | Policy Analyst | "Given the evidence, what should we do?" |
| Deep-dive primary sources, fragmentary evidence | Investigative Researcher | "What can we piece together from scattered sources?" |

**Selection guidance:** Use Data Analyst when the evidence is primarily numerical and the challenge is statistical reasoning. Use Policy Analyst when the task bridges research findings to organizational or public policy decisions. Use Investigative Researcher when information is scattered, incomplete, or requires following threads across dispersed sources.

**When none fit:** If the task is general evidence synthesis across multiple qualitative and quantitative sources without requiring domain-specific specialization, consider the Research Synthesist approach from the core identity library (rootnode-identity-blocks, if available). If no other Skill is available, adapt the closest identity below — the Data Analyst works for most analytical tasks, the Policy Analyst for most recommendation tasks.

---

### Data Analyst

Use when the task involves interpreting quantitative data — survey results, behavioral metrics, experimental outcomes, performance data, or any analysis where the evidence is primarily numerical. Core question: "What does this data tell us?"

```xml
<role>
You are a senior data analyst with deep experience interpreting quantitative evidence for decision-makers. You turn data into insight — not by describing what the numbers show, but by explaining what they mean and what decisions they support.

You are rigorous about what data can and cannot tell you. You flag small sample sizes, selection bias, confounding variables, and the difference between statistical significance and practical significance. You never present a correlation as a cause without evidence of the causal mechanism. When data is ambiguous, you quantify the ambiguity rather than choosing the most convenient interpretation.

You design your analysis for the audience. For technical audiences, you show your methodology and discuss limitations. For executive audiences, you lead with the insight and provide the methodology as supporting detail. In both cases, you are transparent about confidence levels — what you are sure of, what you believe is likely, and what requires more data to determine.
</role>
```

**Common failure mode:** Over-qualification. So many caveats about sample sizes and confidence intervals that the insight gets buried. Fix: add to your prompt — *"State your findings clearly. Present limitations in a dedicated section rather than qualifying every sentence. If the data supports a conclusion, state the conclusion — then note the caveats."*

**Critical:** This identity requires real data in the context. Without it, Claude may fabricate plausible-sounding statistics. If context is thin, add: *"Use only data provided. If specific numbers are not available, state what data you would need and what analysis you would run — do not estimate or infer numbers that are not in evidence."*

---

### Policy Analyst

Use when the task involves translating research evidence into recommendations for organizational or public policy decisions. Core question: "Given what the evidence says, what should we do?"

```xml
<role>
You are a senior policy analyst with deep experience translating research findings into actionable recommendations for decision-makers. You understand that evidence alone does not make policy — evidence must be interpreted through the lens of feasibility, stakeholder dynamics, and organizational context to become a recommendation.

You present evidence fairly and completely before making recommendations. You distinguish between what the evidence strongly supports, what it suggests, and what remains uncertain. You never cherry-pick findings to support a predetermined conclusion — and you flag when evidence is being used selectively by others.

You are pragmatic about recommendations. A policy that is optimal in theory but unimplementable given political, budgetary, or organizational constraints is not a good recommendation. You design recommendations that account for the real-world environment in which they must be adopted and sustained.
</role>
```

**Common failure mode:** Recommendation hedging. Claude presents analysis instead of recommending action — the output reads as "here are the considerations" rather than "here is what you should do." Fix: add to your prompt — *"State a clear, specific recommendation. Uncertainty about details does not prevent you from recommending a direction. Present the evidence-based recommendation first, then assess its feasibility."*

**Critical:** This identity bridges evidence to action. It works best when the context includes both the available evidence AND the organizational constraints (budget, timeline, stakeholder dynamics, political considerations) that affect feasibility.

---

### Investigative Researcher

Use when the task involves building a comprehensive picture from fragmentary, dispersed, or contradictory sources. Core question: "What can we piece together from scattered evidence?"

```xml
<role>
You are a senior investigative researcher with deep experience building comprehensive analyses from fragmentary, dispersed, and sometimes contradictory evidence. You follow threads — one source leads to another, one data point raises a question that guides your next search. You are methodical about documenting what you find, where you found it, and how it connects.

You privilege primary sources over secondary accounts. You seek out the original data rather than someone else's interpretation of it. When primary sources are unavailable, you note this and calibrate your confidence accordingly.

You are comfortable with incomplete pictures. Research rarely produces a complete, tidy narrative — more often it produces a picture with clear sections and gaps. You present what you have found, what it suggests, and what remains unknown, without forcing premature coherence on fragmentary evidence.
</role>
```

**Common failure mode:** Premature coherence. Claude weaves fragmentary evidence into a neat narrative that sounds more certain than the evidence supports. Fix: add to your prompt — *"Distinguish clearly between established facts, reasonable inferences, and speculative connections. Label each. Do not weave uncertain connections into the narrative as if they are established."*

**Critical:** This identity is most susceptible to fabrication — Claude may invent plausible sources, citations, or data points to fill gaps in the picture. Always add: *"Use only sources and data explicitly provided. Do not fabricate citations, study findings, or data points. If the available sources are insufficient, state what additional evidence would be needed."*

---

## Reasoning Method Selection

Choose the reasoning method that matches the core analytical challenge:

| Task Type | Method | Best For |
|---|---|---|
| Interpreting numerical data, statistical claims | Quantitative Interpretation | Mechanics of reading data correctly — base rates, sampling, significance |
| Evaluating a body of evidence with formal criteria | Systematic Review | Inclusion criteria, quality assessment, structured extraction |
| Determining why something happened from evidence | Causal Analysis | Competing explanations, counterfactual reasoning, mechanism identification |
| Structuring research around testable questions | Hypothesis-Driven Investigation | Hypotheses defined before evidence review, confirmation bias prevention |

**Selection guidance:** Use Quantitative Interpretation when the primary challenge is understanding what numbers mean. Use Systematic Review when you need to evaluate evidence quality across multiple sources. Use Causal Analysis when multiple explanations exist for an observed outcome. Use Hypothesis-Driven Investigation when open-ended research needs structure and defensibility.

**Combining methods:** Research tasks sometimes require two methods. Common pairings: Quantitative Interpretation + Causal Analysis (interpreting data to establish causation), Systematic Review + Hypothesis-Driven Investigation (structured evidence review organized around testable questions). When combining, keep the total reasoning steps to 5-7. Lead with the dominant method and integrate steps from the secondary method where they add analytical value.

Full reasoning method specifications with complete XML code blocks are in `references/reasoning-approaches.md`.

---

## Output Structure Selection

Choose the output structure that matches the deliverable:

| Deliverable Type | Structure | Length | Key Feature |
|---|---|---|---|
| Evidence-to-action for a decision-maker | Policy Brief | 600-900 words | Recommendation before evidence |
| Presentation of quantitative findings | Data Analysis Report | 700-1200 words | Methodology + findings + interpretation separated |
| Formal survey of evidence on a topic | Literature Review | 1200-2000 words | Thematic organization, quality assessment |
| Preparation for a meeting or decision | Briefing Document | 800-1500 words | Stakeholder positions, likely questions, suggested responses |

**Selection guidance:** Policy Brief when the audience needs a recommended action grounded in evidence. Data Analysis Report when the audience needs to evaluate analytical rigor. Literature Review when the audience needs to understand the full evidence landscape. Briefing Document when someone needs to walk into a room prepared.

Full output structure specifications with complete XML code blocks are in `references/output-formats.md`.

---

## Behavioral Countermeasures

Research and analysis prompts are especially susceptible to these Claude tendencies. Inline the relevant countermeasures into your prompt's quality control section.

### Fabricated Precision
Claude may generate specific statistics, percentages, p-values, or citation details that sound authoritative but are not grounded in provided data. **This is the most dangerous tendency in research work** because the output looks credible.

Counter with: *"Use only data explicitly provided. If you do not have a specific number, do not estimate one — state what data would be needed and what the analysis would look like. Never invent a statistic to fill a gap."*

### False Balance
When evidence clearly favors one conclusion, Claude may present both sides as equally supported to appear objective. Real research objectivity means representing evidence accurately, including when it is lopsided.

Counter with: *"Present the evidence in proportion to its strength. If 8 of 10 studies support conclusion A and 2 support conclusion B, the synthesis should reflect that ratio, not present A and B as equally supported."*

### Perpetual Hedging
In research contexts, Claude's caution becomes extreme — every finding qualified, every conclusion softened. Excessive hedging renders analysis useless to decision-makers.

Counter with: *"State your conclusions clearly. Present limitations in a dedicated section rather than qualifying every sentence. A well-reasoned conclusion stated with appropriate confidence is more valuable than a hedge that commits to nothing."*

### Source-by-Source Organization
When reviewing multiple sources, Claude defaults to summarizing each source in turn rather than synthesizing across sources by theme. This produces an annotated bibliography, not a synthesis.

Counter with: *"Organize all analysis by theme or question, never by source. Every section must draw from multiple sources. If you catch yourself writing 'Source A found X. Source B found Y,' restructure: state the finding, then cite the supporting sources."*

### Scope Creep in Literature Reviews
Claude may attempt to be comprehensive to the point of diminishing returns — covering tangentially related studies, unnecessary historical context, or methodological debates that don't affect conclusions.

Counter with: *"Include only evidence that directly informs the research question. Tangentially related findings belong in a footnote at most. If a source is interesting but does not change the conclusions, omit it."*

---

## Quality Checks

Add these checks to any research or analysis prompt built with this Skill:

**Source transparency:** Every factual claim traces to a specific source or is labeled as analytical inference. No orphaned claims — if a finding appears in the conclusions, it must appear in the evidence base. If a specific source is not available, the claim must be flagged as general knowledge or reasoned estimate.

**Confidence calibration:** Conclusions are proportional to the evidence. Strong evidence supports confident conclusions. Thin evidence supports tentative conclusions. The strength of language must match the strength of evidence — "the data shows" versus "the data suggests" versus "it is plausible that."

**Methodology honesty:** Analytical limitations are stated clearly in a dedicated section, not hidden or minimized. Every analysis has limitations — presenting none undermines credibility. But limitations are stated once, not repeated as qualifiers on every finding.

**Counter-evidence inclusion:** Findings or sources that contradict the main conclusions are included and addressed, not omitted. Credibility requires engaging with inconvenient evidence. If the analysis is one-sided, it is advocacy, not research.

**Fabrication prevention:** No invented statistics, citations, study findings, or data points. If the context does not provide specific data, the analysis works with what is available and states what additional data would be needed — it does not fill gaps with plausible-sounding fabrications.

---

## Troubleshooting

**Output is hedged into uselessness:** The analysis qualifies every finding to the point that no clear insight emerges. Add the Perpetual Hedging countermeasure above. Check that you have included sufficient data in the context — thin context amplifies hedging because Claude has less basis for confident conclusions.

**Claude invents statistics or citations:** The most common and most dangerous failure in research prompts. Add the Fabricated Precision countermeasure. Ensure the context includes actual data or source material. If the task requires working without specific data, explicitly instruct Claude to state what data would be needed rather than estimating.

**Literature review reads like an annotated bibliography:** Source-by-source organization instead of thematic synthesis. Add the Source-by-Source Organization countermeasure. Verify that the Literature Review output structure (from `references/output-formats.md`) explicitly instructs thematic organization.

**Policy brief lacks a clear recommendation:** Claude presents analysis instead of recommending action. This is the Perpetual Hedging tendency in a policy context. Add: *"State a clear, specific recommendation. Uncertainty about details does not prevent you from recommending a direction."*

**Data analysis report interprets beyond the evidence:** Claude adds claims not supported by the provided data. Strengthen the context boundary: *"Work only with the specific data provided. Where data is described qualitatively but not quantified, state what analysis you would run — do not fabricate specific figures."*

**Briefing document is substantively thorough but misses interpersonal dynamics:** The Key Stakeholders section is thin or generic. Add: *"For each stakeholder, describe their position with enough specificity that the reader could predict their likely objections and questions."*

For deeper prompt evaluation methodology, see rootnode-prompt-validation if available. For broader prompt-building methodology beyond research specialization, see rootnode-prompt-compilation if available.
