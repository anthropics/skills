---
name: deep-research
description: "Conduct a thorough multi-source academic literature search and synthesise findings into a structured report. Use when asked to research a topic, survey a field, investigate a question, or produce a literature review. Covers: scope calibration, search strategy across multiple databases, paper reading, discrepancy analysis, structured synthesis, and saving results. TRIGGER when: user says 'research', 'investigate', 'survey the literature', 'literature review', 'what does the research say about', or asks for a structured report with sources. SKIP: simple factual questions, definitions, calculations, or conversational replies answerable from training knowledge."
license: MIT
---

# Deep Research Skill

A structured workflow for thorough academic literature research — from scope calibration and multi-source search through critical synthesis and saving the final report.

## When to Use

- User asks to "research", "investigate", "survey", or "review the literature" on a topic
- User wants a structured report with sources and citations
- User wants findings saved to a note-taking tool or knowledge base
- The task requires reading multiple academic papers and synthesising them critically

Do **not** use this skill for simple factual questions answerable from training knowledge, brief definitions, quick calculations, or casual conversational replies.

## Step 1 — Calibrate Scope

Read the query carefully **before** doing anything else:

- **Narrow/specific query** (a particular method, compound, model, phenomenon, dataset): stay tightly within that context; do not broaden to the general field unnecessarily. Depth and specificity matter more than breadth.
- **Broad/survey query** (a research area, open problem, field overview): survey major themes, schools of thought, and representative work. Representative coverage matters more than exhaustive detail.

## Step 2 — Plan

Create a research plan — sub-topics to cover, search angles, terminology variants, and specific papers or authors worth targeting. Use a planning tool (`write_todos`, a notes file, or similar) if one is available.

## Step 3 — Search Broadly

Run **at least 5–6 searches** across multiple sources using varied terminology to avoid missing relevant work:

- **Peer-reviewed databases** (OpenAlex, Semantic Scholar, PubMed, Web of Science): prioritise for highly-cited foundational work.
- **Preprint servers** (arXiv, bioRxiv, SSRN): use for recent and cutting-edge research (last 1–3 years).
- **Web search**: use to find books, review articles, blog posts, and resources not indexed in academic databases.

Vary terminology across searches — use synonyms, acronyms, related concepts, and field-specific jargon to maximise coverage.

## Step 4 — Read Key Papers

For the **2–4 most relevant papers**, read the full text (not just the abstract). Delegate to a paper-reading tool or subagent if one is available (e.g., one that fetches full text by DOI and isolates figures/noise).

Ask targeted, precise questions when reading:
- "What methodology and experimental setup was used?"
- "What are the exact quantitative results and metrics reported?"
- "What are the stated limitations and failure cases?"
- "How does this compare to [specific prior work] in terms of [metric]?"
- "What dataset was used and how was it collected?"

If a local knowledge base is available, save a structured note for each paper so findings accumulate across sessions.

## Step 5 — Retrieve and Compare

Before writing, query your local knowledge base or search results for the most semantically relevant documents across all searches. Actively compare findings: where do sources agree, where do they contradict, and what methodological differences explain the disagreements?

## Step 6 — Synthesise

Write a comprehensive, critically engaged report with these sections:

### Background
Key concepts, theoretical foundations, and the current state of the field as established in the literature. Cite inline as [Author, Year].

### Key Findings
The main results and contributions from the literature. Group related findings and note where multiple independent sources corroborate a result.

### Discrepancies and Debates
Explicitly surface conflicting evidence and contradictory claims between sources. For each discrepancy: state what each side claims, cite the sources, and offer a reasoned explanation for why the disagreement exists (different methods, datasets, scopes, time periods, etc.).

**Do not smooth over contradictions.**

### Methodological Approaches
How researchers study this topic. Compare approaches: what each method can and cannot reveal, where results are method-dependent, and what the best-practice consensus is (if any).

### Open Questions
Specific unanswered questions and gaps that emerge from the literature. Prioritise questions directly relevant to the original query and that appear tractable.

### Conclusion
A direct, synthesised answer to the original research query, grounded in the evidence gathered. Be specific — do not hedge beyond what the evidence warrants.

## Step 7 — Save the Report

Save the report using whatever note-taking or knowledge-base tool is available (Notion, a markdown file, a project document, etc.). Include the full synthesis and a formatted sources list.

If no save tool is available, output the full report in the response.

## Analytical Principles

- Surface disagreements; do not smooth over contradictions.
- Distinguish between well-replicated findings and single-study claims.
- For narrow queries, depth and specificity matter more than breadth.
- For broad queries, representative coverage matters more than exhaustive detail.
- Every claim in the synthesis must be traceable to a source retrieved in this session — do not rely on training knowledge for factual claims.
- Do not skip the retrieval/comparison step before writing the synthesis.
