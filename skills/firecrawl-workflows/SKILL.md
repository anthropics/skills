---
source: https://github.com/firecrawl/skills/tree/main/skills/workflows/firecrawl-workflows
name: firecrawl-workflows
description: Run outcome-focused Firecrawl workflows that produce deliverables such as research reports, literature reviews over published papers, SEO audits, QA reports, lead lists, knowledge bases, website design systems, and other structured web-data artifacts. Use when the user wants Firecrawl to complete a business, marketing, product, or creative workflow rather than merely scrape a page or integrate API calls into code.
license: ISC
metadata:
  author: firecrawl
  version: "0.1.0"
  homepage: https://www.firecrawl.dev
  source: https://github.com/firecrawl/firecrawl-workflows
inputs:
  - name: FIRECRAWL_API_KEY
    description: Firecrawl API key for hosted Firecrawl requests when the workflow runs through the CLI or API.
    required: true
references:
  - references/workflow-authoring.md
---

# Firecrawl Workflows

Use this when the user wants a finished deliverable powered by Firecrawl, not only raw web extraction and not product-code integration.

## Choose The Workflow

- Use [firecrawl-website-design-clone](../firecrawl-website-design-clone/SKILL.md) to extract a website's colors, fonts, spacing, components, and layout patterns into an agent-ready `DESIGN.md`.
- Use [firecrawl-research-papers](../firecrawl-research-papers/SKILL.md) for literature reviews and paper-backed synthesis, including biomedical, clinical, drug, gene, disease, epidemiology, and public-health topics. It queries Firecrawl's paper index — PubMed, bioRxiv, medRxiv, and arXiv abstracts with full text reachable per paper — rather than searching websites.
- Use [firecrawl-deep-research](../firecrawl-deep-research/SKILL.md) for sourced multi-source research reports built from **web** evidence: market, policy, technical, or industry topics. Not for literature reviews — when the evidence base is published papers, use `firecrawl-research-papers` above.
- Use [firecrawl-seo-audit](../firecrawl-seo-audit/SKILL.md) for site structure, on-page SEO, keyword, and SERP audits.
- Use [firecrawl-lead-research](../firecrawl-lead-research/SKILL.md) for pre-meeting company/person intelligence briefs.
- Use [firecrawl-qa](../firecrawl-qa/SKILL.md) for live-site QA testing and bug reports.
- Use [firecrawl-competitive-intel](../firecrawl-competitive-intel/SKILL.md) for recurring pricing, feature, and changelog monitoring.
- Use [firecrawl-company-directories](../firecrawl-company-directories/SKILL.md) for directory extraction into company lists.
- Use [firecrawl-dashboard-reporting](../firecrawl-dashboard-reporting/SKILL.md) for dashboard metrics extraction.
- Use [firecrawl-knowledge-base](../firecrawl-knowledge-base/SKILL.md) for LLM-ready docs, RAG chunks, training data, or docs mirrors.
- Use [firecrawl-knowledge-ingest](../firecrawl-knowledge-ingest/SKILL.md) for auth-gated or JS-heavy docs portal ingestion.
- Use [firecrawl-lead-gen](../firecrawl-lead-gen/SKILL.md) for prospect list generation.
- Use [firecrawl-market-research](../firecrawl-market-research/SKILL.md) for market, financial, and industry research.
- Use [firecrawl-demo-walkthrough](../firecrawl-demo-walkthrough/SKILL.md) for product flow walkthroughs and UX teardown reports.
- Use [firecrawl-shop](../firecrawl-shop/SKILL.md) for product research and shopping recommendations.

If no existing workflow fits, use this generic process and produce a reusable pattern that could become a new skill.

## Required Intake

Infer the workflow, inputs, audience, and output format from the user's request and surrounding context. If enough is clear, start immediately.

Ask at most 1-3 concise clarifying questions only when a missing input would block the work, such as:

- the URL, company, topic, or source to analyze
- the desired deliverable or output format
- a constraint that would materially change the workflow

Use the host agent's normal way to ask clarifying questions. Do not depend on a harness-specific function name.

## Default Process

1. Confirm the workflow and final artifact.
2. Collect web evidence with Firecrawl through the CLI or equivalent Firecrawl tool surface.
3. Save or cite source evidence so the final claims are traceable.
4. Run independent research units in parallel when available.
5. Synthesize findings into the requested deliverable.
6. Include a short "rerun inputs" block when the workflow could be automated.

## Parallel Work

If appropriate, use sub-agents or equivalent parallel task runners for independent units such as:

- one competitor per researcher
- one URL or page per researcher
- one source category per researcher
- one analysis dimension per reviewer

Keep the handoff generic: provide the unit of work, source URLs or search terms, expected extracted fields, and output format.

## Deliverable Standards

Every workflow should return:

- a concise executive summary
- the evidence base used
- the analysis or artifact requested by the user
- recommendations or next actions when useful
- automation inputs for reruns

For authoring new workflow skills, see [workflow-authoring.md](references/workflow-authoring.md).
