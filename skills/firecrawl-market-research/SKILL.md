---
source: https://github.com/firecrawl/skills/tree/main/skills/workflows/firecrawl-market-research
name: firecrawl-market-research
description: Extract market, financial, earnings, industry, and company metrics with Firecrawl. Use when the user asks for market research, industry trends, public company data, financial comparisons, earnings research, or structured market reports.
license: ISC
metadata:
  author: firecrawl
  version: "0.1.0"
  homepage: https://www.firecrawl.dev
  source: https://github.com/firecrawl/firecrawl-workflows
inputs:
  - name: FIRECRAWL_API_KEY
    description: Firecrawl API key for hosted Firecrawl requests.
    required: true
---

# Firecrawl Market Research

Use this for sourced market and financial research.

## Onboarding Interview

Infer the market/company, data focus, timeframe, and output format from context. If the research target is clear, proceed immediately.

Ask at most 1-3 concise questions only if blocked, such as the market/company, required data focus, or timeframe/geography.

## Firecrawl Collection Plan

Use Firecrawl search and scrape for market reports, news, investor relations, SEC filings, and company pages. Use browser where charts, tabs, period selectors, or financial portals require interaction.

Common sources include company investor relations pages, SEC filings, financial portals, earnings releases, industry reports, and news.

## Parallel Work

If appropriate, use sub-agents or equivalent parallel task runners:

- company financials
- market metrics
- industry trends
- recent news and analyst commentary
- source validation

## Final Deliverable

```markdown
# Market Research: [Market]

## Market Overview
[Industry description, size, growth, key players]

## Company Profiles
[Financial summary, market metrics, recent developments]

## Comparison Tables
[Revenue, margins, valuation multiples, growth]

## Trends And Outlook
[Industry trends, forecasts, risks]

## Sources
[URLs and data extracted]

## Rerun Inputs
workflow: firecrawl-market-research
query: [market/company]
companies: [list]
data_points: [all/financial/metrics/trends]
output: [json/markdown]
```

## Quality Bar

- Cross-reference key numbers when possible.
- Note conflicting data across sources.
- Include period and unit for every metric.
- Do not provide financial advice.
