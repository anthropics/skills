---
source: https://github.com/firecrawl/skills/tree/main/skills/workflows/firecrawl-seo-audit
name: firecrawl-seo-audit
description: Audit a website's SEO with Firecrawl. Use when the user asks for an SEO audit, metadata and heading review, sitemap/site-structure analysis, keyword opportunities, competitor SERP comparison, or prioritized search optimization recommendations.
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

# Firecrawl SEO Audit

Use this to turn a website into a specific, prioritized SEO audit.

## Onboarding Interview

Infer the site, target keywords, and output format from context. If the site is clear, proceed immediately.

Ask at most 1-3 concise questions only if blocked, such as the site URL, required target keywords, or whether a specific page/competitor set matters.

## Firecrawl Collection Plan

1. Map the site with Firecrawl to understand URL structure.
2. Scrape key pages: homepage, product/service pages, pricing, docs, blog, about, and high-value landing pages.
3. Extract title tags, meta descriptions, headings, internal links, content structure, canonical signals when visible, and image alt text when available.
4. Search target keywords when provided; scrape top ranking pages for comparison.

## Parallel Work

If appropriate, use sub-agents or equivalent parallel task runners:

- Site Structure: URL patterns, sitemap health, internal linking, orphan/broken pages.
- On-Page SEO: titles, meta descriptions, H1/H2 hierarchy, content quality.
- Keyword And SERP: target keywords, ranking pages, competitor page patterns.
- Technical Issues: broken links, duplicate content signals, missing metadata.

## Final Deliverable

```markdown
# SEO Audit: [Site]

## Executive Summary
[Top risks and opportunities]

## Site Structure
[Pages found, URL quality, sitemap/internal-link notes]

## On-Page SEO
[Per-page title, meta, headings, content, linking notes]

## Keyword Opportunities
[Target keywords, missing pages, content gaps]

## Competitor/SERP Comparison
[Who outranks the site and why]

## Prioritized Recommendations
[High/medium/low impact fixes with exact changes]

## Sources
[URLs scraped and what was checked]

## Rerun Inputs
workflow: firecrawl-seo-audit
site: [url]
keywords: [list]
output: [markdown/json]
```

## Quality Bar

- Make recommendations specific, not generic.
- Show the page or source behind each issue.
- Distinguish technical findings from content strategy guesses.
