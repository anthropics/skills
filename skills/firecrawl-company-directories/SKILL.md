---
source: https://github.com/firecrawl/skills/tree/main/skills/workflows/firecrawl-company-directories
name: firecrawl-company-directories
description: Extract structured company lists from directories with Firecrawl. Use for scraping YC, Crunchbase, Product Hunt, G2, startup directories, category directories, or custom company databases into JSON, CSV, CRM-ready lists, or research tables.
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

# Firecrawl Company Directories

Use this to turn startup or company directories into structured lists.

## Onboarding Interview

Infer the directory, filters, result count, and output format from context. If the source is clear, proceed immediately.

Ask at most 1-3 concise questions only if blocked, such as the directory URL/name, required filters, or target result count.

## Firecrawl Collection Plan

Use Firecrawl browser when the directory needs filters, pagination, infinite scroll, or profile clicks. Use scrape/map when listings are public and static.

Suggested sources include YC companies, Crunchbase, Product Hunt, G2 categories, or any custom directory URL.

## Extraction Fields

Capture fields that are visible:

- name
- description
- industry/category
- stage/founded/location/team size/funding when visible
- tags
- directory profile URL
- company website URL

Leave unavailable fields blank. Do not infer.

## Final Deliverable

```markdown
# Company Directory Export: [Source]

## Summary
[Filters, count extracted, limitations]

## Companies
[Table or link to JSON/CSV]

## Sources
[Directory pages and profiles used]

## Rerun Inputs
workflow: firecrawl-company-directories
directory: [source]
filters: [criteria]
max_results: [number]
output: [json/csv/markdown]
```

## JSON Shape

Use `source`, `filters`, `extractedAt`, `totalResults`, and `companies[]` with `name`, `url`, `description`, `industry`, `stage`, `founded`, `location`, `teamSize`, `funding`, `tags`, `profileUrl`, and `websiteUrl`.

## Quality Bar

- Deduplicate companies.
- Track pagination progress.
- Note rate limits, login walls, or CAPTCHA blocks.
