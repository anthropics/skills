---
source: https://github.com/firecrawl/skills/tree/main/skills/workflows/firecrawl-competitive-intel
name: firecrawl-competitive-intel
description: Monitor competitor pricing, features, changelogs, dashboards, and product changes with Firecrawl. Use for recurring competitive intelligence, pricing tier extraction, feature change tracking, or structured competitor alerts.
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

# Firecrawl Competitive Intel

Use this for monitoring competitors over time. This is not the broad competitor analysis workflow.

## Onboarding Interview

Infer competitors, focus, cadence, and output format from context. If competitors are clear, proceed immediately.

Ask at most 1-3 concise questions only if blocked, such as the competitor list, focus area, or whether authenticated pages/profiles are required.

## Firecrawl Collection Plan

For each competitor, use Firecrawl scrape or browser as needed:

- pricing pages, annual/monthly toggles, expanded feature tables
- feature and product pages
- changelogs, blogs, release notes, docs updates
- authenticated dashboards only when the user has legitimate access

## Parallel Work

If appropriate, use sub-agents or equivalent parallel task runners. A natural split is one competitor per researcher or one focus area per researcher.

Each researcher should return pricing tiers, features, recent changes, source URLs, and confidence notes.

## Final Deliverable

```markdown
# Competitive Intel: [Competitors]

## Alerts
[Notable pricing, feature, or positioning changes]

## Per-Competitor Breakdown
[Pricing tiers, feature inventory, recent changes]

## Cross-Competitor Comparison
[Pricing table, feature matrix, key differentiators]

## Suggested Follow-Ups
[What to monitor next]

## Sources
[URLs visited]

## Rerun Inputs
workflow: firecrawl-competitive-intel
competitors: [list]
focus: [all/pricing/features/changelog]
cadence: [one-off/weekly/monthly]
```

## JSON Shape

When structured output is requested, include `generatedAt`, `competitors`, `pricing`, `recentChanges`, `features`, and `sources`.

## Quality Bar

- Extract real plan names, limits, and dates when available.
- Note contact-sales or gated details instead of guessing.
- Preserve sources for diffing future runs.
