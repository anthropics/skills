---
source: https://github.com/firecrawl/skills/tree/main/skills/workflows/firecrawl-dashboard-reporting
name: firecrawl-dashboard-reporting
description: Pull metrics from analytics dashboards and internal web tools with Firecrawl browser. Use when the user needs dashboard reporting, cross-platform metric summaries, authenticated analytics extraction, date-range reports, or structured metrics from web dashboards.
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

# Firecrawl Dashboard Reporting

Use this to extract visible metrics from dashboards the user can legitimately access.

## Onboarding Interview

Infer dashboard URLs, metrics, date range, and output format from context. If dashboard targets are clear and accessible, proceed immediately.

Ask at most 1-3 concise questions only if blocked, such as the dashboard URLs, auth/profile requirement, or date range.

## Firecrawl Collection Plan

Use Firecrawl browser for authenticated dashboards and UI interaction:

- open each dashboard
- set or verify date range
- extract visible KPI cards, tables, and labels
- click tabs, expand sections, and scroll tables
- use export/download buttons only when appropriate and allowed

If login has expired, ask the user to re-authenticate rather than attempting to bypass access controls.

## Parallel Work

If appropriate, use sub-agents or equivalent parallel task runners. Split by dashboard platform or metric category. Each researcher should return metrics, units, period, source URL, and caveats.

## Final Deliverable

```markdown
# Dashboard Report

## Summary
[Highlights, alerts, trends]

## Metrics By Dashboard
[Platform, metric, value, unit, change, period]

## Tables Or Exports
[Captured tables/files and what they contain]

## Notes And Caveats
[Auth issues, chart-only data, unavailable metrics]

## Rerun Inputs
workflow: firecrawl-dashboard-reporting
dashboards: [urls]
date_range: [range]
metrics: [list]
output: [json/markdown]
```

## JSON Shape

Use `reportedAt`, `dateRange`, `dashboards[]`, `metrics[]`, `tables[]`, `exports[]`, and `summary`.

## Quality Bar

- Extract actual numbers, not just chart labels.
- Note when a chart cannot be read precisely.
- Preserve date ranges and source URLs.
