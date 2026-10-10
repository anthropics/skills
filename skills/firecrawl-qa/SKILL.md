---
source: https://github.com/firecrawl/skills/tree/main/skills/workflows/firecrawl-qa
name: firecrawl-qa
description: QA test a live website with Firecrawl browser and scrape evidence. Use when the user wants exploratory QA, form testing, navigation/link checks, responsive checks, performance observations, bug reports, or a pre-launch quality review.
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

# Firecrawl QA

Use this to test a live site and return a unified QA report.

## Onboarding Interview

Infer the URL, QA focus, and output format from context. If the target URL is clear, proceed immediately.

Ask at most 1-3 concise questions only if blocked, such as the URL, the focus area, or credentials/constraints for protected flows.

## Firecrawl Collection Plan

Use Firecrawl map to discover pages. Use Firecrawl browser for interactions, forms, navigation, and responsive/manual checks when available. Use scrape for page content and link extraction.

## Parallel Work

If appropriate, use sub-agents or equivalent parallel task runners:

- Full: Navigation and Links, Forms and Interactions, Content and Visual, Error States.
- Forms: Form Discovery, Happy Path, Edge Cases, Validation.
- Navigation: Sitemap, Nav Testing, Link Checker, Routing.
- Responsive: Desktop, Tablet, Mobile, Interaction.
- Performance: Page Load, Asset Audit, Content Efficiency, Comparison.

Each tester should return severity, URL, description, evidence, and reproduction steps.

## Final Deliverable

```markdown
# QA Report: [Site]

## Summary
- Health score: [x/10]
- Pages tested: [count]
- Issues found: [critical/major/minor]

## Critical Issues
[C-1] URL | Description | Steps to reproduce | Expected vs actual

## Major Issues
[M-1] URL | Description | Steps to reproduce

## Minor Issues
[m-1] URL | Description

## Positive Observations
[What works well]

## Pages Tested
[URLs]

## Agent/Test Summary
[Who tested what]

## Rerun Inputs
workflow: firecrawl-qa
url: [url]
focus: [full/forms/navigation/responsive/performance]
```

## Quality Bar

- Include reproduction steps for functional issues.
- Do not report speculative bugs without evidence.
- Deduplicate findings across testers.
