---
source: https://github.com/firecrawl/skills/tree/main/skills/workflows/firecrawl-shop
name: firecrawl-shop
description: Research products across the web with Firecrawl and produce a shopping recommendation or cart-ready summary. Use when the user wants to compare products, find the best option, evaluate reviews, respect budget/preferences, or shop with a saved browser session.
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

# Firecrawl Shop

Use this to research products and recommend a purchase option. Only add items to a cart when the user explicitly asks and has an authenticated browser profile available.

## Onboarding Interview

Infer the product, budget, preferences, sites, and desired stopping point from context. If the product is clear, proceed immediately.

Ask at most 1-3 concise questions only if blocked, such as the product, hard budget/preferences, or whether cart actions are allowed.

## Firecrawl Collection Plan

Use Firecrawl search and scrape to compare reviews, product pages, specifications, pricing, Reddit/forums, and trusted review sites. Use Firecrawl browser for shopping-site navigation and cart actions when authorized.

## Process

1. Research product options across multiple sources.
2. Compare price, specs, reviews, seller quality, shipping, and fit to preferences.
3. Pick the best option and explain why.
4. If the user asked for cart actions, open the shopping site in browser, add the item, and stop before checkout unless explicitly instructed.

## Final Deliverable

```markdown
# Shopping Research: [Product]

## Recommendation
[Best option and why]

## Products Compared
[Product, price, seller, key specs, pros/cons]

## Review Signals
[Patterns from reviews and external sources]

## Cart Status
[Only if requested: item added, price, seller, confirmation]

## Sources
[URLs used]

## Rerun Inputs
workflow: firecrawl-shop
query: [product]
budget: [budget]
sites: [preferred sites]
```

## Quality Bar

- Be specific with model numbers, prices, and sellers.
- Do not purchase or check out without explicit approval.
- Note affiliate, sponsored, or unreliable sources when visible.
