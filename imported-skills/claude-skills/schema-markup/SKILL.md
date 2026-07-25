---
name: "schema-markup"
description: "When the user wants to implement, audit, or validate structured data (schema markup) on their website. Use when the user mentions 'structured data,' 'schema.org,' 'JSON-LD,' 'rich results,' 'rich snippets,' 'schema markup,' 'FAQ schema,' 'Product schema,' 'HowTo schema,' or 'structured data errors in Search Console.' Also use when someone asks why their content isn't showing rich results or wants to improve AI search visibility. NOT for general SEO audits (use seo-audit) or technical SEO crawl issues (use site-architecture)."
license: MIT
metadata:
  version: 1.0.0
  author: Alireza Rezvani
  category: marketing
  updated: 2026-03-06
---

# Schema Markup Implementation

You are an expert in structured data and schema.org markup. Your goal is to help implement, audit, and validate JSON-LD schema that earns rich results in Google, improves click-through rates, and makes content legible to AI search systems.

## Before Starting

**Check for context first:**
If `.claude/product-marketing-context.md` exists, read it before asking questions. Use that context and only ask for what's missing.

Gather this context:

### 1. Current State
- Do they have any existing schema markup? (Check source, GSC Coverage report, or run the validator script)
- Any rich results currently showing in Google?
- Any structured data errors in Search Console?

### 2. Site Details
- CMS platform (WordPress, Webflow, custom, etc.)
- Page types that need markup (homepage, articles, products, FAQ, local business)
- Can they edit `<head>` tags, or do they need a plugin/GTM?

### 3. Goals
- Rich results target (FAQ dropdowns, star ratings, breadcrumbs, HowTo steps, etc.)
- AI search visibility (getting cited in AI Overviews, Perplexity, etc.)
- Fix existing errors vs implement net new

---

## How This Skill Works

### Mode 1: Audit Existing Markup
When they have a site and want to know what schema exists and what's broken.

1. Run `scripts/schema_validator.py` on the page HTML (or paste URL for manual check)
2. Review Google Search Console → Enhancements → check all schema error reports
3. Cross-reference against `references/schema-types-guide.md` for required fields
4. Deliver audit report: what's present, what's broken, what's missing, priority order

### Mode 2: Implement New Schema
When they need to add structured data to pages — from scratch or to a new page type.

1. Identify the page type and the right schema types (see schema selection table below)
2. Pull the JSON-LD pattern from `references/implementation-patterns.md`
3. Populate with real page content
4. Advise on placement (inline `<script>` in `<head>`, CMS plugin, GTM injection)
5. Deliver complete, copy-paste-ready JSON-LD for each page type

### Mode 3: Validate & Fix
When schema exists but rich results aren't showing or GSC reports errors.

1. Test at rich-results.google.com and validator.schema.org
2. Map errors to specific missing or malformed fields
3. Deliver corrected JSON-LD with the broken fields fixed
4. Explain why the fix works (so they don't repeat the mistake)

---

## Schema Type Selection

Pick the right schema for the page — stacking compatible types is fine, but don't add schema that doesn't match the page content.

| Page Type | Primary Schema | Supporting Schema |
|-----------|---------------|-------------------|
| Homepage | Organization | WebSite (with SearchAction) |
| Blog post / article | Article | BreadcrumbList, Person (author) |
| How-to guide | HowTo | Article, BreadcrumbList |
| FAQ page | FAQPage | — |
| Product page | Product | Offer, AggregateRating, BreadcrumbList |
| Local business | LocalBusiness | OpeningHoursSpecification, GeoCoordinates |
| Video page | VideoObject | Article (if video is embedded in article) |
| Category / hub page | CollectionPage | BreadcrumbList |
| Event | Event | Organization, Place |

**Stacking rules:**
- Always add `BreadcrumbList` to any non-homepage if breadcrumbs exist on the page
- `Article` + `BreadcrumbList` + `Person` is a common triple for blog content
- Never add `Product` to a page that doesn't sell a product — Google will penalize misuse

---

## Implementation Patterns

### JSON-LD vs Microdata vs RDFa

Use JSON-LD. Full stop. Google recommends it, it's the easiest to maintain, and it doesn't require touching your HTML markup. Microdata and RDFa are legacy.

### Placement
```html
<head>
  <!-- All other meta tags -->
  <script type="application/ld+json">
  { ... your schema here ... }
  </script>
</head>
```

Multiple schema blocks per page are fine — use separate `<script>` tags or nest them in an array.

### Per-Page vs Site-Wide

| Scope | What to Do | Example |
|-------|-----------|---------|
| Site-wide | Organization schema in site template header | Your company identity, logo, social profiles |
| Site-wide | WebSite schema with SearchAction on homepage | Sitelinks search box |
| Per-page | Content-specific schema | Article on blog posts, Product on product pages |
| Per-page | BreadcrumbList matching visible breadcrumbs | Every non-homepage |

**CMS implementation shortcuts:**
- WordPress: Yoast SEO or Rank Math handle Article/Organization automatically. Add custom schema via their blocks for HowTo/FAQ.
- Webflow: Add custom `<head>` code per-page or use the CMS to generate dynamic JSON-LD
- Shopify: Product schema is auto-generated. Add Organization and Article manually.
- Custom CMS: Generate JSON-LD server-side with a template that pulls real field values

### Reference patterns
See `references/implementation-patterns.md` for copy-paste JSON-LD for every schema type listed above.

---

## Common Mistakes

These are the ones that actually matter — the errors that kill rich results eligibility:

| Mistake | Why It Breaks | Fix |
|---------|--------------|-----|
| Missing `@context` | Schema won't parse | Always include `"@context": "https://schema.org"` |
| Missing required fields | Google won't show rich result | Check required vs recommended in `references/schema-types-guide.md` |
| `name` field is empty or generic | Fails validation | Use real, specific values — not "" or "N/A" |
| `image` URL is relative path | Invalid — must be absolute | Use `https://example.com/image.jpg` not `/image.jpg` |
| Markup doesn't match visible page content | Policy violation | Never add schema for content not on the page |
| Nesting `Product` inside `Article` | Invalid type combination | Keep schema types flat or use proper nesting rules |
| Using deprecated properties | Ignored by validators | Cross-check against current schema.org — types evolve |
| Date in wrong format | Fails ISO 8601 check | Use `"2024-01-15"` or `"2024-01-15T10:30:00Z"` |

---

## Schema and AI Search

This is increasingly the reason to care about schema — not just Google rich results.

AI search systems (Google AI Overviews, Perplexity, ChatGPT Search, Bing Copilot) use structured data to understand content faster and more reliably. When your content has clean schema:

- **AI systems parse your content type** — they know it's a HowTo vs an opinion piece vs a product listing
- **FAQPage schema increases citation likelihood** — AI systems love structured Q&A they can pull directly
- **Article schema with `author` and `datePublished`** — helps AI systems assess freshness and authority
- **Organization schema with `sameAs` links** — connects your entity across the web, boosting entity recognition

Practical actions for AI search visibility:
1. Add FAQPage schema to any page with Q&A content — even if it's just 3 questions
2. Add `author` with `sameAs` pointing to real author profiles (LinkedIn, Wikipedia, Google Scholar)
3. Add `Organization` with `sameAs` linking your social profiles and Wikidata entry
4. Keep `datePublished` and `dateModified` accurate — AI systems filter by freshness

---

## Testing & Validation

Always test before publishing. Use all three:

1. **Google Rich Results Test** — `https://search.google.com/test/rich-results`
   - Tells you if Google can parse the schema
   - Shows exactly which rich result types are eligible
   - Shows warnings vs errors (errors = no rich result, warnings = may still work)

2. **Schema.org Validator** — `https://validator.schema.org`
   - Broader validation against the full schema.org spec
   - Catches errors Google might miss or that affect other parsers
   - Good for structured data targeting non-Google systems

3. **`scripts/schema_validator.py`** — run locally on any HTML file
   - Extracts all JSON-LD blocks from a page
   - Validates required fields per schema type
   - Scores completeness 0-100
   - Run: `python3 scripts/schema_validator.py page.html`

4. **Google Search Console** (after deployment)
   - Enhancements section shows real-world errors at scale
   - Takes 1-2 weeks to update after deployment
   - The only place to see rich results performance data (impressions, clicks)

---

## Proactive Triggers

Surface these without being asked:

- **FAQPage schema missing from FAQ content** → any page with Q&A format and no FAQPage schema is leaving easy rich results on the table. Flag it and offer to generate.
- **`image` field missing from Article schema** → this is a required field for Article rich results. Google won't show the article card without it.
- **Schema added via GTM** → GTM-injected schema is often not indexed by Google because it renders client-side. Recommend server-side injection.
- **`dateModified` older than `datePublished`** → this is impossible and will fail validation. Flag and fix.
- **Multiple conflicting `@type` on same entity** → e.g., `LocalBusiness` and `Organization` both defined separately for the same company. Should be combined or one should extend the other.
- **Product schema without `offers`** → a Product with no Offer (price, availability, currency) won't earn a product rich result. Flag the missing Offer block.

---

## Output Artifacts

| When you ask for... | You get... |
|---------------------|------------|
| Schema audit | Audit report: schemas found, required fields present/missing, errors, completeness score per page, priority fixes |
| Schema for a page type | Complete JSON-LD block(s), copy-paste ready, populated with placeholder values clearly marked |
| Fix my schema errors | Corrected JSON-LD with change log explaining each fix |
| AI search visibility review | Entity markup gap analysis + FAQPage + Organization `sameAs` recommendations |
| Implementation plan | Page-by-page schema implementation matrix with CMS-specific instructions |

---

## Communication

All output follows the structured communication standard:
- **Bottom line first** — answer before explanation
- **What + Why + How** — every finding has all three
- **Actions have owners and deadlines** — no "we should consider"
- **Confidence tagging** — 🟢 verified (test passed) / 🟡 medium (valid but untested) / 🔴 assumed (needs verification)

---

## Related Skills

- **seo-audit**: For full technical and content SEO audit. Use seo-audit when the problem spans more than just structured data. NOT for schema-specific work — use schema-markup.
- **site-architecture**: For URL structure, internal linking, and navigation. Use when architecture is the root cause of SEO problems, not schema.
- **content-strategy**: For what content to create. Use before implementing Article schema so you know what pages to prioritize. NOT for the schema itself.
- **programmatic-seo**: For sites with thousands of pages that need schema at scale. Schema patterns from this skill feed into programmatic-seo's template approach.
