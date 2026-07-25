# Schema Markup Types Reference

JSON-LD structured data types, their status, and validation guidance. Updated for 2026.

## Active schema types (use these)

| Type | Use case | Rich result? | Priority |
|---|---|---|---|
| `Organization` | Company/brand identity | Knowledge panel | High — every site |
| `WebSite` | Site-level info + sitelinks search | Sitelinks searchbox | High — every site |
| `BreadcrumbList` | Navigation path | Breadcrumbs in SERPs | High — multi-level sites |
| `Article` / `NewsArticle` | Blog posts, news | Article cards, Top Stories | High — publishers |
| `Product` | Product pages | Price, availability, reviews | Critical — ecommerce |
| `FAQPage` | FAQ sections | Expandable FAQ in SERPs | Medium |
| `HowTo` | Step-by-step guides | Step-by-step cards | Medium |
| `LocalBusiness` | Physical businesses | Maps, hours, reviews | Critical — local |
| `Review` / `AggregateRating` | Reviews and ratings | Star ratings in SERPs | High — review sites |
| `Event` | Events with dates | Event cards | Medium — event sites |
| `VideoObject` | Video content | Video cards | Medium — video pages |
| `SoftwareApplication` | Apps/tools | App info in SERPs | Medium — SaaS |
| `Course` | Educational content | Course cards | Medium — edu sites |
| `Recipe` | Recipes | Recipe cards | High — food sites |
| `JobPosting` | Job listings | Job search integration | High — job sites |

## Deprecated / reduced (avoid or migrate)

| Type | Status | Since | Notes |
|---|---|---|---|
| `HowTo` | **Reduced visibility** | Aug 2023 | Still valid but rarely shown as rich result |
| `SpecialAnnouncement` | **Deprecated** | 2024 | Was for COVID; no longer processed |
| `QAPage` | **Reduced** | 2024 | Showing less frequently; prefer FAQPage |

## Validation checklist

For each schema type on the page:
- [ ] Valid JSON-LD (not Microdata or RDFa — JSON-LD preferred)
- [ ] Passes Google Rich Results Test
- [ ] No warnings in Search Console
- [ ] Required properties present (per schema.org spec)
- [ ] No fabricated reviews or ratings
- [ ] @type matches actual page content (no schema spam)
- [ ] Nested schemas properly connected (@id references)

## Common mistakes

- **Schema spam:** Adding Review schema to non-review pages
- **Self-serving reviews:** AggregateRating on your own product page without genuine reviews
- **Missing required fields:** Product without `offers`, Article without `author`
- **Stale data:** Event schema with past dates still active
- **Duplicate schemas:** Multiple Organization schemas on one page
