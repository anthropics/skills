# Schema Types Guide

A practitioner's reference for schema.org types — what they do, what fields matter, and what Google actually uses for rich results.

---

## How to Read This Guide

Each type lists:
- **Purpose** — what it tells search engines
- **Rich result** — what you can earn in Google (if anything)
- **Required fields** — missing these = no rich result
- **Recommended fields** — fill these to maximize eligibility
- **Gotchas** — the field mistakes that waste everyone's time

---

## Article

**Purpose:** Marks editorial content — news, blog posts, opinion pieces.

**Rich result:** Article rich result (expanded card in Google News, Discover, and some search results). Also influences AI Overview citation likelihood.

**Required fields:**
- `headline` — the article title (max 110 characters for display)
- `image` — at least one image, minimum 1200px wide for rich results
- `datePublished` — ISO 8601 format
- `author` — Person or Organization type

**Recommended fields:**
- `dateModified` — keep current; freshness signal
- `publisher` — Organization type with `logo`
- `description` — 150-300 char summary
- `url` — canonical URL of the article

**Subtypes:** Use `NewsArticle` for news content, `BlogPosting` for blog posts. Both inherit from Article. Google treats them similarly.

**Gotchas:**
- `image` must be absolute URL. Relative URLs fail silently.
- `headline` should match the visible `<h1>` on the page. Google cross-validates.
- Multiple `author` values are valid — use an array: `"author": [{"@type": "Person", "name": "..."}, ...]`

---

## HowTo

**Purpose:** Step-by-step instructions for completing a task.

**Rich result:** HowTo steps appear directly in Google search results as expandable steps (desktop and mobile).

**Required fields:**
- `name` — title of the how-to (e.g., "How to change a bike tire")
- `step` — array of HowToStep objects, each with:
  - `name` — step title
  - `text` — step instructions

**Recommended fields:**
- `image` — overall how-to image
- `totalTime` — ISO 8601 duration (e.g., `"PT30M"` = 30 minutes)
- `tool` — list of tools needed (HowToTool type)
- `supply` — list of materials (HowToSupply type)
- `estimatedCost` — MonetaryAmount type

**Gotchas:**
- Steps must appear on the page in readable form — hidden steps fail Google's content matching.
- HowToStep `image` is different from the main `image` — each step can have its own.
- Don't use HowTo for recipe content — use Recipe type instead.

---

## FAQPage

**Purpose:** A page containing a list of frequently asked questions and their answers.

**Rich result:** FAQ accordion dropdowns directly in Google search results. High-value visibility — shows your Q&A without clicking.

**Required fields:**
- `mainEntity` — array of Question objects, each with:
  - `name` — the question text
  - `acceptedAnswer` — Answer type with `text` field containing the answer

**Recommended fields:**
- No additional fields required — this type is simple by design.

**Gotchas:**
- Both the question AND the answer must be visible on the page. Google explicitly checks.
- Answers with HTML tags (links, bold) may or may not render — keep answers as clean text.
- Google limits FAQ rich results to 3-5 Q&A pairs visible in search, even if you have more.
- Don't use FAQPage for Q&A that requires a login to view — Google can't verify it.

---

## Product

**Purpose:** Describes a product for sale, including pricing, availability, and reviews.

**Rich result:** Product rich results with price, availability, rating stars. Eligible for Google Shopping surfaces.

**Required fields (for rich results):**
- `name` — product name
- `offers` — Offer type with:
  - `price` — numeric price (not formatted with currency symbol)
  - `priceCurrency` — ISO 4217 currency code (e.g., `"USD"`, `"EUR"`)
  - `availability` — schema.org availability URL (e.g., `"https://schema.org/InStock"`)

**Recommended fields:**
- `image` — product image(s), absolute URLs
- `description` — product description
- `sku` — stock-keeping unit
- `brand` — Brand or Organization type
- `aggregateRating` — AggregateRating type (required for star ratings)
- `review` — individual Review objects

**AggregateRating required fields:**
- `ratingValue` — average rating
- `reviewCount` — number of reviews (or `ratingCount`)
- `bestRating` — maximum rating value (default: 5)

**Gotchas:**
- Price must be a number, not a string: `"price": 29.99` not `"price": "$29.99"`
- `availability` must use the full schema.org URL, not just "InStock"
- If you show ratings, you must have real reviews — fabricated ratings violate Google's policies
- Price shown in schema must match the price visible on the page

---

## Organization

**Purpose:** Identifies your company/organization as an entity to search engines and knowledge graphs.

**Rich result:** Knowledge panel information, logo in search results, organization entity recognition.

**Required fields:**
- `name` — official organization name
- `url` — organization website

**Recommended fields:**
- `logo` — ImageObject with absolute URL to logo
- `sameAs` — array of URLs to your organization's profiles elsewhere (LinkedIn, Twitter/X, Facebook, Crunchbase, Wikidata, Wikipedia)
- `contactPoint` — ContactPoint type with `telephone` and `contactType`
- `address` — PostalAddress type
- `foundingDate` — year or ISO date
- `numberOfEmployees` — QuantitativeValue type
- `description` — brief company description

**Gotchas:**
- `sameAs` is the most important field for entity establishment — the more authoritative sources you include, the stronger the entity signal.
- Use `https://www.wikidata.org/wiki/Q[ID]` in `sameAs` if your company has a Wikidata entry.
- Only one Organization schema per domain — put it on every page if you want, but keep it consistent.

---

## LocalBusiness

**Purpose:** Extends Organization for businesses with a physical location. Used for local search results and map listings.

**Rich result:** Local knowledge panel, map pin details, opening hours, star ratings in local results.

**Required fields:**
- `name` — business name
- `address` — PostalAddress with `streetAddress`, `addressLocality`, `postalCode`, `addressCountry`

**Recommended fields:**
- `telephone` — with country code (e.g., `"+1-800-555-1234"`)
- `openingHoursSpecification` — array by day with opens/closes times
- `geo` — GeoCoordinates with `latitude` and `longitude`
- `priceRange` — string like `"$$"` or `"€€"` or `"$10-$50"`
- `image` — photos of the business
- `url` — website URL
- `aggregateRating` — if you have reviews

**Subtypes:** Use the most specific subtype available. `Restaurant`, `MedicalClinic`, `LegalService`, `Hotel` all extend LocalBusiness and unlock additional rich result fields.

**Gotchas:**
- Address must exactly match what's in Google Business Profile for local SEO to connect.
- Hours must use 24-hour format in `openingHoursSpecification`.
- If closed on a day, omit that day rather than using `"00:00"`.

---

## BreadcrumbList

**Purpose:** Represents the breadcrumb trail shown on a page — the hierarchy from homepage to current page.

**Rich result:** Breadcrumb path shown in Google search results instead of the raw URL. Cleaner appearance, more clicks.

**Required fields:**
- `itemListElement` — array of ListItem objects, each with:
  - `position` — integer starting at 1
  - `name` — breadcrumb label
  - `item` — absolute URL of that breadcrumb level

**Recommended fields:**
None required beyond the above.

**Gotchas:**
- Positions must be sequential integers starting at 1. Gaps or non-integers fail validation.
- The last breadcrumb (current page) may omit `item` since it's the current URL — but including it is safer.
- Breadcrumb schema must match the visible breadcrumbs on the page.
- Use on every non-homepage if you have visible breadcrumbs.

---

## VideoObject

**Purpose:** Describes an embedded or hosted video.

**Rich result:** Video carousels, video badges on search results, timestamp markers that appear in results.

**Required fields:**
- `name` — video title
- `description` — video description
- `thumbnailUrl` — absolute URL to thumbnail image
- `uploadDate` — ISO 8601 date

**Recommended fields:**
- `duration` — ISO 8601 duration (e.g., `"PT12M30S"` = 12 min 30 sec)
- `contentUrl` — direct URL to the video file
- `embedUrl` — URL of the embeddable player
- `hasPart` — array of Clip objects with start/end times for key moments
- `interactionStatistic` — view count (InteractionCounter type)

**Key moments (Clip type for timestamp markers):**
```json
"hasPart": [
  {
    "@type": "Clip",
    "name": "Introduction",
    "startOffset": 0,
    "endOffset": 60,
    "url": "https://example.com/video#t=0"
  }
]
```

**Gotchas:**
- `thumbnailUrl` must resolve to an actual image — Google checks it.
- Without `contentUrl` or `embedUrl`, Google may not index the video.
- Videos behind login/paywall are not eligible for video rich results.

---

## WebSite

**Purpose:** Identifies your website and enables the sitelinks search box in Google results.

**Rich result:** Sitelinks search box — a search field that appears under your domain in branded searches.

**Required fields:**
- `url` — homepage URL
- `potentialAction` — SearchAction type for sitelinks search box:
  ```json
  "potentialAction": {
    "@type": "SearchAction",
    "target": {
      "@type": "EntryPoint",
      "urlTemplate": "https://example.com/search?q={search_term_string}"
    },
    "query-input": "required name=search_term_string"
  }
  ```

**Gotchas:**
- Only put WebSite schema on the homepage.
- The `urlTemplate` must point to a working search endpoint.
- Sitelinks search box only appears for branded queries — this won't help you rank for generic terms.

---

## Schema Eligibility Summary

Quick-reference: what actually earns a rich result vs what's just entity data.

| Schema Type | Rich Result Available | Rich Result Type |
|-------------|----------------------|-----------------|
| Article | ✅ | Top stories card, article rich result |
| HowTo | ✅ | Step-by-step in SERP |
| FAQPage | ✅ | Accordion Q&A in SERP |
| Product + Offer | ✅ | Price/availability badge |
| Product + AggregateRating | ✅ | Star ratings |
| LocalBusiness | ✅ | Local knowledge panel |
| BreadcrumbList | ✅ | Breadcrumb path in SERP |
| VideoObject | ✅ | Video carousel, key moments |
| Organization | ⚠️ | Knowledge panel (not guaranteed) |
| WebSite | ⚠️ | Sitelinks search box (not guaranteed) |
