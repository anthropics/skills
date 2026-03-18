# Programmatic SEO — Build SEO Pages at Scale

## What is Programmatic SEO?

Programmatic SEO = creating hundreds or thousands of SEO-optimized pages from templates + data, rather than writing each manually.

**Examples:**
- Yelp: one page per "[business type] in [city]" — millions of pages
- Zapier: "[App A] + [App B] integration" — 50,000+ pages
- NomadList: "Cost of living in [city]" — one template, 1,000+ cities
- G2: "[Software] reviews and pricing" — one template per product

---

## When to Use Programmatic SEO

✅ Good fit:
- You have structured data (locations, products, categories, comparisons)
- There are repetitive search patterns at scale ("X in Y", "X vs Y", "best X for Y")
- Each combination has unique search intent and real search volume
- You can provide genuine value at scale (not just template-spun thin content)

❌ Bad fit:
- Your topic doesn't have scalable patterns
- You can't provide unique value per page
- You're trying to game rankings with thin content (Google penalizes this)

---

## Step-by-Step Programmatic SEO Workflow

### Step 1: Find Your Scalable Pattern
Use **Keyword Magic Tool** to identify patterns:
- Filter by: same modifier + variable format
- Example: "SEO tools for [industry]" → lawyers, dentists, restaurants, etc.
- Look for: consistent volume across variables, low competition

Patterns to look for:
- `[service] in [location]`
- `[product] for [use case]`
- `[brand A] vs [brand B]`
- `best [category] for [persona]`
- `how to [verb] [noun]`
- `[noun] alternatives`
- `[noun] pricing`

### Step 2: Validate Demand
For each pattern, check:
1. **Keyword Overview**: Does each variable have real volume? (even 50/mo is fine × 500 pages)
2. **SERP analysis**: Are current results satisfying the query, or is there a gap?
3. **Competition**: Can you realistically rank? Check domain authority of current results.

### Step 3: Build Your Data Source
Options:
- Internal database (product catalog, locations, job listings)
- Public datasets (census data, government data, APIs)
- Manually curated structured data (CSV/spreadsheet)
- Third-party API (weather, finance, sports, etc.)

Data fields needed per page:
- Primary variable (city name, product name, etc.)
- Supporting data (stats, descriptions, unique facts)
- Structured metadata (title, meta description templates)

### Step 4: Design Your Template

**Template anatomy:**
```
H1: [Primary keyword with variable]
Intro: [2-3 sentences contextualizing the variable]
Data section: [Unique data pulled from your source]
Comparison/List: [Related entities or options]
FAQ: [3-5 questions targeting PAA patterns]
CTA: [Relevant next step]
Internal links: [Related pages in the same cluster]
```

**Rules for non-thin content:**
- Minimum 300 words of unique content per page
- At least 3 data points unique to that variable
- Genuine utility — answer the question completely
- Avoid copy-paste with only the variable swapped

### Step 5: Internal Linking at Scale
- Hub page → links to all variable pages
- Each variable page → links to hub + related variables
- Breadcrumb navigation (Location > State > City)
- Avoid orphan pages (every page must have ≥ 2 inbound internal links)

### Step 6: Technical Setup
Critical for programmatic SEO at scale:

**URL structure:**
- Clean, descriptive: `/seo-tools/dentists/` not `/tools?id=43&cat=2`
- Consistent pattern across all pages
- Max 3 levels deep recommended

**Indexing control:**
- Use `robots.txt` to block pages during development
- Submit sitemap with all target URLs after launch
- Monitor Google Search Console for indexing rate
- Canonicalize similar pages if needed

**Page speed:**
- Programmatic pages are often slow (database queries) — optimize
- Use CDN/edge caching
- Pregenerate (SSG) if possible rather than SSR

### Step 7: Monitor Performance
- **Position Tracking**: Sample 20-30 representative pages across variables
- **Google Search Console**: Filter by URL pattern to see index rate
- **Traffic Analytics**: Watch for traffic growth as pages index
- Use **Site Audit** monthly to catch thin content flags or duplicate issues

---

## Schema Markup for Programmatic Pages

Apply appropriate schema to every page type:

| Page Type | Schema |
|-----------|--------|
| Location pages | `LocalBusiness`, `Place` |
| Product pages | `Product`, `AggregateRating` |
| Comparison pages | `ItemList`, `FAQPage` |
| Review pages | `Review`, `AggregateRating` |
| How-to pages | `HowTo` |
| FAQ sections | `FAQPage` |

---

## Avoiding Thin Content Penalties

Google's "helpful content" system targets programmatic pages specifically.

**Safe signals:**
- Real data unique to each page (not just variable name swap)
- User engagement (time on page, low bounce rate)
- Editorial mentions or backlinks to individual pages
- Pages that answer follow-up questions, not just the head query

**Red flags:**
- Identical structure with only variable name changed
- No data beyond what's in the template
- High page count, low traffic per page
- No backlinks to any individual pages

---

## Scale Benchmarks

| Pages | Management Approach |
|-------|-------------------|
| < 100 | Manual review + publish |
| 100–1,000 | CMS + spreadsheet data source |
| 1,000–10,000 | Headless CMS + database |
| 10,000+ | Custom build + automated QA |
