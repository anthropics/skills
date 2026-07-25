# URL Design Guide

URL structure by site type — with examples of what good and bad looks like in practice.

---

## Universal URL Rules

Before the site-specific patterns, these apply everywhere:

1. **Lowercase always** — `/Blog/SEO-Tips` and `/blog/seo-tips` are different URLs. Always lowercase.
2. **Hyphens, not underscores** — Google treats hyphens as word separators. Underscores join words. `/seo-tips` not `/seo_tips`.
3. **No special characters** — No `%`, `&`, `#`, `?` in the path itself.
4. **No trailing slash inconsistency** — Pick a convention (`/page` or `/page/`) and enforce it sitewide with redirects.
5. **No dates in URLs unless required** — `/blog/2024/03/seo-tips` ages poorly. `/blog/seo-tips` is evergreen.
6. **Stop words are usually fine** — `/how-to-write-cold-emails` is readable and fine. Don't obsessively remove "how", "to", "a", "the" unless the URL is very long.
7. **Keep them short** — Under 75 characters is a good target. Shorter is usually better.

---

## SaaS / B2B Software

### Recommended Structure

```
/ (homepage)
/features
/features/[feature-name]           e.g. /features/email-automation
/pricing
/solutions/[use-case]              e.g. /solutions/sales-teams
/solutions/[industry]              e.g. /solutions/healthcare
/integrations
/integrations/[tool-name]          e.g. /integrations/salesforce
/blog
/blog/[post-slug]                  e.g. /blog/cold-email-templates
/customers
/customers/[customer-name]         e.g. /customers/acme-corp
/about
/changelog
/docs                              (or subdomain: docs.example.com)
/docs/[topic]/[subtopic]
```

### What Works and What Doesn't

| ✅ Do | ❌ Don't |
|-------|----------|
| `/pricing` | `/pricing-plans` (redundant) |
| `/features/email-automation` | `/product/features/email-automation/detail` (too deep) |
| `/blog/cold-email-guide` | `/blog/articles/cold-email/complete-guide-to-cold-email` (too long) |
| `/solutions/sales-teams` | `/solutions-for-sales-teams` (ugly) |
| `/integrations/hubspot` | `/connect-with/hubspot-integration` |

### SaaS-Specific Notes

- `/features/` pages should actually be rankable landing pages, not just nav items.
- `/solutions/` by use case captures bottom-funnel searches ("sales team email tool").
- `/integrations/[tool]` pages are high-intent SEO goldmines — build a real page for each.
- Blog posts should live at `/blog/[slug]` — not `/resources/`, not `/learn/`, not `/content/`. Pick one.
- Changelog belongs at `/changelog` — some companies put it at `/releases` or `/updates`. Fine, just pick one.

---

## Blog / Content Site

### Recommended Structure

```
/ (homepage)
/[category]                        e.g. /seo, /email-marketing, /content
/[category]/[post-slug]            e.g. /seo/technical-seo-audit-checklist
/guides                            (optional hub for long-form guides)
/guides/[guide-slug]               e.g. /guides/cold-email-complete-guide
/tools                             (optional if you have free tools)
/tools/[tool-name]
/author/[author-slug]
/tag/[tag-name]                    (often better to noindex tags)
```

### What Works and What Doesn't

| ✅ Do | ❌ Don't |
|-------|----------|
| `/seo/keyword-research-guide` | `/seo/keyword-research/a-complete-guide-to-keyword-research-for-beginners-in-2024` |
| `/guides/cold-email` | `/blog/2024/03/15/cold-email-guide` |
| `/author/reza-rezvani` | `/author?id=42` |
| Flat category → post structure | 4-level nesting |

### Blog-Specific Notes

- Date-based URLs (`/2024/03/15/slug`) age poorly and look stale. Avoid.
- Tag pages create duplicate/thin content at scale. Either noindex them or give them real content.
- If you have <500 posts, flat `/post-slug` is fine. If you have >500, category buckets help organization.
- Author pages are worth building as real pages — they help E-E-A-T signals.

---

## E-Commerce

### Recommended Structure

```
/ (homepage)
/collections                       (or /shop, /catalog)
/collections/[category]            e.g. /collections/mens-shoes
/collections/[category]/[subcategory]   e.g. /collections/mens-shoes/running
/products/[product-slug]           e.g. /products/air-max-270-black
/brands/[brand-name]
/sale
/new-arrivals
/blog
/blog/[post-slug]
```

### What Works and What Doesn't

| ✅ Do | ❌ Don't |
|-------|----------|
| `/products/air-max-270-black` | `/products?id=89472&color=black&size=10` |
| `/collections/mens-shoes` | `/products/shoes/men/athletic/running/all-styles` |
| Canonical on variant pages | Let `?color=red&size=10` create duplicate URLs |

### E-Commerce-Specific Notes

- Product variant pages (size, color) are the biggest duplicate content risk in e-commerce. Use canonical tags pointing to the base product URL, or use URL parameters and configure them in GSC.
- Filter and sort pages (`?sort=price-asc&brand=nike`) should either be canonicalized or blocked.
- Collection/category pages need real content to rank — not just a product grid.
- Discontinued products: don't just delete them. 301 to closest alternative or return 410 with a helpful message.

---

## Local Business / Service Area

### Recommended Structure (Single Location)

```
/ (homepage)
/services
/services/[service-name]           e.g. /services/plumbing-repair
/about
/contact
/blog
/blog/[post-slug]
/areas-served                      (optional hub for service area pages)
/areas-served/[city-name]          e.g. /areas-served/brooklyn
```

### Recommended Structure (Multi-Location)

```
/ (homepage)
/locations
/locations/[city]                  e.g. /locations/new-york
/locations/[city]/[service]        e.g. /locations/new-york/plumbing
/services/[service-name]           (generic service pages)
```

### Local-Specific Notes

- City/location pages must have unique, locally relevant content — not just "Find our [service] in [city]" copy-pasted 47 times.
- `/areas-served/brooklyn` should have real information about serving Brooklyn, not a thin page.
- Multi-location sites: `/locations/[city]` works better than subdomain per city for smaller operations. Subdomains make sense for truly independent franchises.

---

## URL Redirect Mapping (When Restructuring)

If you're changing URLs, you need a 301 redirect map. Every old URL → new URL. No exceptions.

**Redirect mapping process:**
1. Export all indexed URLs from Google Search Console (Crawl → Coverage → All)
2. Export all inbound links to your site (use Ahrefs, Semrush, or GSC)
3. Map old → new for every URL that has inbound links or search traffic
4. Implement 301 redirects server-side (not JS redirects, not meta refresh)
5. Monitor in GSC for 404 errors after migration
6. Update internal links — don't just redirect, fix the source links

**Priority redirect tiers:**
- **Tier 1:** Pages with significant inbound external links — redirect these first
- **Tier 2:** Pages with significant organic traffic — redirect to preserve equity
- **Tier 3:** Pages with neither — still redirect, but lower urgency

**Never:**
- Chain redirects more than 1 hop (`/old` → `/temp` → `/new` wastes equity)
- 302 redirect something that's a permanent move (use 301)
- Leave old URLs live as duplicates without canonicals

---

## Canonicalization

When the same content is accessible at multiple URLs, tell Google which one is canonical.

```html
<link rel="canonical" href="https://example.com/the-canonical-url" />
```

Common scenarios requiring canonicals:
- `http://` vs `https://` — canonical should always be `https://`
- `www` vs non-www — pick one, canonical + 301 the other
- Trailing slash vs no trailing slash — `/page` and `/page/` are different URLs to Google
- Filtered/sorted product pages — canonical to base product/collection URL
- Paginated pages — canonical the first page (or use `rel=next`/`rel=prev`)
- Printer-friendly versions — canonical to main page
- Syndicated content — canonical to original source

---

## HTTP Status Code Reference

| Code | Meaning | Use |
|------|---------|-----|
| 200 | OK | Normal page |
| 301 | Moved Permanently | URL changed permanently — passes equity |
| 302 | Found (Temporary) | Temporary redirect — does NOT pass equity |
| 404 | Not Found | Page doesn't exist — configure a helpful 404 page |
| 410 | Gone | Page intentionally removed — Google deindexes faster than 404 |
| 503 | Service Unavailable | Maintenance mode — tell Google to come back later |

Use 301, not 302, for all permanent URL changes.
