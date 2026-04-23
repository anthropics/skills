# Technical SEO — Full Audit Checklist

## Running a Site Audit in Semrush

1. Go to **Site Audit** → Create new project
2. Set crawl scope: full domain or specific subfolder
3. Set crawl limit (up to 100k pages on Pro)
4. Schedule: weekly recrawl recommended
5. After crawl: check the **Overview** dashboard for health score

---

## Priority Issue Categories

### 🔴 Critical (Errors) — Fix First

#### Crawlability
- [ ] Pages blocked by robots.txt (unintentionally)
- [ ] Noindex on important pages
- [ ] Broken internal links (404s)
- [ ] Redirect loops or chains (301 → 301 → 301)
- [ ] XML sitemap missing or not submitted

#### Performance (Core Web Vitals)
- [ ] LCP > 2.5s (Largest Contentful Paint) — fix: image optimization, server speed
- [ ] CLS > 0.1 (Cumulative Layout Shift) — fix: reserve space for images/ads
- [ ] INP > 200ms (Interaction to Next Paint) — fix: reduce JavaScript execution

#### Content Issues
- [ ] Duplicate content (same content on multiple URLs)
- [ ] Missing title tags
- [ ] Missing meta descriptions
- [ ] Duplicate title tags
- [ ] Very thin content (< 300 words on important pages)

### 🟡 Warnings — Fix Next

#### Internal Linking
- [ ] Pages with only 1 internal link (orphan-adjacent)
- [ ] Too many links on a single page (> 100)
- [ ] Broken anchor text (keyword-rich anchors are best)

#### Images
- [ ] Missing alt text
- [ ] Images not compressed (slow load)
- [ ] No next-gen format (WebP/AVIF)

#### HTTPS & Security
- [ ] Mixed content (HTTP resources on HTTPS pages)
- [ ] Invalid SSL certificate
- [ ] HTTP pages not redirecting to HTTPS

#### Structured Data
- [ ] Schema markup errors (validate at schema.org/validator)
- [ ] Missing schema for key page types (Article, Product, FAQ, LocalBusiness)

### 🔵 Notices — Nice to Fix

- Hreflang issues (for international sites)
- Long URLs (> 115 characters)
- Pagination issues (canonical vs rel=next/prev)
- AMP issues (if using AMP)

---

## Page Speed Optimization Quick Wins

| Issue | Solution | Impact |
|-------|---------|--------|
| Uncompressed images | Use TinyPNG or WebP | High |
| No browser caching | Set Cache-Control headers | Medium |
| Render-blocking JS | Defer/async scripts | High |
| No CDN | Add Cloudflare or similar | Medium-High |
| Slow server (TTFB > 600ms) | Upgrade hosting or use edge caching | High |

---

## Canonicalization Best Practices

- Every page should have a self-referencing canonical
- WWW vs non-WWW: pick one, redirect the other
- HTTP → HTTPS: 301 redirect all HTTP
- Trailing slash: be consistent (either always or never)
- Paginated content: use `rel="canonical"` to main page (or `rel="next/prev"`)

---

## Log File Analysis (Advanced)

Use **Log File Analyzer** tool to see:
- Which pages Googlebot crawls most
- Crawl frequency vs importance
- Wasted crawl budget (bot crawling 404s, duplicate URLs)

**Goal**: Get Googlebot to crawl your most important pages most often

---

## Monitoring After Fixes

- Re-run Site Audit weekly
- Track health score improvement over time
- Use **Sensor** tool to detect Google algorithm updates that may affect rankings
- Set up Position Tracking to see if technical fixes move rankings
