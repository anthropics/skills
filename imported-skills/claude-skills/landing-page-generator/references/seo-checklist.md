# Landing Page SEO Checklist

## Overview

This checklist ensures landing pages are optimized for search engine visibility while maintaining conversion focus. Apply these checks before launching any landing page.

## Meta Tags

- [ ] **Title tag**: Under 60 characters, includes primary keyword, ends with brand name
- [ ] **Meta description**: 150-160 characters, includes CTA language, unique per page
- [ ] **Canonical URL**: Set to prevent duplicate content issues
- [ ] **Robots meta**: Ensure page is indexable (`index, follow`) unless intentionally noindex
- [ ] **Open Graph tags**: og:title, og:description, og:image, og:url for social sharing
- [ ] **Twitter Card tags**: twitter:card, twitter:title, twitter:description, twitter:image
- [ ] **Viewport meta**: `<meta name="viewport" content="width=device-width, initial-scale=1">`

## Structured Data

- [ ] **Organization schema**: Company name, logo, social profiles
- [ ] **Product schema**: Name, description, price, availability (for product pages)
- [ ] **FAQ schema**: For pages with FAQ sections (rich snippet opportunity)
- [ ] **Breadcrumb schema**: Navigation path for deep pages
- [ ] **Review schema**: Aggregate rating if testimonials present (use carefully per guidelines)
- [ ] **Validate**: Test all structured data with Google Rich Results Test

## Core Web Vitals Targets

### Largest Contentful Paint (LCP) - Target: < 2.5s
- [ ] Optimize hero image (WebP format, proper dimensions)
- [ ] Preload critical resources (`<link rel="preload">`)
- [ ] Use CDN for static assets
- [ ] Minimize render-blocking CSS and JavaScript

### First Input Delay (FID) / Interaction to Next Paint (INP) - Target: < 200ms
- [ ] Defer non-critical JavaScript
- [ ] Break up long tasks (>50ms)
- [ ] Minimize third-party script impact
- [ ] Use `requestAnimationFrame` for visual updates

### Cumulative Layout Shift (CLS) - Target: < 0.1
- [ ] Set explicit width/height on images and videos
- [ ] Reserve space for dynamic content (ads, embeds)
- [ ] Use `font-display: swap` for web fonts
- [ ] Avoid inserting content above existing content

## Keyword Placement

- [ ] **H1 tag**: Contains primary keyword, one per page only
- [ ] **H2 tags**: Include secondary keywords naturally
- [ ] **First paragraph**: Primary keyword appears in first 100 words
- [ ] **Body copy**: Natural keyword density (1-2%), no stuffing
- [ ] **Image alt text**: Descriptive, includes keyword where relevant
- [ ] **URL slug**: Short, keyword-rich, hyphen-separated
- [ ] **CTA text**: Consider keyword inclusion where natural

## Internal Linking

- [ ] Link to relevant product/feature pages
- [ ] Link to blog content that supports the page topic
- [ ] Use descriptive anchor text (not "click here")
- [ ] Ensure landing page is linked from main navigation or sitemap
- [ ] Link to pricing page if applicable
- [ ] Limit links to avoid diluting page authority (15-20 max)

## Image Optimization

- [ ] **Format**: Use WebP with JPEG/PNG fallback
- [ ] **Compression**: Lossy compression for photos, lossless for graphics
- [ ] **Dimensions**: Serve at exact display size (no CSS resizing)
- [ ] **Alt text**: Descriptive, 125 characters max, natural keyword inclusion
- [ ] **File names**: Descriptive, hyphenated (e.g., `product-dashboard-screenshot.webp`)
- [ ] **Lazy loading**: Apply to images below the fold (`loading="lazy"`)
- [ ] **Responsive images**: Use `srcset` for different viewport sizes

## Canonical URLs

- [ ] Self-referencing canonical on every page
- [ ] Consistent protocol (https) and trailing slash usage
- [ ] Canonical points to preferred URL version (www vs non-www)
- [ ] UTM parameters excluded from canonical URL
- [ ] Pagination handled with rel="next"/"prev" or single-page canonical

## Mobile Responsiveness

- [ ] **Mobile-friendly test**: Pass Google Mobile-Friendly Test
- [ ] **Touch targets**: Minimum 44x44px, 8px spacing between targets
- [ ] **Font size**: Minimum 16px base font, no pinch-to-zoom needed
- [ ] **Content parity**: All critical content accessible on mobile
- [ ] **Horizontal scroll**: None present at any viewport width
- [ ] **Form usability**: Appropriate input types (email, tel), autocomplete attributes
- [ ] **Media queries**: Breakpoints at 480px, 768px, 1024px, 1200px minimum

## Technical SEO

- [ ] **HTTPS**: SSL certificate valid and active
- [ ] **Page speed**: < 3s load time on mobile (test with PageSpeed Insights)
- [ ] **XML sitemap**: Page included in sitemap.xml
- [ ] **Robots.txt**: Page not blocked by robots.txt
- [ ] **404 handling**: Custom 404 page with navigation
- [ ] **Redirect chains**: No more than 1 redirect hop
- [ ] **Hreflang**: Set for multi-language landing pages

## Content Quality Signals

- [ ] **Unique content**: No duplicate content from other pages
- [ ] **Content depth**: Sufficient content for topic coverage (500+ words for SEO pages)
- [ ] **Readability**: Grade level 6-8 for broad audiences
- [ ] **Freshness**: Last modified date reflects recent updates
- [ ] **E-E-A-T signals**: Author expertise, company authority, trust indicators
