# Core Web Vitals Thresholds (2026)

Reference for `seo_health_scorer.py` and the Performance category. Updated per Google's CrUX methodology.

## The three metrics

| Metric | Good | Needs Improvement | Poor | What it measures |
|---|---|---|---|---|
| **LCP** (Largest Contentful Paint) | ≤ 2.5s | 2.5s – 4.0s | > 4.0s | Loading speed — when the main content is visible |
| **CLS** (Cumulative Layout Shift) | ≤ 0.1 | 0.1 – 0.25 | > 0.25 | Visual stability — unexpected layout jumps |
| **INP** (Interaction to Next Paint) | ≤ 200ms | 200ms – 500ms | > 500ms | Responsiveness — delay after user interaction |

## Scoring mapping

```
pass = metric in "Good" range
warn = metric in "Needs Improvement" range
fail = metric in "Poor" range
```

## Common fixes by metric

### LCP > 2.5s
- Optimize largest image (WebP/AVIF, proper sizing, preload)
- Reduce server response time (TTFB < 800ms)
- Remove render-blocking CSS/JS
- Use CDN for static assets

### CLS > 0.1
- Set explicit width/height on images and video
- Reserve space for ads/embeds before load
- Avoid inserting content above the fold after page load
- Use `font-display: swap` for web fonts

### INP > 200ms
- Break up long tasks (> 50ms) into smaller chunks
- Defer non-critical JavaScript
- Use `requestIdleCallback` for low-priority work
- Minimize main-thread blocking from third-party scripts

## Measurement sources

- **Field data:** CrUX (Chrome User Experience Report) — 28-day rolling p75
- **Lab data:** Lighthouse, PageSpeed Insights — synthetic, not real users
- **Monitoring:** web-vitals.js library for RUM (Real User Monitoring)

Field data (CrUX) is what Google uses for ranking signals. Lab data helps debug but doesn't directly affect rankings.
