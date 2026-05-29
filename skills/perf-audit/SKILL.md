---
name: perf-audit
description: Run a comprehensive performance audit on a Next.js web application. Use when asked to "test speed", "check performance", "run lighthouse", "audit performance", or "speed test". Measures FCP, LCP, CLS, TTFB, bundle size, and Lighthouse scores across all pages.
---

# Performance Audit Skill

Run a comprehensive performance audit on the current web application.
Target: $ARGUMENTS (defaults to "full" if not specified).

## Targets

- `full` (default) — All pages, interactions, Lighthouse, and bundle analysis
- `pages` — Page load metrics only (public + authenticated)
- `lighthouse` — Lighthouse detailed audit
- `interactions` — UI interaction timing
- `bundle` — Bundle size analysis only
- `vitals` — Core Web Vitals summary

## Prerequisites

1. The project must be a Next.js application
2. Playwright must be installed (`npx playwright install chromium`)
3. For authenticated pages, test credentials in `.env.local`:
   ```
   TEST_USER_EMAIL=<email>
   TEST_USER_PASSWORD=<password>
   ```

If missing, tell the user to set them up before running the audit.

## Workflow

### 1. Discover Application Routes

Before auditing, scan the project to discover all routes:

- Read the `app/` directory structure to find all pages (look for `page.tsx` or `page.js` files)
- Identify public vs. authenticated routes (check for auth middleware, layout auth checks)
- Identify detail/dynamic routes (e.g., `/projects/[id]`)
- Check for sidebar or navigation components to find all user-facing pages
- Group routes into: public pages, authenticated pages, detail pages

### 2. Page Load Audit (Playwright)

For each discovered route, use Playwright to measure performance metrics.

Create a temporary script or run inline:

```javascript
const { chromium } = require('playwright');

const browser = await chromium.launch({ headless: true });
const context = await browser.newContext();
const page = await context.newPage();

// For authenticated routes, log in first
// Find the login page and fill credentials from env vars

await page.goto(url, { waitUntil: 'networkidle' });

const metrics = await page.evaluate(() => {
  const nav = performance.getEntriesByType('navigation')[0];
  const paint = performance.getEntriesByType('paint');
  const fcp = paint.find(e => e.name === 'first-contentful-paint');
  const lcp = new Promise(resolve => {
    new PerformanceObserver(list => {
      const entries = list.getEntries();
      resolve(entries[entries.length - 1].startTime);
    }).observe({ type: 'largest-contentful-paint', buffered: true });
  });
  const resources = performance.getEntriesByType('resource');

  return {
    ttfb: nav.responseStart - nav.requestStart,
    fcp: fcp?.startTime,
    domCount: document.querySelectorAll('*').length,
    resourceCount: resources.length,
    transferSize: resources.reduce((s, r) => s + (r.transferSize || 0), 0),
    jsBytes: resources.filter(r => r.initiatorType === 'script').reduce((s, r) => s + (r.transferSize || 0), 0),
    cssBytes: resources.filter(r => r.initiatorType === 'link' || r.initiatorType === 'style').reduce((s, r) => s + (r.transferSize || 0), 0),
    imageBytes: resources.filter(r => r.initiatorType === 'img').reduce((s, r) => s + (r.transferSize || 0), 0),
  };
});
```

For **authenticated routes**:
1. Navigate to the login page
2. Fill in `TEST_USER_EMAIL` and `TEST_USER_PASSWORD` from environment
3. Submit the form and wait for redirect
4. Then navigate to each authenticated route using the same browser context

### 3. Lighthouse Audit

Run Lighthouse CLI on each page:

```bash
npx lighthouse <url> --output=json --output-path=./lighthouse-report.json \
  --chrome-flags="--headless --no-sandbox" \
  --only-categories=performance,accessibility,best-practices,seo
```

For authenticated pages, extract cookies from the Playwright session and pass via `--extra-headers`:

```bash
npx lighthouse <url> --output=json --output-path=./lighthouse-report.json \
  --chrome-flags="--headless --no-sandbox" \
  --extra-headers='{"Cookie": "<session-cookies>"}' \
  --only-categories=performance,accessibility,best-practices,seo
```

Parse the JSON output to extract category scores.

Note: Lighthouse may exit with code 1 on Windows due to Chrome temp dir cleanup — this is harmless. Check that the JSON report was written successfully.

If any authenticated page shows redirect to login, the auth cookies may have expired. Re-authenticate and retry.

### 4. Bundle Size Analysis

Run Next.js build with webpack bundle analyzer:

```bash
ANALYZE=true npx next build
```

Then list the top JS chunks by size from `.next/static/chunks/`:

```bash
node -e "
const fs = require('fs');
const path = require('path');
function walk(dir) {
  let r = [];
  for (const item of fs.readdirSync(dir)) {
    const full = path.join(dir, item);
    const stat = fs.statSync(full);
    if (stat.isDirectory()) r = r.concat(walk(full));
    else if (item.endsWith('.js')) r.push({ name: item, size: stat.size });
  }
  return r;
}
const files = walk('.next/static/chunks').sort((a,b) => b.size - a.size);
let total = 0;
files.forEach(f => total += f.size);
console.log('Top 10 chunks:');
files.slice(0,10).forEach(f => console.log('  ' + (f.size/1024).toFixed(0) + ' kB  ' + f.name));
console.log('Total: ' + (total/1024).toFixed(0) + ' kB (' + files.length + ' chunks)');
"
```

### 5. Core Web Vitals

Check for `@vercel/speed-insights` or `web-vitals` in `package.json` dependencies.

If the app is deployed, remind the user to check real-user metrics in their hosting provider's dashboard (Vercel Speed Insights, Google Search Console, etc.).

### 6. Interaction Timing (if target is `full` or `interactions`)

Test common UI interactions:

- **Command palette / search**: Measure time from keyboard shortcut (Cmd+K / Ctrl+K) to visible
- **Modal / dialog opening**: Measure time from click to fully rendered
- **Navigation transitions**: Measure sidebar link click to new page content visible
- **Form submissions**: Measure submit to response

Use Playwright's timing APIs:
```javascript
const start = Date.now();
await page.keyboard.press('Control+k');
await page.waitForSelector('[data-command-palette]', { state: 'visible' });
const duration = Date.now() - start;
```

### 7. Comparison with Previous Run

If a previous results file exists (e.g., `perf-audit-results.json`), load it and compare:

- Flag regressions (metrics that got worse by >10%)
- Highlight improvements
- Show delta for each metric

Save current results for future comparison.

## Summary Report

Present a comprehensive summary covering:

1. **Page Metrics Table** — All pages with FCP, LCP, CLS, TTFB, DOM count, transfer size
2. **Lighthouse Scores** — Performance, Accessibility, Best Practices, SEO per page
3. **Bundle Sizes** — Total JS, top 10 chunks
4. **Interaction Timing** — Command palette, modals, navigation transitions
5. **Threshold Checks** — Flag any page exceeding:
   - LCP > 2.5s
   - FCP > 1.8s
   - CLS > 0.1
   - TTFB > 800ms
6. **Regressions** — Compare with previous run if available
7. **Recommendations** — Suggest specific fixes for any failing metrics
