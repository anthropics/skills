---
name: playwright-scraper
description: Web scraping with Playwright for dynamic content, authentication flows, pagination, data extraction, and screenshots. Handles JavaScript-rendered sites that simpler tools can't reach.
license: Apache-2.0
---

# Playwright Scraper

Web scraping skill using Playwright browser automation. Handles dynamic JavaScript-rendered content, authentication flows, multi-page pagination, structured data extraction, and screenshot capture.

## When to Use

Use this skill when you need to scrape sites with:
- JavaScript-rendered content (React, Angular, Vue apps)
- Login-protected pages (dashboards, admin panels)
- Paginated results (search results, product listings)
- Dynamic content that loads on scroll or interaction
- Visual capture needs (screenshots, PDFs)

**Don't use** for static HTML — simpler tools like `curl` or `requests` are faster.

## Decision Tree

```
Need to scrape a site?
├── Static HTML (view-source shows the data) → Use curl/fetch, not this skill
└── Dynamic/JS-rendered → Use Playwright
    ├── Requires login? → Handle auth flow first (see below)
    ├── Multiple pages? → Use pagination pattern (see below)
    └── Single page extraction → Navigate + extract
```

## Core Patterns

### 1. Basic Page Extraction

```javascript
const browser = await playwright.chromium.launch({ headless: true });
const page = await browser.newPage();
await page.goto('https://example.com', { waitUntil: 'networkidle' });

const data = await page.evaluate(() => {
  return Array.from(document.querySelectorAll('.item')).map(el => ({
    title: el.querySelector('h2')?.innerText,
    link: el.querySelector('a')?.href,
    description: el.querySelector('p')?.innerText
  }));
});

console.log(JSON.stringify(data, null, 2));
await browser.close();
```

### 2. Authenticated Scraping

```javascript
const browser = await playwright.chromium.launch();
const page = await browser.newPage();

// Navigate to login
await page.goto('https://dashboard.example.com/login');
await page.fill('#username', process.env.USERNAME);
await page.fill('#password', process.env.PASSWORD);
await page.click('#submit');

// Wait for redirect to dashboard
await page.waitForURL('**/dashboard**');

// Now scrape the authenticated content
const data = await page.evaluate(() =>
  document.querySelector('#dashboard-data').innerText
);

await browser.close();
```

### 3. Pagination

```javascript
const browser = await playwright.chromium.launch();
const page = await browser.newPage();
await page.goto('https://search.example.com?q=query');

let allItems = [];
let pageNum = 1;

while (true) {
  // Extract current page
  const items = await page.$$eval('.result-item', elements =>
    elements.map(el => ({
      title: el.querySelector('.title')?.innerText,
      url: el.querySelector('a')?.href
    }))
  );
  allItems.push(...items);
  console.log(`Page ${pageNum}: ${items.length} items`);

  // Try to go to next page
  const nextButton = await page.$('.next-page:not([disabled])');
  if (!nextButton) break;

  await nextButton.click();
  await page.waitForLoadState('networkidle');
  pageNum++;
}

console.log(`Total: ${allItems.length} items`);
await browser.close();
```

### 4. Infinite Scroll

```javascript
const browser = await playwright.chromium.launch();
const page = await browser.newPage();
await page.goto('https://feed.example.com');

let previousHeight = 0;
let scrollAttempts = 0;
const maxScrolls = 10;

while (scrollAttempts < maxScrolls) {
  await page.evaluate(() => window.scrollTo(0, document.body.scrollHeight));
  await page.waitForTimeout(2000);

  const currentHeight = await page.evaluate(() => document.body.scrollHeight);
  if (currentHeight === previousHeight) break;

  previousHeight = currentHeight;
  scrollAttempts++;
}

const items = await page.$$eval('.feed-item', els =>
  els.map(el => el.innerText)
);
await browser.close();
```

### 5. Screenshot & PDF Capture

```javascript
const browser = await playwright.chromium.launch();
const page = await browser.newPage();
await page.goto('https://example.com');

// Viewport screenshot
await page.screenshot({ path: 'screenshot.png' });

// Full page screenshot
await page.screenshot({ path: 'full-page.png', fullPage: true });

// Specific element
await page.locator('.chart').screenshot({ path: 'chart.png' });

// PDF (Chromium only)
await page.pdf({ path: 'page.pdf', format: 'A4' });

await browser.close();
```

## Error Handling

Always wrap navigation and interactions in try-catch blocks:

```javascript
try {
  await page.goto(url, { waitUntil: 'networkidle', timeout: 30000 });
} catch (e) {
  console.error(`Navigation failed: ${e.message}`);
  // Retry with domcontentloaded (less strict)
  await page.goto(url, { waitUntil: 'domcontentloaded', timeout: 30000 });
}

// Wait for element with fallback
try {
  await page.waitForSelector('#content', { timeout: 10000 });
} catch {
  console.error('Element not found, trying alternative selector');
  await page.waitForSelector('.content-area', { timeout: 10000 });
}
```

### Common Failure Modes

| Issue | Solution |
|-------|----------|
| Element not found | Use `waitForSelector` with timeout before interacting |
| Page loads slowly | Use `waitUntil: 'networkidle'` or increase timeout |
| Anti-bot detection | Add realistic viewport, user-agent, and delays |
| Login session expires | Re-authenticate when 401/403 detected |
| Stale element reference | Re-query the element after page changes |

## Anti-Detection Tips

```javascript
const browser = await playwright.chromium.launch({
  headless: true,
  args: ['--disable-blink-features=AutomationControlled']
});

const context = await browser.newContext({
  viewport: { width: 1920, height: 1080 },
  userAgent: 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) ...',
  locale: 'en-US',
  timezoneId: 'America/Los_Angeles'
});
```

## Proxy Support

```javascript
const browser = await playwright.chromium.launch({
  proxy: {
    server: 'http://myproxy.com:8080',
    username: 'user',
    password: 'pass'
  }
});
```

## Output Formats

Structure your scraping output for downstream use:

```javascript
// JSON output
const data = { timestamp: new Date().toISOString(), items: scrapedItems };
fs.writeFileSync('output.json', JSON.stringify(data, null, 2));

// CSV output
const csv = ['title,url,price', ...items.map(i => `"${i.title}","${i.url}","${i.price}"`)].join('\n');
fs.writeFileSync('output.csv', csv);
```

## Integration Notes

- Requires Node.js 14+ with `playwright` installed (`npm install playwright`)
- Use environment variables for credentials — never hardcode
- For large scraping jobs, implement rate limiting between requests
- Save browser context/cookies for session reuse across runs
- Chain with data processing tools for ETL pipelines
