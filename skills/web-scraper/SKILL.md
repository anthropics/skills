---
name: shopify-web-scraper
description: Web scraping patterns for Shopify App Store research tasks. Use when extracting data from Shopify App Store (reviews, pricing, install counts, usage duration), general web pages, or any structured data extraction task. Trigger phrases: "爬取", "抓取", "scrape", "extract reviews", "get reviews from", "fetch data from", "Shopify app reviews", "app store data".
---

# Shopify Web Scraper Skill

Standard patterns for web scraping Shopify App Store and general research tasks.

> **Note:** Primarily designed for Shopify App Store research — scraping app reviews, pricing, usage duration, and feature history. Also includes general-purpose patterns for web page extraction and Wayback Machine historical snapshots.

## Tool Priority

1. **WebFetch** — for simple pages where rendered HTML isn't needed (blogs, docs, marketing pages)
2. **curl + python3** — for pages that serve content in HTML but block JS rendering detection
3. **dev-browser** — only when JavaScript rendering is required (SPAs, infinite scroll, login-required pages)

Always try WebFetch first. Fall back to curl if WebFetch fails or returns empty content.

---

## Pattern 1: Shopify App Store Reviews

Extracts review text + star rating + usage duration for any Shopify app.

```bash
curl -s "https://apps.shopify.com/{app-slug}/reviews" \
  -H "User-Agent: Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36" \
  2>/dev/null | python3 -c "
import sys, re

content = sys.stdin.read()

# Usage duration (e.g. '7 months using the app', '4 days using the app')
durations = re.findall(r'[\w\s]+using the app', content, re.IGNORECASE)
print('=== USAGE DURATIONS ===')
for d in durations:
    print(' -', d.strip())

# Review text
content_clean = re.sub(r'<script[^>]*>.*?</script>', '', content, flags=re.DOTALL)
content_clean = re.sub(r'<style[^>]*>.*?</style>', '', content_clean, flags=re.DOTALL)
content_clean = re.sub(r'<[^>]+>', ' ', content_clean)
content_clean = re.sub(r'&quot;', '\"', content_clean)
content_clean = re.sub(r'&amp;', '&', content_clean)
content_clean = re.sub(r'\s+', ' ', content_clean)

# Extract review sentences (look for patterns near star ratings)
reviews = re.findall(r'[A-Z][^.!?]{40,300}[.!?]', content_clean)
print()
print('=== REVIEW EXCERPTS ===')
seen = set()
for r in reviews[:20]:
    r = r.strip()
    if r not in seen and len(r) > 50:
        seen.add(r)
        print(' -', r[:200])
"
```

### Multi-page reviews (page 2, 3...):
```bash
curl -s "https://apps.shopify.com/{app-slug}/reviews?page=2" \
  -H "User-Agent: Mozilla/5.0 ..." 2>/dev/null | python3 -c "..."
```

---

## Pattern 2: Shopify App Store — App Info & Pricing

```bash
curl -s "https://apps.shopify.com/{app-slug}" \
  -H "User-Agent: Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36" \
  2>/dev/null | python3 -c "
import sys, re

content = sys.stdin.read()
content_clean = re.sub(r'<script[^>]*>.*?</script>', '', content, flags=re.DOTALL)
content_clean = re.sub(r'<style[^>]*>.*?</style>', '', content_clean, flags=re.DOTALL)
content_clean = re.sub(r'<[^>]+>', ' ', content_clean)
content_clean = re.sub(r'\s+', ' ', content_clean)

# Pricing
pricing = re.findall(r'\\\$[\d,.]+\s*/\s*month[\w\s,/]*', content_clean, re.IGNORECASE)
print('=== PRICING ===')
for p in set(pricing):
    print(' -', p.strip())

# Rating
rating = re.findall(r'[\d.]+\s*(?:out of|/)\s*5\s*stars?', content_clean, re.IGNORECASE)
print()
print('=== RATING ===')
for r in rating[:3]:
    print(' -', r.strip())

# Features (look for bullet-point style content)
features = re.findall(r'(?:•|·|\*|✓|✅)[^\n•·*✓✅]{10,150}', content_clean)
print()
print('=== FEATURES ===')
for f in features[:15]:
    print(' -', f.strip())
"
```

---

## Pattern 3: Wayback Machine Historical Snapshots

Use this to track when a feature first appeared on a product page.

```bash
# Step 1: Get all snapshot timestamps for a URL
curl -s "https://web.archive.org/cdx/search/cdx?url={URL}&output=json&fl=timestamp,statuscode&filter=statuscode:200&limit=50" \
  2>/dev/null | python3 -c "
import json, sys
data = json.load(sys.stdin)
for row in data[1:]:  # skip header
    print(row[0])  # timestamp like 20230208213304
"

# Step 2: Fetch a specific snapshot and search for keywords
curl -s "https://web.archive.org/web/{TIMESTAMP}/{URL}" \
  -H "User-Agent: Mozilla/5.0 ..." 2>/dev/null | python3 -c "
import sys, re
content = sys.stdin.read()
content = re.sub(r'<script[^>]*>.*?</script>', '', content, flags=re.DOTALL)
content = re.sub(r'<style[^>]*>.*?</style>', '', content, flags=re.DOTALL)
content = re.sub(r'<[^>]+>', ' ', content)
content = re.sub(r'\s+', ' ', content)

keywords = ['AMP', 'Instant Index', 'AI Blog', 'ChatGPT', 'JSON-LD']
for kw in keywords:
    idx = content.lower().find(kw.lower())
    if idx >= 0:
        print(f'[{kw}] {content[max(0,idx-60):idx+120].strip()}')
"
```

---

## Pattern 4: General Web Page Content Extraction

```bash
curl -s "{URL}" \
  -H "User-Agent: Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36" \
  -H "Accept-Language: en-US,en;q=0.9" \
  -L \
  2>/dev/null | python3 -c "
import sys, re
content = sys.stdin.read()
content = re.sub(r'<script[^>]*>.*?</script>', '', content, flags=re.DOTALL)
content = re.sub(r'<style[^>]*>.*?</style>', '', content, flags=re.DOTALL)
content = re.sub(r'<[^>]+>', ' ', content)
content = re.sub(r'&[a-z]+;', ' ', content)
content = re.sub(r'\s+', ' ', content).strip()
print(content[:3000])
"
```

---

## When to Use dev-browser Instead

Use dev-browser when:
- Page requires login / session cookie
- Content loads via JavaScript after page load (infinite scroll, React SPA)
- Need to click buttons or fill forms
- Need screenshots

```bash
dev-browser --headless <<'EOF'
const page = await browser.getPage("main");
await page.goto("{URL}");
await page.waitForTimeout(2000);  // wait for JS to render
const content = await page.evaluate(() => document.body.innerText);
console.log(content.slice(0, 3000));
EOF
```

---

## Common Issues

| Problem | Solution |
|---------|----------|
| `apps.shopify.com` returns 403 | Add `-H "User-Agent: Mozilla/5.0..."` header |
| Content is empty | Page uses JS rendering → use dev-browser |
| Wayback Machine blocked | `web.archive.org` occasionally rate-limits, retry after 10s |
| Chinese/UTF-8 content garbled | Add `PYTHONIOENCODING=utf-8` before python3 command |
