---
name: "browser-automation"
description: "Use when the user asks to automate browser tasks, scrape websites, fill forms, capture screenshots, extract structured data from web pages, or build web automation workflows. NOT for testing — use playwright-pro for that."
---

# Browser Automation - POWERFUL

## Overview

The Browser Automation skill provides comprehensive tools and knowledge for building production-grade web automation workflows using Playwright. This skill covers data extraction, form filling, screenshot capture, session management, and anti-detection patterns for reliable browser automation at scale.

**When to use this skill:**
- Scraping structured data from websites (tables, listings, search results)
- Automating multi-step browser workflows (login, fill forms, download files)
- Capturing screenshots or PDFs of web pages
- Extracting data from SPAs and JavaScript-heavy sites
- Building repeatable browser-based data pipelines

**When NOT to use this skill:**
- Writing browser tests or E2E test suites — use **playwright-pro** instead
- Testing API endpoints — use **api-test-suite-builder** instead
- Load testing or performance benchmarking — use **performance-profiler** instead

**Why Playwright over Selenium or Puppeteer:**
- **Auto-wait built in** — no explicit `sleep()` or `waitForElement()` needed for most actions
- **Multi-browser from one API** — Chromium, Firefox, WebKit with zero config changes
- **Network interception** — block ads, mock responses, capture API calls natively
- **Browser contexts** — isolated sessions without spinning up new browser instances
- **Codegen** — `playwright codegen` records your actions and generates scripts
- **Async-first** — Python async/await for high-throughput scraping

## Core Competencies

### 1. Web Scraping Patterns

**Selector priority (most to least reliable):**
1. `data-testid`, `data-id`, or custom data attributes — stable across redesigns
2. `#id` selectors — unique but may change between deploys
3. Semantic selectors: `article`, `nav`, `main`, `section` — resilient to CSS changes
4. Class-based: `.product-card`, `.price` — brittle if classes are generated (e.g., CSS modules)
5. Positional: `nth-child()`, `nth-of-type()` — last resort, breaks on layout changes

Use XPath only when CSS cannot express the relationship (e.g., ancestor traversal, text-based selection).

**Pagination strategies:** next-button, URL-based (`?page=N`), infinite scroll, load-more button. See [data_extraction_recipes.md](references/data_extraction_recipes.md) for complete pagination handlers and scroll patterns.

### 2. Form Filling & Multi-Step Workflows

Break multi-step forms into discrete functions per step. Each function fills fields, clicks "Next"/"Continue", and waits for the next step to load (URL change or DOM element).

Key patterns: login flows, multi-page forms, file uploads (including drag-and-drop zones), native and custom dropdown handling. See [playwright_browser_api.md](references/playwright_browser_api.md) for complete API reference on `fill()`, `select_option()`, `set_input_files()`, and `expect_file_chooser()`.

### 3. Screenshot & PDF Capture

- **Full page:** `await page.screenshot(path="full.png", full_page=True)`
- **Element:** `await page.locator("div.chart").screenshot(path="chart.png")`
- **PDF (Chromium only):** `await page.pdf(path="out.pdf", format="A4", print_background=True)`
- **Visual regression:** Take screenshots at known states, store baselines in version control with naming: `{page}_{viewport}_{state}.png`

See [playwright_browser_api.md](references/playwright_browser_api.md) for full screenshot/PDF options.

### 4. Structured Data Extraction

Core extraction patterns:
- **Tables to JSON** — Extract `<thead>` headers and `<tbody>` rows into dictionaries
- **Listings to arrays** — Map repeating card elements using a field-selector map (supports `::attr()` for attributes)
- **Nested/threaded data** — Recursive extraction for comments with replies, category trees

See [data_extraction_recipes.md](references/data_extraction_recipes.md) for complete extraction functions, price parsing, data cleaning utilities, and output format helpers (JSON, CSV, JSONL).

### 5. Cookie & Session Management

- **Save/restore cookies:** `context.cookies()` and `context.add_cookies()`
- **Full storage state** (cookies + localStorage): `context.storage_state(path="state.json")` to save, `browser.new_context(storage_state="state.json")` to restore

**Best practice:** Save state after login, reuse across scraping sessions. Check session validity before starting a long job — make a lightweight request to a protected page and verify you are not redirected to login. See [playwright_browser_api.md](references/playwright_browser_api.md) for cookie and storage state API details.

### 6. Anti-Detection Patterns

Modern websites detect automation through multiple vectors. Apply these in priority order:

1. **WebDriver flag removal** — Remove `navigator.webdriver = true` via init script (critical)
2. **Custom user agent** — Rotate through real browser UAs; never use the default headless UA
3. **Realistic viewport** — Set 1920x1080 or similar real-world dimensions (default 800x600 is a red flag)
4. **Request throttling** — Add `random.uniform()` delays between actions
5. **Proxy support** — Per-browser or per-context proxy configuration

See [anti_detection_patterns.md](references/anti_detection_patterns.md) for the complete stealth stack: navigator property hardening, WebGL/canvas fingerprint evasion, behavioral simulation (mouse movement, typing speed, scroll patterns), proxy rotation strategies, and detection self-test URLs.

### 7. Dynamic Content Handling

- **SPA rendering:** Wait for content selectors (`wait_for_selector`), not the page load event
- **AJAX/Fetch waiting:** Use `page.expect_response("**/api/data*")` to intercept and wait for specific API calls
- **Shadow DOM:** Playwright pierces open Shadow DOM with `>>` operator: `page.locator("custom-element >> .inner-class")`
- **Lazy-loaded images:** Scroll elements into view with `scroll_into_view_if_needed()` to trigger loading

See [playwright_browser_api.md](references/playwright_browser_api.md) for wait strategies, network interception, and Shadow DOM details.

### 8. Error Handling & Retry Logic

- **Retry with backoff:** Wrap page interactions in retry logic with exponential backoff (e.g., 1s, 2s, 4s)
- **Fallback selectors:** On `TimeoutError`, try alternative selectors before failing
- **Error-state screenshots:** Capture `page.screenshot(path="error-state.png")` on unexpected failures for debugging
- **Rate limit detection:** Check for HTTP 429 responses and respect `Retry-After` headers

See [anti_detection_patterns.md](references/anti_detection_patterns.md) for the complete exponential backoff implementation and rate limiter class.

## Workflows

### Workflow 1: Single-Page Data Extraction

**Scenario:** Extract product data from a single page with JavaScript-rendered content.

**Steps:**
1. Launch browser in headed mode during development (`headless=False`), switch to headless for production
2. Navigate to URL and wait for content selector
3. Extract data using `query_selector_all` with field mapping
4. Validate extracted data (check for nulls, expected types)
5. Output as JSON

```python
async def extract_single_page(url, selectors):
    async with async_playwright() as p:
        browser = await p.chromium.launch(headless=True)
        context = await browser.new_context(
            viewport={"width": 1920, "height": 1080},
            user_agent="Mozilla/5.0 ..."
        )
        page = await context.new_page()
        await page.goto(url, wait_until="networkidle")
        data = await extract_listings(page, selectors["container"], selectors["fields"])
        await browser.close()
    return data
```

### Workflow 2: Multi-Page Scraping with Pagination

**Scenario:** Scrape search results across 50+ pages.

**Steps:**
1. Launch browser with anti-detection settings
2. Navigate to first page
3. Extract data from current page
4. Check if "Next" button exists and is enabled
5. Click next, wait for new content to load (not just navigation)
6. Repeat until no next page or max pages reached
7. Deduplicate results by unique key
8. Write output incrementally (don't hold everything in memory)

```python
async def scrape_paginated(base_url, selectors, max_pages=100):
    all_data = []
    async with async_playwright() as p:
        browser = await p.chromium.launch(headless=True)
        page = await (await browser.new_context()).new_page()
        await page.goto(base_url)

        for page_num in range(max_pages):
            items = await extract_listings(page, selectors["container"], selectors["fields"])
            all_data.extend(items)

            next_btn = page.locator(selectors["next_button"])
            if await next_btn.count() == 0 or await next_btn.is_disabled():
                break

            await next_btn.click()
            await page.wait_for_selector(selectors["container"])
            await human_delay(800, 2000)

        await browser.close()
    return all_data
```

### Workflow 3: Authenticated Workflow Automation

**Scenario:** Log into a portal, navigate a multi-step form, download a report.

**Steps:**
1. Check for existing session state file
2. If no session, perform login and save state
3. Navigate to target page using saved session
4. Fill multi-step form with provided data
5. Wait for download to trigger
6. Save downloaded file to target directory

```python
async def authenticated_workflow(credentials, form_data, download_dir):
    async with async_playwright() as p:
        browser = await p.chromium.launch(headless=True)
        state_file = "session_state.json"

        # Restore or create session
        if os.path.exists(state_file):
            context = await browser.new_context(storage_state=state_file)
        else:
            context = await browser.new_context()
            page = await context.new_page()
            await login(page, credentials["url"], credentials["user"], credentials["pass"])
            await context.storage_state(path=state_file)

        page = await context.new_page()
        await page.goto(form_data["target_url"])

        # Fill form steps
        for step_fn in [fill_step_1, fill_step_2]:
            await step_fn(page, form_data)

        # Handle download
        async with page.expect_download() as dl_info:
            await page.click("button:has-text('Download Report')")
        download = await dl_info.value
        await download.save_as(os.path.join(download_dir, download.suggested_filename))

        await browser.close()
```

## Tools Reference

| Script | Purpose | Key Flags | Output |
|--------|---------|-----------|--------|
| `scraping_toolkit.py` | Generate Playwright scraping script skeleton | `--url`, `--selectors`, `--paginate`, `--output` | Python script or JSON config |
| `form_automation_builder.py` | Generate form-fill automation script from field spec | `--fields`, `--url`, `--output` | Python automation script |
| `anti_detection_checker.py` | Audit a Playwright script for detection vectors | `--file`, `--verbose` | Risk report with score |

All scripts are stdlib-only. Run `python3 <script> --help` for full usage.

## Anti-Patterns

### Hardcoded Waits
**Bad:** `await page.wait_for_timeout(5000)` before every action.
**Good:** Use `wait_for_selector`, `wait_for_url`, `expect_response`, or `wait_for_load_state`. Hardcoded waits are flaky and slow.

### No Error Recovery
**Bad:** Linear script that crashes on first failure.
**Good:** Wrap each page interaction in try/except. Take error-state screenshots. Implement retry with exponential backoff.

### Ignoring robots.txt
**Bad:** Scraping without checking robots.txt directives.
**Good:** Fetch and parse robots.txt before scraping. Respect `Crawl-delay`. Skip disallowed paths. Add your bot name to User-Agent if running at scale.

### Storing Credentials in Scripts
**Bad:** Hardcoding usernames and passwords in Python files.
**Good:** Use environment variables, `.env` files (gitignored), or a secrets manager. Pass credentials via CLI arguments.

### No Rate Limiting
**Bad:** Hammering a site with 100 requests/second.
**Good:** Add random delays between requests (1-3s for polite scraping). Monitor for 429 responses. Implement exponential backoff.

### Selector Fragility
**Bad:** Relying on auto-generated class names (`.css-1a2b3c`) or deep nesting (`div > div > div > span:nth-child(3)`).
**Good:** Use data attributes, semantic HTML, or text-based locators. Test selectors in browser DevTools first.

### Not Cleaning Up Browser Instances
**Bad:** Launching browsers without closing them, leading to resource leaks.
**Good:** Always use `try/finally` or async context managers to ensure `browser.close()` is called.

### Running Headed in Production
**Bad:** Using `headless=False` in production/CI.
**Good:** Develop with headed mode for debugging, deploy with `headless=True`. Use environment variable to toggle: `headless = os.environ.get("HEADLESS", "true") == "true"`.

## Cross-References

- **playwright-pro** — Browser testing skill. Use for E2E tests, test assertions, test fixtures. Browser Automation is for data extraction and workflow automation, not testing.
- **api-test-suite-builder** — When the website has a public API, hit the API directly instead of scraping the rendered page. Faster, more reliable, less detectable.
- **performance-profiler** — If your automation scripts are slow, profile the bottlenecks before adding concurrency.
- **env-secrets-manager** — For securely managing credentials used in authenticated automation workflows.
