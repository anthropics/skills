# Playwright Browser API Reference (Automation Focus)

This reference covers Playwright's Python async API for browser automation tasks — NOT testing. For test-specific APIs (assertions, fixtures, test runners), see playwright-pro.

## Browser Launch & Context

### Launching the Browser

```python
from playwright.async_api import async_playwright

async with async_playwright() as p:
    # Chromium (recommended for most automation)
    browser = await p.chromium.launch(headless=True)

    # Firefox (better for some anti-detection scenarios)
    browser = await p.firefox.launch(headless=True)

    # WebKit (Safari engine — useful for Apple-specific sites)
    browser = await p.webkit.launch(headless=True)
```

**Launch options:**
| Option | Type | Default | Purpose |
|--------|------|---------|---------|
| `headless` | bool | True | Run without visible window |
| `slow_mo` | int | 0 | Milliseconds to slow each operation (debugging) |
| `proxy` | dict | None | Proxy server configuration |
| `args` | list | [] | Additional Chromium flags |
| `downloads_path` | str | None | Directory for downloads |
| `channel` | str | None | Browser channel: "chrome", "msedge" |

### Browser Contexts (Session Isolation)

Browser contexts are isolated environments within a single browser instance. Each context has its own cookies, localStorage, and cache. Use them instead of launching multiple browsers.

```python
# Create isolated context
context = await browser.new_context(
    viewport={"width": 1920, "height": 1080},
    user_agent="Mozilla/5.0 ...",
    locale="en-US",
    timezone_id="America/New_York",
    geolocation={"latitude": 40.7128, "longitude": -74.0060},
    permissions=["geolocation"],
)

# Multiple contexts share one browser (resource efficient)
context_a = await browser.new_context()  # User A session
context_b = await browser.new_context()  # User B session
```

### Storage State (Session Persistence)

```python
# Save state after login (cookies + localStorage)
await context.storage_state(path="auth_state.json")

# Restore state in new context
context = await browser.new_context(storage_state="auth_state.json")
```

## Page Navigation

### Basic Navigation

```python
page = await context.new_page()

# Navigate with different wait strategies
await page.goto("https://example.com")                          # Default: "load"
await page.goto("https://example.com", wait_until="domcontentloaded")  # Faster
await page.goto("https://example.com", wait_until="networkidle")       # Wait for network quiet
await page.goto("https://example.com", timeout=30000)                  # Custom timeout (ms)
```

**`wait_until` options:**
- `"load"` — wait for the `load` event (all resources loaded)
- `"domcontentloaded"` — DOM is ready, images/styles may still load
- `"networkidle"` — no network requests for 500ms (best for SPAs)
- `"commit"` — response received, before any rendering

### Wait Strategies

```python
# Wait for a specific element to appear
await page.wait_for_selector("div.content", state="visible")
await page.wait_for_selector("div.loading", state="hidden")     # Wait for loading to finish
await page.wait_for_selector("table tbody tr", state="attached") # In DOM but maybe not visible

# Wait for URL change
await page.wait_for_url("**/dashboard**")
await page.wait_for_url(re.compile(r"/dashboard/\d+"))

# Wait for specific network response
async with page.expect_response("**/api/data*") as resp_info:
    await page.click("button.load")
response = await resp_info.value
json_data = await response.json()

# Wait for page load state
await page.wait_for_load_state("networkidle")

# Fixed wait (use sparingly — prefer the methods above)
await page.wait_for_timeout(1000)  # milliseconds
```

### Navigation History

```python
await page.go_back()
await page.go_forward()
await page.reload()
```

## Element Interaction

### Finding Elements

```python
# Single element (returns first match)
element = await page.query_selector("css=div.product")
element = await page.query_selector("xpath=//div[@class='product']")

# Multiple elements
elements = await page.query_selector_all("div.product")

# Locator API (recommended — auto-waits, re-queries on each action)
locator = page.locator("div.product")
count = await locator.count()
first = locator.first
nth = locator.nth(2)
```

**Locator vs query_selector:**
- `query_selector` — returns an ElementHandle at a point in time. Can go stale if DOM changes.
- `locator` — returns a Locator that re-queries each time you interact with it. Preferred for reliability.

### Clicking

```python
await page.click("button.submit")
await page.click("a:has-text('Next')")
await page.dblclick("div.editable")
await page.click("button", position={"x": 10, "y": 10})  # Click at offset
await page.click("button", force=True)  # Skip actionability checks
await page.click("button", modifiers=["Shift"])  # With modifier key
```

### Text Input

```python
# Fill (clears existing content first)
await page.fill("input#email", "user@example.com")

# Type (simulates keystroke-by-keystroke input — slower, more realistic)
await page.type("input#search", "query text", delay=50)  # 50ms between keys

# Press specific keys
await page.press("input#search", "Enter")
await page.press("body", "Control+a")
```

### Dropdowns & Select

```python
# Native <select> element
await page.select_option("select#country", value="US")
await page.select_option("select#country", label="United States")
await page.select_option("select#tags", value=["tag1", "tag2"])  # Multi-select

# Custom dropdown (non-native)
await page.click("div.dropdown-trigger")
await page.click("li.option:has-text('United States')")
```

### Checkboxes & Radio Buttons

```python
await page.check("input#agree")
await page.uncheck("input#newsletter")
is_checked = await page.is_checked("input#agree")
```

### File Upload

```python
# Standard file input
await page.set_input_files("input[type='file']", "/path/to/file.pdf")
await page.set_input_files("input[type='file']", ["/path/a.pdf", "/path/b.pdf"])

# Clear file selection
await page.set_input_files("input[type='file']", [])

# Non-standard upload (drag-and-drop zones)
async with page.expect_file_chooser() as fc_info:
    await page.click("div.upload-zone")
file_chooser = await fc_info.value
await file_chooser.set_files("/path/to/file.pdf")
```

### Hover & Focus

```python
await page.hover("div.menu-item")
await page.focus("input#search")
```

## Data Extraction

### Text Content

```python
# Get text content of an element
text = await page.text_content("h1.title")
inner_text = await page.inner_text("div.description")  # Visible text only
inner_html = await page.inner_html("div.content")       # HTML markup

# Get attribute
href = await page.get_attribute("a.link", "href")
src = await page.get_attribute("img.photo", "src")
```

### JavaScript Evaluation

```python
# Evaluate in page context
title = await page.evaluate("document.title")
scroll_height = await page.evaluate("document.body.scrollHeight")

# Evaluate on a specific element
text = await page.eval_on_selector("h1", "el => el.textContent")
texts = await page.eval_on_selector_all("li", "els => els.map(e => e.textContent.trim())")

# Complex extraction
data = await page.evaluate("""
    () => {
        const rows = document.querySelectorAll('table tbody tr');
        return Array.from(rows).map(row => {
            const cells = row.querySelectorAll('td');
            return {
                name: cells[0]?.textContent.trim(),
                value: cells[1]?.textContent.trim(),
            };
        });
    }
""")
```

### Screenshots & PDF

```python
# Full page screenshot
await page.screenshot(path="page.png", full_page=True)

# Viewport screenshot
await page.screenshot(path="viewport.png")

# Element screenshot
await page.locator("div.chart").screenshot(path="chart.png")

# PDF (Chromium only)
await page.pdf(path="page.pdf", format="A4", print_background=True)

# Screenshot as bytes (for processing without saving)
buffer = await page.screenshot()
```

## Network Interception

### Monitoring Requests

```python
# Listen for all responses
page.on("response", lambda response: print(f"{response.status} {response.url}"))

# Wait for a specific API call
async with page.expect_response("**/api/products*") as resp:
    await page.click("button.load")
response = await resp.value
data = await response.json()
```

### Blocking Resources (Speed Up Scraping)

```python
# Block images, fonts, and CSS to speed up scraping
await page.route("**/*.{png,jpg,jpeg,gif,svg,woff,woff2,ttf}", lambda route: route.abort())
await page.route("**/*.css", lambda route: route.abort())

# Block specific domains (ads, analytics)
await page.route("**/google-analytics.com/**", lambda route: route.abort())
await page.route("**/facebook.com/**", lambda route: route.abort())
```

### Modifying Requests

```python
# Add custom headers
await page.route("**/*", lambda route: route.continue_(headers={
    **route.request.headers,
    "X-Custom-Header": "value"
}))

# Mock API responses
await page.route("**/api/data", lambda route: route.fulfill(
    status=200,
    content_type="application/json",
    body=json.dumps({"items": []}),
))
```

## Dialog Handling

```python
# Auto-accept all dialogs
page.on("dialog", lambda dialog: dialog.accept())

# Handle specific dialog types
async def handle_dialog(dialog):
    if dialog.type == "confirm":
        await dialog.accept()
    elif dialog.type == "prompt":
        await dialog.accept("my input")
    elif dialog.type == "alert":
        await dialog.dismiss()

page.on("dialog", handle_dialog)
```

## File Downloads

```python
# Wait for download to start
async with page.expect_download() as dl_info:
    await page.click("a.download-link")
download = await dl_info.value

# Save to specific path
await download.save_as("/path/to/downloads/" + download.suggested_filename)

# Get download as bytes
path = await download.path()  # Temp file path

# Set download behavior at context level
context = await browser.new_context(accept_downloads=True)
```

## Frames & Iframes

```python
# Access iframe by selector
frame = page.frame_locator("iframe#content")
await frame.locator("button.submit").click()

# Access frame by name
frame = page.frame(name="editor")

# Access all frames
for frame in page.frames:
    print(frame.url)
```

## Cookie Management

```python
# Get all cookies
cookies = await context.cookies()

# Get cookies for specific URL
cookies = await context.cookies(["https://example.com"])

# Add cookies
await context.add_cookies([{
    "name": "session",
    "value": "abc123",
    "domain": "example.com",
    "path": "/",
    "httpOnly": True,
    "secure": True,
}])

# Clear cookies
await context.clear_cookies()
```

## Concurrency Patterns

### Multiple Pages in One Context

```python
# Open multiple tabs in the same session
pages = []
for url in urls:
    page = await context.new_page()
    await page.goto(url)
    pages.append(page)

# Process all pages
for page in pages:
    data = await extract_data(page)
    await page.close()
```

### Multiple Contexts for Parallel Sessions

```python
import asyncio

async def scrape_with_context(browser, url):
    context = await browser.new_context(user_agent=random.choice(USER_AGENTS))
    page = await context.new_page()
    await page.goto(url)
    data = await extract_data(page)
    await context.close()
    return data

# Run 5 concurrent scraping tasks
tasks = [scrape_with_context(browser, url) for url in urls[:5]]
results = await asyncio.gather(*tasks)
```

## Init Scripts (Stealth)

Init scripts run before any page script, in every new page/context.

```python
# Remove webdriver flag
await context.add_init_script("""
    Object.defineProperty(navigator, 'webdriver', {get: () => undefined});
""")

# Override plugins (headless Chrome has empty plugins)
await context.add_init_script("""
    Object.defineProperty(navigator, 'plugins', {
        get: () => [1, 2, 3, 4, 5],
    });
""")

# Override languages
await context.add_init_script("""
    Object.defineProperty(navigator, 'languages', {
        get: () => ['en-US', 'en'],
    });
""")

# From file
await context.add_init_script(path="stealth.js")
```

## Common Automation Patterns

### Scrolling

```python
# Scroll to bottom
await page.evaluate("window.scrollTo(0, document.body.scrollHeight)")

# Scroll element into view
await page.locator("div.target").scroll_into_view_if_needed()

# Smooth scroll simulation
await page.evaluate("""
    async () => {
        const delay = ms => new Promise(r => setTimeout(r, ms));
        for (let i = 0; i < document.body.scrollHeight; i += 300) {
            window.scrollTo(0, i);
            await delay(100);
        }
    }
""")
```

### Clipboard Operations

```python
# Copy text
await page.evaluate("navigator.clipboard.writeText('hello')")

# Paste via keyboard
await page.keyboard.press("Control+v")
```

### Shadow DOM

```python
# Playwright pierces open shadow DOM with >> operator
await page.locator("my-component >> .inner-button").click()

# Or use the css= engine with >> for chained piercing
await page.locator("css=host-element >> css=.shadow-child").click()
```
