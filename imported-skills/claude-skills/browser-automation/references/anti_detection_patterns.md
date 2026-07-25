# Anti-Detection Patterns for Browser Automation

This reference covers techniques to make Playwright automation less detectable by anti-bot services. These are defense-in-depth measures — no single technique is sufficient, but combining them significantly reduces detection risk.

## Detection Vectors

Anti-bot systems detect automation through multiple signals. Understanding what they check helps you counter effectively.

### Tier 1: Trivial Detection (Every Site Checks These)
1. **navigator.webdriver** — Set to `true` by all automation frameworks
2. **User-Agent string** — Default headless UA contains "HeadlessChrome"
3. **WebGL renderer** — Headless Chrome reports "SwiftShader" or "Google SwiftShader"

### Tier 2: Common Detection (Most Anti-Bot Services)
4. **Viewport/screen dimensions** — Unusual sizes flag automation
5. **Plugins array** — Empty in headless mode, populated in real browsers
6. **Languages** — Missing or mismatched locale
7. **Request timing** — Machine-speed interactions
8. **Mouse movement** — No mouse events between clicks

### Tier 3: Advanced Detection (Cloudflare, DataDome, PerimeterX)
9. **Canvas fingerprint** — Headless renders differently
10. **WebGL fingerprint** — GPU-specific rendering variations
11. **Audio fingerprint** — AudioContext processing differences
12. **Font enumeration** — Different available fonts in headless
13. **Behavioral analysis** — Scroll patterns, click patterns, reading time

## Stealth Techniques

### 1. WebDriver Flag Removal

The most critical fix. Every anti-bot check starts here.

```python
await page.add_init_script("""
    // Remove webdriver flag
    Object.defineProperty(navigator, 'webdriver', {
        get: () => undefined,
    });

    // Remove Playwright-specific properties
    delete window.__playwright;
    delete window.__pw_manual;
""")
```

### 2. User Agent Configuration

Match the user agent to the browser you are launching. A Chrome UA with Firefox-specific headers is a red flag.

```python
# Chrome 120 on Windows 10 (most common configuration globally)
CHROME_WIN = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"

# Chrome 120 on macOS
CHROME_MAC = "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"

# Chrome 120 on Linux
CHROME_LINUX = "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"

# Firefox 121 on Windows
FIREFOX_WIN = "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:121.0) Gecko/20100101 Firefox/121.0"
```

**Rules:**
- Update UAs every 2-3 months as browser versions increment
- Match UA platform to `navigator.platform` override
- If using Chromium, use Chrome UAs. If Firefox, use Firefox UAs.
- Never use obviously fake or ancient UAs

### 3. Viewport and Screen Properties

Common real-world screen resolutions (from analytics data):

| Resolution | Market Share | Use For |
|-----------|-------------|---------|
| 1920x1080 | ~23% | Default choice |
| 1366x768 | ~14% | Laptop simulation |
| 1536x864 | ~9% | Scaled laptop |
| 1440x900 | ~7% | MacBook |
| 2560x1440 | ~5% | High-end desktop |

```python
import random

VIEWPORTS = [
    {"width": 1920, "height": 1080},
    {"width": 1366, "height": 768},
    {"width": 1536, "height": 864},
    {"width": 1440, "height": 900},
]

viewport = random.choice(VIEWPORTS)
context = await browser.new_context(
    viewport=viewport,
    screen=viewport,  # screen should match viewport
)
```

### 4. Navigator Properties Hardening

```python
STEALTH_INIT = """
    // Plugins (headless Chrome has 0 plugins, real Chrome has 3-5)
    Object.defineProperty(navigator, 'plugins', {
        get: () => {
            const plugins = [
                { name: 'Chrome PDF Plugin', filename: 'internal-pdf-viewer' },
                { name: 'Chrome PDF Viewer', filename: 'mhjfbmdgcfjbbpaeojofohoefgiehjai' },
                { name: 'Native Client', filename: 'internal-nacl-plugin' },
            ];
            plugins.length = 3;
            return plugins;
        },
    });

    // Languages
    Object.defineProperty(navigator, 'languages', {
        get: () => ['en-US', 'en'],
    });

    // Platform (match to user agent)
    Object.defineProperty(navigator, 'platform', {
        get: () => 'Win32',  // or 'MacIntel' for macOS UA
    });

    // Hardware concurrency (real browsers report CPU cores)
    Object.defineProperty(navigator, 'hardwareConcurrency', {
        get: () => 8,
    });

    // Device memory (Chrome-specific)
    Object.defineProperty(navigator, 'deviceMemory', {
        get: () => 8,
    });

    // Connection info
    Object.defineProperty(navigator, 'connection', {
        get: () => ({
            effectiveType: '4g',
            rtt: 50,
            downlink: 10,
            saveData: false,
        }),
    });
"""

await context.add_init_script(STEALTH_INIT)
```

### 5. WebGL Fingerprint Evasion

Headless Chrome uses SwiftShader for WebGL, which anti-bot services detect.

```python
# Option A: Launch with a real GPU (headed mode on a machine with GPU)
browser = await p.chromium.launch(headless=False)

# Option B: Override WebGL renderer info
await page.add_init_script("""
    const getParameter = WebGLRenderingContext.prototype.getParameter;
    WebGLRenderingContext.prototype.getParameter = function(parameter) {
        if (parameter === 37445) {
            return 'Intel Inc.';  // UNMASKED_VENDOR_WEBGL
        }
        if (parameter === 37446) {
            return 'Intel(R) Iris(TM) Plus Graphics 640';  // UNMASKED_RENDERER_WEBGL
        }
        return getParameter.call(this, parameter);
    };
""")
```

### 6. Canvas Fingerprint Noise

Anti-bot services render text/shapes to a canvas and hash the output. Headless Chrome produces a different hash.

```python
await page.add_init_script("""
    const originalToDataURL = HTMLCanvasElement.prototype.toDataURL;
    HTMLCanvasElement.prototype.toDataURL = function(type) {
        if (type === 'image/png' || type === undefined) {
            // Add minimal noise to the canvas to change fingerprint
            const ctx = this.getContext('2d');
            if (ctx) {
                const imageData = ctx.getImageData(0, 0, this.width, this.height);
                for (let i = 0; i < imageData.data.length; i += 4) {
                    // Shift one channel by +/- 1 (imperceptible)
                    imageData.data[i] = imageData.data[i] ^ 1;
                }
                ctx.putImageData(imageData, 0, 0);
            }
        }
        return originalToDataURL.apply(this, arguments);
    };
""")
```

## Request Throttling Patterns

### Human-Like Delays

Real users do not click at machine speed. Add realistic delays between actions.

```python
import random
import asyncio

async def human_delay(action_type="browse"):
    """Add realistic delay based on action type."""
    delays = {
        "browse": (1.0, 3.0),      # Browsing between pages
        "read": (2.0, 8.0),        # Reading content
        "fill": (0.3, 0.8),        # Between form fields
        "click": (0.1, 0.5),       # Before clicking
        "scroll": (0.5, 1.5),      # Between scroll actions
    }
    min_s, max_s = delays.get(action_type, (0.5, 2.0))
    await asyncio.sleep(random.uniform(min_s, max_s))
```

### Request Rate Limiting

```python
import time

class RateLimiter:
    """Enforce minimum delay between requests."""

    def __init__(self, min_interval_seconds=1.0):
        self.min_interval = min_interval_seconds
        self.last_request_time = 0

    async def wait(self):
        elapsed = time.time() - self.last_request_time
        if elapsed < self.min_interval:
            await asyncio.sleep(self.min_interval - elapsed)
        self.last_request_time = time.time()

# Usage
limiter = RateLimiter(min_interval_seconds=2.0)
for url in urls:
    await limiter.wait()
    await page.goto(url)
```

### Exponential Backoff on Errors

```python
async def with_backoff(coro_factory, max_retries=5, base_delay=1.0):
    for attempt in range(max_retries):
        try:
            return await coro_factory()
        except Exception as e:
            if attempt == max_retries - 1:
                raise
            delay = base_delay * (2 ** attempt) + random.uniform(0, 1)
            print(f"Attempt {attempt + 1} failed: {e}. Retrying in {delay:.1f}s...")
            await asyncio.sleep(delay)
```

## Proxy Rotation Strategies

### Single Proxy

```python
browser = await p.chromium.launch(
    proxy={"server": "http://proxy.example.com:8080"}
)
```

### Authenticated Proxy

```python
context = await browser.new_context(
    proxy={
        "server": "http://proxy.example.com:8080",
        "username": "user",
        "password": "pass",
    }
)
```

### Rotating Proxy Pool

```python
PROXIES = [
    "http://proxy1.example.com:8080",
    "http://proxy2.example.com:8080",
    "http://proxy3.example.com:8080",
]

async def create_context_with_proxy(browser):
    proxy = random.choice(PROXIES)
    return await browser.new_context(
        proxy={"server": proxy}
    )
```

### Per-Request Proxy (via Context Rotation)

Playwright does not support per-request proxy switching. Achieve it by creating a new context for each request or batch:

```python
async def scrape_url(browser, url, proxy):
    context = await browser.new_context(proxy={"server": proxy})
    page = await context.new_page()
    try:
        await page.goto(url)
        data = await extract_data(page)
        return data
    finally:
        await context.close()
```

### SOCKS5 Proxy

```python
browser = await p.chromium.launch(
    proxy={"server": "socks5://proxy.example.com:1080"}
)
```

## Headless Detection Avoidance

### Running Chrome Channel Instead of Chromium

The bundled Chromium binary has different properties than a real Chrome install. Using the Chrome channel makes the browser indistinguishable from a normal install.

```python
# Use installed Chrome instead of bundled Chromium
browser = await p.chromium.launch(channel="chrome", headless=True)
```

**Requirements:** Chrome must be installed on the system.

### New Headless Mode (Chrome 112+)

Chrome's "new headless" mode is harder to detect than the old one:

```python
browser = await p.chromium.launch(
    args=["--headless=new"],
)
```

### Avoiding Common Flags

Do NOT pass these flags — they are headless-detection signals:
- `--disable-gpu` (old headless workaround, not needed)
- `--no-sandbox` (security risk, detectable)
- `--disable-setuid-sandbox` (same as above)

## Behavioral Evasion

### Mouse Movement Simulation

Anti-bot services track mouse events. A click without preceding mouse movement is suspicious.

```python
async def human_click(page, selector):
    """Click with preceding mouse movement."""
    element = await page.query_selector(selector)
    box = await element.bounding_box()
    if box:
        # Move to element with slight offset
        x = box["x"] + box["width"] / 2 + random.uniform(-5, 5)
        y = box["y"] + box["height"] / 2 + random.uniform(-5, 5)
        await page.mouse.move(x, y, steps=random.randint(5, 15))
        await asyncio.sleep(random.uniform(0.05, 0.2))
        await page.mouse.click(x, y)
```

### Typing Speed Variation

```python
async def human_type(page, selector, text):
    """Type with variable speed like a human."""
    await page.click(selector)
    for char in text:
        await page.keyboard.type(char)
        # Faster for common keys, slower for special characters
        if char in "aeiou tnrs":
            await asyncio.sleep(random.uniform(0.03, 0.08))
        else:
            await asyncio.sleep(random.uniform(0.08, 0.20))
```

### Scroll Behavior

Real users scroll gradually, not in instant jumps.

```python
async def human_scroll(page, distance=None):
    """Scroll down gradually like a human."""
    if distance is None:
        distance = random.randint(300, 800)

    current = 0
    while current < distance:
        step = random.randint(50, 150)
        await page.mouse.wheel(0, step)
        current += step
        await asyncio.sleep(random.uniform(0.05, 0.15))
```

## Detection Testing

### Self-Check Script

Navigate to these URLs to test your stealth configuration:

- `https://bot.sannysoft.com/` — Comprehensive bot detection test
- `https://abrahamjuliot.github.io/creepjs/` — Advanced fingerprint analysis
- `https://browserleaks.com/webgl` — WebGL fingerprint details
- `https://browserleaks.com/canvas` — Canvas fingerprint details

### Quick Test Pattern

```python
async def test_stealth(page):
    """Navigate to detection test page and report results."""
    await page.goto("https://bot.sannysoft.com/")
    await page.wait_for_timeout(3000)

    # Check for failed tests
    failed = await page.eval_on_selector_all(
        "td.failed",
        "els => els.map(e => e.parentElement.querySelector('td').textContent)"
    )

    if failed:
        print(f"FAILED checks: {failed}")
    else:
        print("All checks passed.")

    await page.screenshot(path="stealth_test.png", full_page=True)
```

## Recommended Stealth Stack

For most automation tasks, apply these in order of priority:

1. **WebDriver flag removal** — Critical, takes 2 lines
2. **Custom user agent** — Critical, takes 1 line
3. **Viewport configuration** — High priority, takes 1 line
4. **Request delays** — High priority, add random.uniform() calls
5. **Navigator properties** — Medium priority, init script block
6. **Chrome channel** — Medium priority, one launch option
7. **WebGL override** — Low priority unless hitting advanced anti-bot
8. **Canvas noise** — Low priority unless hitting advanced anti-bot
9. **Proxy rotation** — Only for high-volume or repeated scraping
10. **Behavioral simulation** — Only for sites with behavioral analysis
