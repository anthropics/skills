---
name: webapp-testing
description: Playwright automation toolkit for local web application testing, frontend verification, UI debugging, screenshot capture, and browser log extraction.
license: Terms defined in LICENSE.txt
---

# Web Application Testing

Execute local web application tests using native Python Playwright scripts.

## Target Classification and Execution Routing

Route each testing task according to target rendering architecture and local port state:
  + Static HTML target (`file://` URI) ➔ Parse the HTML source file for element selectors, or transition to the dynamic web application workflow when target elements require client-side JavaScript rendering.
  + Dynamic web application on a closed server port ➔ Launch each target server process and coupled Playwright automation script via `scripts/with_server.py`.
  + Dynamic web application on a listening server port ➔ Navigate to the active endpoint, synchronize on `networkidle`, inspect the rendered DOM tree, and execute selector actions.

## Server Lifecycle Management

Orchestrate server lifecycles through the CLI wrapper `scripts/with_server.py` isolated from source file ingestion into the active context window:
- Query CLI parameter definitions via `python scripts/with_server.py --help` prior to process execution.
- Bind 1 server process to its target port and execute the Playwright automation script:
```bash
python scripts/with_server.py --server "npm run dev" --port 5173 -- python your_automation.py
```
- Bind 2 or more concurrent server processes across distinct ports and execute the Playwright automation script:
```bash
python scripts/with_server.py \
  --server "cd backend && python server.py" --port 3000 \
  --server "cd frontend && npm run dev" --port 5173 \
  -- python your_automation.py
```

## Synchronous Playwright Session Lifecycle

Construct each automation script using synchronous Playwright primitives separated from server startup logic:
- Initialize the synchronous runtime context via `sync_playwright()`.
- Launch the Chromium browser instance in headless mode via `p.chromium.launch(headless=True)`.
- Synchronize page execution state via `page.wait_for_load_state('networkidle')` prior to DOM inspection or element interaction, separated from asynchronous JavaScript rendering race conditions:
  + Dynamic DOM inspection prerequisite ➔ Execute `page.wait_for_load_state('networkidle')` after `page.goto()` and prior to `page.content()`, `page.screenshot()`, or `page.locator()`
- Terminate the browser instance via `browser.close()` upon completion of the automation sequence:
```python
from playwright.sync_api import sync_playwright

with sync_playwright() as p:
    browser = p.chromium.launch(headless=True)
    page = browser.new_page()
    page.goto('http://localhost:5173')
    page.wait_for_load_state('networkidle')
    browser.close()
```

## DOM Inspection and Selector Resolution

Execute DOM state inspection and selector resolution across 3 sequential phases after `networkidle` synchronization:
1. Capture the rendered DOM state via page screenshot generation (`full_page=True`), HTML serialization, and locator enumeration:
```python
page.screenshot(path='/tmp/inspect.png', full_page=True)
content = page.content()
page.locator('button').all()
```
2. Resolve each target element using explicit locator prefixes and structural attributes:
  + Text content match ➔ `text=`
  + ARIA role attribute ➔ `role=`
  + Structural style path ➔ CSS selector
  + Unique element identifier ➔ ID attribute
3. Synchronize individual element interactions via `page.wait_for_selector()` or `page.wait_for_timeout()` prior to action invocation.

## Reference Implementations

Map each testing scenario to the corresponding reference script in `examples/`:
  + `examples/element_discovery.py` ➔ Enumerate button, link, and input elements on a rendered page.
  + `examples/static_html_automation.py` ➔ Automate local HTML files via `file://` URLs.
  + `examples/console_logging.py` ➔ Capture browser console log streams during script execution.
