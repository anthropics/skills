# WebApp Testing

## Description
This skill provides a toolkit and workflow for testing local web applications using Python and Playwright. It is designed to handle both static HTML files and dynamic web applications (React, Vue, etc.) that require a running server. It includes helper scripts to manage server lifecycles (starting/stopping servers automatically) and guidelines for a "Reconnaissance-Then-Action" approach: inspecting the DOM state before attempting interactions to ensure robust, non-flaky automation.

## Requirements
- Python environment with `playwright` installed.
- Playwright browsers installed (`playwright install chromium`).
- `scripts/with_server.py`: Helper script for managing background servers.
- Application source code or static HTML to test.

## Cautions
- **Headless Mode**: Always run Playwright in headless mode (`headless=True`) unless specifically debugging visually.
- **Wait States**: For dynamic apps, always use `page.wait_for_load_state('networkidle')` before inspecting the DOM to avoid "element not found" errors.
- **Server Management**: Do not try to manually manage background processes with `&`; use `with_server.py` to ensure clean startup and teardown.

## Definitions
- **Playwright**: A Python library for browser automation.
- **Network Idle**: A state where there are no active network connections for at least 500ms, indicating the page has finished initial loading.
- **Selector**: A pattern used to locate elements on the page (CSS, XPath, text, role).

## Log
(No run logs available yet. This section will be populated by the system upon successful execution.)

## Model Readme
To use this skill:
1.  **Analyze**: Determine if the target is a static file or a dynamic app.
2.  **Server Setup**:
    -   If dynamic and server not running: Use `python scripts/with_server.py --server "cmd" --port XXX -- python test_script.py`.
    -   If static: Use `file:///` URLs directly.
3.  **Develop Script**: Write a Python script using `sync_playwright`.
    -   Pattern: Launch -> Page -> Goto -> **Wait** -> Inspect/Interact -> Close.
4.  **Execute**: Run the script. If using `with_server.py`, the server will start, wait for the port, run your script, and then shut down.
