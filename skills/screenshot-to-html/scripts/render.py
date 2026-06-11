#!/usr/bin/env python3
"""
render.py — Render an HTML file to PNG using headless Chromium via Playwright.

Usage:
    python3 render.py <html_path> <output_dir> [selector]

Arguments:
    html_path   — path to the self-contained HTML file
    output_dir  — directory to write PNGs into
    selector    — CSS selector of element to screenshot (default: .wrap)

Output:
    <output_dir>/dashboard.png       — 1x standard
    <output_dir>/dashboard@2x.png   — 2x retina
"""

import sys
import os

def render(html_path, output_dir, selector=".wrap"):
    try:
        from playwright.sync_api import sync_playwright
    except ImportError:
        print("Playwright not installed. Run: pip install playwright --break-system-packages && python3 -m playwright install chromium")
        sys.exit(1)

    os.makedirs(output_dir, exist_ok=True)
    abs_path = os.path.abspath(html_path)
    out_1x = os.path.join(output_dir, "dashboard.png")
    out_2x = os.path.join(output_dir, "dashboard@2x.png")

    with sync_playwright() as p:
        # 1x render
        browser = p.chromium.launch()
        page = browser.new_page(viewport={"width": 1200, "height": 1000})
        page.goto(f"file://{abs_path}")
        page.wait_for_timeout(800)
        el = page.query_selector(selector)
        if el is None:
            print(f"Warning: selector '{selector}' not found, falling back to full page")
            page.screenshot(path=out_1x, type="png", full_page=True)
        else:
            el.screenshot(path=out_1x, type="png")
        browser.close()

        # 2x render (retina)
        browser = p.chromium.launch()
        page = browser.new_page(viewport={"width": 1200, "height": 1000}, device_scale_factor=2)
        page.goto(f"file://{abs_path}")
        page.wait_for_timeout(800)
        el = page.query_selector(selector)
        if el is None:
            page.screenshot(path=out_2x, type="png", full_page=True)
        else:
            el.screenshot(path=out_2x, type="png")
        browser.close()

    print(f"Rendered:")
    print(f"  1x: {out_1x}  ({os.path.getsize(out_1x):,} bytes)")
    print(f"  2x: {out_2x}  ({os.path.getsize(out_2x):,} bytes)")
    return out_1x, out_2x


if __name__ == "__main__":
    if len(sys.argv) < 3:
        print(__doc__)
        sys.exit(1)

    html_path = sys.argv[1]
    output_dir = sys.argv[2]
    selector = sys.argv[3] if len(sys.argv) > 3 else ".wrap"

    render(html_path, output_dir, selector)
