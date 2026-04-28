#!/usr/bin/env python3
"""
Interactive Component Video Recorder (v6.0)

Records videos of interactive component state transitions.
For each component (tabs, workflow steps, carousels), clicks through
each state with pauses to capture the transition animations.

This gives Gemini visual context for how component states transition —
timing, easing, direction, and visual effects that screenshots can't show.

Requirements:
    pip install playwright
    playwright install chromium

Usage:
    # Auto-detect interactive components and record
    python record_interactions.py https://example.com /tmp/interactions.webm

    # Specify components manually
    python record_interactions.py https://example.com /tmp/interactions.webm \
        --selectors ".tab-btn" ".workflow-step" ".carousel-next"
"""

import asyncio
import argparse
import sys
from pathlib import Path

try:
    from playwright.async_api import async_playwright
except ImportError:
    print("Error: playwright not installed")
    print("Install with: pip install playwright && playwright install chromium")
    sys.exit(1)


async def detect_interactive_components(page):
    """
    Auto-detect interactive components on the page using accessibility tree
    and common patterns.

    Returns list of component configs:
    [
        {"selector": ".tab-btn", "type": "click-each", "count": 4, "label": "tabs"},
        {"selector": ".step-item", "type": "click-each", "count": 7, "label": "workflow"},
        {"selector": ".carousel-next", "type": "click-repeat", "count": 5, "label": "carousel"},
    ]
    """
    return await page.evaluate("""
        (() => {
            const components = [];

            // Detect tab systems
            const tabButtons = document.querySelectorAll('[role="tab"], [data-tab], .tab-btn, .tab-trigger');
            if (tabButtons.length >= 2) {
                const selector = tabButtons[0].getAttribute('role') === 'tab'
                    ? '[role="tab"]'
                    : tabButtons[0].className.split(' ').map(c => '.' + c).join('');
                components.push({
                    selector: selector,
                    type: 'click-each',
                    count: tabButtons.length,
                    label: 'tabs'
                });
            }

            // Detect step/workflow systems
            const steps = document.querySelectorAll(
                '[class*="step"], [class*="workflow"], [class*="progress-item"], ' +
                '[class*="timeline-item"], [data-step]'
            );
            if (steps.length >= 3) {
                // Find clickable elements within steps
                const clickable = [...steps].filter(s =>
                    s.tagName === 'BUTTON' || s.tagName === 'A' ||
                    s.getAttribute('role') === 'tab' ||
                    s.style.cursor === 'pointer' ||
                    getComputedStyle(s).cursor === 'pointer'
                );
                if (clickable.length >= 3) {
                    const firstClass = clickable[0].className.split(' ')[0];
                    components.push({
                        selector: '.' + firstClass,
                        type: 'click-each',
                        count: clickable.length,
                        label: 'workflow-steps'
                    });
                }
            }

            // Detect carousels/sliders
            const nextBtns = document.querySelectorAll(
                '[class*="next"], [class*="slide-next"], [aria-label*="next"], ' +
                '[aria-label*="Next"], button[class*="arrow-right"]'
            );
            if (nextBtns.length > 0) {
                components.push({
                    selector: nextBtns[0].className
                        ? '.' + nextBtns[0].className.split(' ')[0]
                        : '[aria-label*="next"]',
                    type: 'click-repeat',
                    count: 5,  // Click next 5 times
                    label: 'carousel'
                });
            }

            // Detect accordions
            const accordions = document.querySelectorAll(
                '[class*="accordion"] button, [class*="faq"] button, ' +
                'button[aria-expanded], details > summary'
            );
            if (accordions.length >= 2) {
                components.push({
                    selector: accordions[0].tagName === 'SUMMARY'
                        ? 'details > summary'
                        : '[class*="accordion"] button, [class*="faq"] button',
                    type: 'click-each',
                    count: Math.min(accordions.length, 8),
                    label: 'accordion'
                });
            }

            return components;
        })()
    """)


async def record_component_interactions(
    url: str,
    output_path: str,
    selectors: list = None,
    viewport_width: int = 1440,
    viewport_height: int = 900,
    device_scale_factor: int = 2,
    pause_between_clicks: int = 1500,
    headless: bool = True
):
    """
    Record video of clicking through interactive component states.

    Args:
        url: Page URL to record
        output_path: Where to save the .webm video file
        selectors: Optional list of CSS selectors to click. If None, auto-detect.
        viewport_width: Browser viewport width
        viewport_height: Browser viewport height
        device_scale_factor: DPI scale (2 for Retina)
        pause_between_clicks: Milliseconds to wait between clicks (captures transition)
        headless: Run browser without GUI (True for server/CI)

    Returns:
        Path to the recorded video file
    """
    print(f"[1/5] Launching browser for interaction recording...")

    async with async_playwright() as p:
        # Launch browser with video recording enabled
        browser = await p.chromium.launch(headless=headless)

        # Create a new context with video recording
        context = await browser.new_context(
            viewport={"width": viewport_width, "height": viewport_height},
            device_scale_factor=device_scale_factor,
            record_video_dir=str(Path(output_path).parent),
            record_video_size={"width": viewport_width, "height": viewport_height}
        )

        page = await context.new_page()

        print(f"[2/5] Navigating to {url}...")
        try:
            await page.goto(url, wait_until="networkidle", timeout=15000)
        except Exception:
            print("       networkidle timed out, using domcontentloaded fallback...")
            await page.goto(url, wait_until="domcontentloaded", timeout=30000)

        # Wait for page to fully render
        await page.wait_for_timeout(3000)

        # Determine components to interact with
        if selectors:
            components = [
                {"selector": s, "type": "click-each", "count": 10, "label": s}
                for s in selectors
            ]
        else:
            print(f"[3/5] Auto-detecting interactive components...")
            components = await detect_interactive_components(page)

        if not components:
            print("       No interactive components detected. Recording scroll only.")
            # Fallback: just do a slow scroll so the video isn't empty
            page_height = await page.evaluate("document.body.scrollHeight")
            total_steps = 300
            for i in range(total_steps):
                await page.evaluate(f"window.scrollTo(0, {int((page_height / total_steps) * i)})")
                await page.wait_for_timeout(16)
            await page.wait_for_timeout(1000)
        else:
            print(f"       Found {len(components)} interactive components:")
            for comp in components:
                print(f"       - {comp['label']}: {comp['selector']} ({comp['count']} states)")

            print(f"[4/5] Recording interactions ({pause_between_clicks}ms between clicks)...")

            for comp in components:
                try:
                    # Scroll the first matching element into view
                    first_el = await page.query_selector(comp["selector"])
                    if not first_el:
                        print(f"       Skipping {comp['label']}: selector not found")
                        continue

                    await first_el.scroll_into_view_if_needed()
                    await page.wait_for_timeout(500)

                    if comp["type"] == "click-each":
                        # Click each matching element one by one
                        elements = await page.query_selector_all(comp["selector"])
                        for i, el in enumerate(elements[:comp["count"]]):
                            is_visible = await el.is_visible()
                            if not is_visible:
                                continue
                            await el.click()
                            await page.wait_for_timeout(pause_between_clicks)
                            print(f"       Clicked {comp['label']} state {i + 1}/{min(len(elements), comp['count'])}")

                    elif comp["type"] == "click-repeat":
                        # Click the same button N times (carousel next)
                        for i in range(comp["count"]):
                            try:
                                el = await page.query_selector(comp["selector"])
                                if el and await el.is_visible():
                                    await el.click()
                                    await page.wait_for_timeout(pause_between_clicks)
                                    print(f"       Clicked {comp['label']} #{i + 1}/{comp['count']}")
                            except Exception:
                                break

                    # Pause after finishing this component
                    await page.wait_for_timeout(500)

                except Exception as e:
                    print(f"       Warning: Error interacting with {comp['label']}: {e}")

        print(f"[5/5] Saving interaction video to {output_path}...")

        # Close page to finalize video
        await page.close()
        await context.close()
        await browser.close()

        # Find the recorded video file
        # Playwright saves it with a random name, we need to rename it
        video_dir = Path(output_path).parent
        video_files = list(video_dir.glob("*.webm"))

        if video_files:
            # Get the most recent video file
            latest_video = max(video_files, key=lambda f: f.stat().st_mtime)

            # Rename to the desired output path
            final_path = Path(output_path)
            if latest_video != final_path:
                latest_video.rename(final_path)

            print(f"\n✅ Interaction video saved to: {final_path}")
            print(f"   Size: {final_path.stat().st_size / 1024:.1f} KB")
            return str(final_path)
        else:
            print("❌ Error: No video file was created")
            return None


def main():
    parser = argparse.ArgumentParser(
        description="Record interactive component state transitions as video"
    )
    parser.add_argument("url", help="URL to record")
    parser.add_argument("output", help="Output video path (e.g., /tmp/interactions.webm)")
    parser.add_argument(
        "--selectors",
        nargs="+",
        help="CSS selectors of interactive elements to click (auto-detect if omitted)"
    )
    parser.add_argument(
        "--pause",
        type=int,
        default=1500,
        help="Milliseconds between clicks (default: 1500)"
    )
    parser.add_argument(
        "--visible",
        action="store_true",
        help="Show browser window (not headless)"
    )

    args = parser.parse_args()

    # Create output directory if needed
    Path(args.output).parent.mkdir(parents=True, exist_ok=True)

    asyncio.run(record_component_interactions(
        url=args.url,
        output_path=args.output,
        selectors=args.selectors,
        pause_between_clicks=args.pause,
        headless=not args.visible
    ))


if __name__ == "__main__":
    main()
