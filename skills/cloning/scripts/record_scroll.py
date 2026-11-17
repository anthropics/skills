#!/usr/bin/env python3
"""
Scroll Animation Video Recorder (v4.0)

Records a video of a webpage scrolling from top to bottom.
This allows Gemini to "see" scroll-triggered animations.

Requirements:
    pip install playwright
    playwright install chromium

Usage:
    python record_scroll.py https://escape.cafe /tmp/scroll-recording.webm

What it captures:
    - Full page scroll (slow, ~10 seconds)
    - All scroll-triggered animations
    - Parallax effects
    - Staggered reveals
    - Any motion that only appears on scroll

Why this matters:
    Static screenshots cannot capture motion. This video gives
    Gemini the visual context it needs to implement scroll animations
    with the correct timing and effects.
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


async def record_scroll_animation(
    url: str,
    output_path: str,
    scroll_duration: int = 10,
    viewport_width: int = 1440,
    viewport_height: int = 900,
    device_scale_factor: int = 2,
    headless: bool = True
):
    """
    Record a video of smooth scrolling through a webpage.

    Args:
        url: The webpage URL to record
        output_path: Where to save the .webm video file
        scroll_duration: How long the scroll should take (seconds)
        viewport_width: Browser viewport width
        viewport_height: Browser viewport height
        device_scale_factor: DPI scale (2 for Retina)
        headless: Run browser without GUI (True for server/CI)

    Returns:
        Path to the recorded video file
    """
    print(f"[1/5] Launching browser...")

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
            # Fallback: networkidle times out on sites with persistent connections (Webflow, etc.)
            print("       networkidle timed out, using domcontentloaded fallback...")
            await page.goto(url, wait_until="domcontentloaded", timeout=30000)

        # Wait for page to fully render (fonts, images, animations init)
        await page.wait_for_timeout(3000)

        print(f"[3/5] Getting page dimensions...")
        # Get the full page height
        page_height = await page.evaluate("document.body.scrollHeight")
        print(f"       Page height: {page_height}px")

        print(f"[4/5] Recording scroll animation ({scroll_duration}s)...")

        # Calculate scroll step for smooth animation
        # We want to complete the scroll in `scroll_duration` seconds
        # at ~60fps, that's scroll_duration * 60 steps
        total_steps = scroll_duration * 60
        scroll_step = page_height / total_steps
        delay_per_step = 1000 / 60  # ~16.67ms per frame

        # Smooth scroll from top to bottom
        for i in range(int(total_steps)):
            await page.evaluate(f"window.scrollTo(0, {int(scroll_step * i)})")
            await page.wait_for_timeout(delay_per_step)

            # Progress indicator every 25%
            if i > 0 and i % (total_steps // 4) == 0:
                progress = (i / total_steps) * 100
                print(f"       Scroll progress: {progress:.0f}%")

        # Wait at bottom for any final animations
        await page.wait_for_timeout(1000)

        # Scroll back to top (optional - shows reverse animations)
        print("[4/5] Scrolling back to top...")
        await page.evaluate("window.scrollTo(0, 0)")
        await page.wait_for_timeout(1000)

        print(f"[5/5] Saving video to {output_path}...")

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

            print(f"\n✅ Video saved to: {final_path}")
            print(f"   Size: {final_path.stat().st_size / 1024:.1f} KB")
            return str(final_path)
        else:
            print("❌ Error: No video file was created")
            return None


async def record_hover_interactions(
    url: str,
    output_path: str,
    elements_to_hover: list = None,
    headless: bool = True
):
    """
    Record a video of hovering over interactive elements.

    This captures hover state transitions that can't be shown in screenshots.

    Args:
        url: The webpage URL
        output_path: Where to save the .webm video
        elements_to_hover: CSS selectors of elements to hover over
        headless: Run browser without GUI
    """
    if elements_to_hover is None:
        elements_to_hover = [
            "button",
            "a.btn",
            ".product-card",
            ".card",
            ".nav-link",
            ".social-icon",
            "[class*='card']",
            "[class*='btn']"
        ]

    print(f"[1/4] Launching browser for hover recording...")

    async with async_playwright() as p:
        browser = await p.chromium.launch(headless=headless)

        context = await browser.new_context(
            viewport={"width": 1440, "height": 900},
            device_scale_factor=2,
            record_video_dir=str(Path(output_path).parent),
            record_video_size={"width": 1440, "height": 900}
        )

        page = await context.new_page()

        print(f"[2/4] Navigating to {url}...")
        try:
            await page.goto(url, wait_until="networkidle", timeout=15000)
        except Exception:
            print("       networkidle timed out, using domcontentloaded fallback...")
            await page.goto(url, wait_until="domcontentloaded", timeout=30000)
        await page.wait_for_timeout(3000)

        print(f"[3/4] Recording hover interactions...")

        for selector in elements_to_hover:
            try:
                elements = await page.query_selector_all(selector)
                print(f"       Found {len(elements)} elements matching '{selector}'")

                for el in elements[:5]:  # Limit to 5 per selector
                    # Check if element is visible
                    is_visible = await el.is_visible()
                    if not is_visible:
                        continue

                    # Scroll element into view
                    await el.scroll_into_view_if_needed()
                    await page.wait_for_timeout(300)

                    # Hover over element
                    await el.hover()
                    await page.wait_for_timeout(600)  # Wait for transition

                    # Move away
                    await page.mouse.move(0, 0)
                    await page.wait_for_timeout(300)

            except Exception as e:
                print(f"       Warning: Could not hover on '{selector}': {e}")

        print(f"[4/4] Saving hover video to {output_path}...")

        await page.close()
        await context.close()
        await browser.close()

        # Find and rename the video file
        video_dir = Path(output_path).parent
        video_files = list(video_dir.glob("*.webm"))

        if video_files:
            latest_video = max(video_files, key=lambda f: f.stat().st_mtime)
            final_path = Path(output_path)
            if latest_video != final_path:
                latest_video.rename(final_path)

            print(f"\n✅ Hover video saved to: {final_path}")
            return str(final_path)

        return None


def main():
    parser = argparse.ArgumentParser(
        description="Record scroll and hover animations from a webpage"
    )
    parser.add_argument("url", help="URL to record")
    parser.add_argument("output", help="Output video path (e.g., /tmp/scroll.webm)")
    parser.add_argument(
        "--duration",
        type=int,
        default=10,
        help="Scroll duration in seconds (default: 10)"
    )
    parser.add_argument(
        "--hover",
        action="store_true",
        help="Record hover interactions instead of scroll"
    )
    parser.add_argument(
        "--visible",
        action="store_true",
        help="Show browser window (not headless)"
    )
    parser.add_argument(
        "--retina",
        action="store_true",
        default=True,
        help="Use 2x DPI for Retina quality (default: True)"
    )

    args = parser.parse_args()

    # Create output directory if needed
    Path(args.output).parent.mkdir(parents=True, exist_ok=True)

    if args.hover:
        asyncio.run(record_hover_interactions(
            url=args.url,
            output_path=args.output,
            headless=not args.visible
        ))
    else:
        asyncio.run(record_scroll_animation(
            url=args.url,
            output_path=args.output,
            scroll_duration=args.duration,
            device_scale_factor=2 if args.retina else 1,
            headless=not args.visible
        ))


if __name__ == "__main__":
    main()
