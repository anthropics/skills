#!/usr/bin/env python3
"""
Multi-Viewport Screenshot Capture (v4.0)

Captures screenshots at multiple viewport sizes to show responsive design.
Uses 2x DPI for Retina-quality images that Gemini can analyze in detail.

Requirements:
    pip install playwright
    playwright install chromium

Usage:
    python capture_multi_viewport.py https://example.com /output/folder

What it captures:
    - Mobile (375x812) - iPhone-sized
    - Tablet (768x1024) - iPad-sized
    - Desktop (1440x900) - Standard desktop
    - Wide (1920x1080) - Full HD

Each viewport is captured at 2x DPI for maximum detail.
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


# Viewport configurations
VIEWPORTS = [
    {
        'name': 'mobile',
        'width': 375,
        'height': 812,
        'device_scale_factor': 2,
        'is_mobile': True,
        'has_touch': True,
        'user_agent': 'Mozilla/5.0 (iPhone; CPU iPhone OS 16_0 like Mac OS X) AppleWebKit/605.1.15'
    },
    {
        'name': 'tablet',
        'width': 768,
        'height': 1024,
        'device_scale_factor': 2,
        'is_mobile': True,
        'has_touch': True,
        'user_agent': 'Mozilla/5.0 (iPad; CPU OS 16_0 like Mac OS X) AppleWebKit/605.1.15'
    },
    {
        'name': 'desktop',
        'width': 1440,
        'height': 900,
        'device_scale_factor': 2,
        'is_mobile': False,
        'has_touch': False,
        'user_agent': None  # Use default
    },
    {
        'name': 'wide',
        'width': 1920,
        'height': 1080,
        'device_scale_factor': 2,
        'is_mobile': False,
        'has_touch': False,
        'user_agent': None
    }
]


async def capture_viewport(
    browser,
    url: str,
    viewport: dict,
    output_folder: Path,
    full_page: bool = True
) -> str:
    """
    Capture a screenshot at a specific viewport size.

    Args:
        browser: Playwright browser instance
        url: URL to capture
        viewport: Viewport configuration dict
        output_folder: Where to save screenshots
        full_page: Whether to capture full page or just viewport

    Returns:
        Path to the saved screenshot
    """
    name = viewport['name']
    print(f"  [{name}] Creating context at {viewport['width']}x{viewport['height']} @{viewport['device_scale_factor']}x")

    context_opts = {
        'viewport': {
            'width': viewport['width'],
            'height': viewport['height']
        },
        'device_scale_factor': viewport['device_scale_factor'],
        'is_mobile': viewport['is_mobile'],
        'has_touch': viewport['has_touch'],
    }

    if viewport['user_agent']:
        context_opts['user_agent'] = viewport['user_agent']

    context = await browser.new_context(**context_opts)
    page = await context.new_page()

    try:
        print(f"  [{name}] Loading page...")
        await page.goto(url, wait_until='networkidle', timeout=60000)

        # Wait for any animations to settle
        await page.wait_for_timeout(2000)

        # Get page dimensions
        dimensions = await page.evaluate("""
            () => ({
                scrollHeight: document.body.scrollHeight,
                viewportHeight: window.innerHeight,
                scrollWidth: document.body.scrollWidth,
                viewportWidth: window.innerWidth
            })
        """)
        print(f"  [{name}] Page dimensions: {dimensions['scrollWidth']}x{dimensions['scrollHeight']}")

        # Capture screenshot
        output_path = output_folder / f"viewport-{name}.png"

        if full_page:
            await page.screenshot(path=str(output_path), full_page=True)
        else:
            await page.screenshot(path=str(output_path))

        file_size = output_path.stat().st_size / 1024
        print(f"  [{name}] Saved: {output_path.name} ({file_size:.1f} KB)")

        return str(output_path)

    finally:
        await context.close()


async def capture_all_viewports(
    url: str,
    output_folder: str,
    viewports: list = None,
    full_page: bool = True,
    headless: bool = True
) -> dict:
    """
    Capture screenshots at all viewport sizes.

    Args:
        url: URL to capture
        output_folder: Where to save screenshots
        viewports: List of viewport configs (default: all standard viewports)
        full_page: Whether to capture full page
        headless: Run browser without GUI

    Returns:
        Dictionary with viewport names as keys and paths as values
    """
    if viewports is None:
        viewports = VIEWPORTS

    output_path = Path(output_folder)
    output_path.mkdir(parents=True, exist_ok=True)

    print(f"Capturing {len(viewports)} viewports from: {url}")
    print(f"Output folder: {output_path}")
    print()

    results = {}

    async with async_playwright() as p:
        browser = await p.chromium.launch(headless=headless)

        for viewport in viewports:
            try:
                path = await capture_viewport(
                    browser=browser,
                    url=url,
                    viewport=viewport,
                    output_folder=output_path,
                    full_page=full_page
                )
                results[viewport['name']] = path
            except Exception as e:
                print(f"  [{viewport['name']}] Error: {e}")
                results[viewport['name']] = None

        await browser.close()

    print()
    print(f"Captured {len([v for v in results.values() if v])} of {len(viewports)} viewports")

    return results


async def capture_scroll_sequence(
    url: str,
    output_folder: str,
    viewport_name: str = 'desktop',
    scroll_overlap: float = 0.2,
    headless: bool = True
) -> list:
    """
    Capture a sequence of scroll screenshots for a single viewport.

    This is used for the full-page stitch that Gemini uses to understand
    the complete page layout.

    Args:
        url: URL to capture
        output_folder: Where to save screenshots
        viewport_name: Which viewport to use ('mobile', 'tablet', 'desktop', 'wide')
        scroll_overlap: Overlap between screenshots (0.0 to 0.5)
        headless: Run browser without GUI

    Returns:
        List of screenshot paths
    """
    viewport = next(v for v in VIEWPORTS if v['name'] == viewport_name)

    output_path = Path(output_folder)
    output_path.mkdir(parents=True, exist_ok=True)

    print(f"Capturing scroll sequence at {viewport['width']}x{viewport['height']}")

    screenshots = []

    async with async_playwright() as p:
        browser = await p.chromium.launch(headless=headless)

        context = await browser.new_context(
            viewport={
                'width': viewport['width'],
                'height': viewport['height']
            },
            device_scale_factor=viewport['device_scale_factor'],
            is_mobile=viewport['is_mobile'],
        )

        page = await context.new_page()
        await page.goto(url, wait_until='networkidle', timeout=60000)
        await page.wait_for_timeout(2000)

        # Get dimensions
        dimensions = await page.evaluate("""
            () => ({
                scrollHeight: document.body.scrollHeight,
                viewportHeight: window.innerHeight
            })
        """)

        scroll_height = dimensions['scrollHeight']
        viewport_height = dimensions['viewportHeight']
        scroll_step = int(viewport_height * (1 - scroll_overlap))

        print(f"Page height: {scroll_height}px, step: {scroll_step}px")

        # Capture scroll sequence
        current_scroll = 0
        index = 1

        while current_scroll < scroll_height:
            # Scroll to position
            await page.evaluate(f"window.scrollTo(0, {current_scroll})")
            await page.wait_for_timeout(500)

            # Capture
            filename = f"{index:02d}-scroll-{current_scroll}.png"
            filepath = output_path / filename
            await page.screenshot(path=str(filepath))

            screenshots.append(str(filepath))
            print(f"  Captured {filename}")

            current_scroll += scroll_step
            index += 1

        await context.close()
        await browser.close()

    print(f"Captured {len(screenshots)} scroll screenshots")
    return screenshots


def main():
    parser = argparse.ArgumentParser(
        description="Capture multi-viewport screenshots for website cloning"
    )
    parser.add_argument("url", help="URL to capture")
    parser.add_argument("output", help="Output folder for screenshots")
    parser.add_argument(
        "--viewports",
        nargs="+",
        choices=['mobile', 'tablet', 'desktop', 'wide', 'all'],
        default=['all'],
        help="Which viewports to capture (default: all)"
    )
    parser.add_argument(
        "--viewport-only",
        action="store_true",
        help="Only capture viewport (not full page)"
    )
    parser.add_argument(
        "--visible",
        action="store_true",
        help="Show browser window (not headless)"
    )
    parser.add_argument(
        "--scroll-sequence",
        action="store_true",
        help="Capture scroll sequence instead of viewports"
    )
    parser.add_argument(
        "--scroll-viewport",
        choices=['mobile', 'tablet', 'desktop', 'wide'],
        default='desktop',
        help="Viewport to use for scroll sequence (default: desktop)"
    )

    args = parser.parse_args()

    # Create output directory
    Path(args.output).mkdir(parents=True, exist_ok=True)

    if args.scroll_sequence:
        asyncio.run(capture_scroll_sequence(
            url=args.url,
            output_folder=args.output,
            viewport_name=args.scroll_viewport,
            headless=not args.visible
        ))
    else:
        # Filter viewports if specified
        if 'all' in args.viewports:
            viewports = VIEWPORTS
        else:
            viewports = [v for v in VIEWPORTS if v['name'] in args.viewports]

        asyncio.run(capture_all_viewports(
            url=args.url,
            output_folder=args.output,
            viewports=viewports,
            full_page=not args.viewport_only,
            headless=not args.visible
        ))


if __name__ == "__main__":
    main()
