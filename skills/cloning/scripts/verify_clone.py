#!/usr/bin/env python3
"""
Clone Verification Script v6.1

Visually compares original website with clone by taking matching screenshots.
Includes scroll-state comparison for detecting missing animations.
Used in the self-healing loop: generate -> verify -> fix -> verify -> repeat.

Usage:
    python verify_clone.py https://original.com http://localhost:3001 /tmp/verify-output
    python verify_clone.py https://original.com http://localhost:3001 /tmp/verify-output --iteration 2
    python verify_clone.py https://original.com http://localhost:3001 /tmp/verify-output --quick
"""

import asyncio
import argparse
import json
import sys
import time
from pathlib import Path

try:
    from playwright.async_api import async_playwright
except ImportError:
    print("Error: playwright not installed")
    print("Install with: pip install playwright && playwright install chromium")
    sys.exit(1)


async def navigate_safe(page, url):
    """Navigate with networkidle fallback for Webflow/Framer sites."""
    try:
        await page.goto(url, wait_until="networkidle", timeout=15000)
    except Exception:
        print("       networkidle timed out, using domcontentloaded fallback...")
        await page.goto(url, wait_until="domcontentloaded", timeout=60000)
    await page.wait_for_timeout(3000)


async def capture_site(browser, url, output_dir, label):
    """
    Capture full-page + viewport-section screenshots of a site.
    Returns (sections list, page_height).
    """
    site_dir = output_dir / label
    sections_dir = site_dir / "sections"
    site_dir.mkdir(parents=True, exist_ok=True)
    sections_dir.mkdir(parents=True, exist_ok=True)

    context = await browser.new_context(
        viewport={"width": 1440, "height": 900},
        device_scale_factor=2,
    )
    page = await context.new_page()

    print(f"\n  [{label}] Navigating to {url}...")
    await navigate_safe(page, url)

    # Full-page screenshot
    full_path = site_dir / "full-page.png"
    await page.screenshot(path=str(full_path), full_page=True)
    file_size = full_path.stat().st_size / 1024
    print(f"  [{label}] Full-page screenshot ({file_size:.0f}KB)")

    # Get page dimensions
    page_height = await page.evaluate("document.body.scrollHeight")
    viewport_height = 900

    # Capture viewport-sized sections by scrolling
    sections = []
    num_sections = min(int(page_height / viewport_height) + 1, 15)

    for i in range(num_sections):
        scroll_y = i * viewport_height
        if scroll_y > page_height:
            break

        await page.evaluate(f"window.scrollTo(0, {scroll_y})")
        await page.wait_for_timeout(500)  # Let animations/transitions settle

        section_path = sections_dir / f"section-{i:02d}.png"
        await page.screenshot(path=str(section_path))  # Viewport only
        sections.append({
            "index": i,
            "scroll_y": scroll_y,
            "path": f"{label}/sections/section-{i:02d}.png",
        })

    print(f"  [{label}] {len(sections)} section screenshots captured")

    # Wait 8s and capture again to catch auto-cycling tabs/carousels
    await page.evaluate("window.scrollTo(0, 0)")
    await page.wait_for_timeout(8000)
    waited_path = site_dir / "waited-8s.png"
    await page.screenshot(path=str(waited_path))
    print(f"  [{label}] Waited 8s screenshot captured (auto-cycle detection)")

    await context.close()
    return sections, page_height


async def capture_scroll_states(browser, url, output_dir, label, page_height):
    """
    Capture screenshots at fine-grained scroll positions to compare animation states.
    Takes screenshots at every 25% of viewport height (450px) for granular comparison.
    Catches: partially highlighted words, auto-advanced tabs, sticky elements.
    """
    context = await browser.new_context(
        viewport={"width": 1440, "height": 900},
        device_scale_factor=2,
    )
    page = await context.new_page()
    await navigate_safe(page, url)

    scroll_dir = output_dir / label / "scroll-states"
    scroll_dir.mkdir(parents=True, exist_ok=True)

    # More granular scroll: every 450px (half viewport) instead of 900px
    step_size = 450
    num_steps = min(int(page_height / step_size) + 1, 25)

    states = []
    for i in range(num_steps):
        scroll_y = i * step_size
        if scroll_y > page_height:
            break

        await page.evaluate(f"window.scrollTo(0, {scroll_y})")
        await page.wait_for_timeout(800)  # Wait for scroll animations to trigger

        path = scroll_dir / f"scroll-{i:02d}-y{scroll_y}.png"
        await page.screenshot(path=str(path))
        states.append({
            "index": i,
            "scroll_y": scroll_y,
            "path": f"{label}/scroll-states/scroll-{i:02d}-y{scroll_y}.png",
        })

    print(f"  [{label}] {len(states)} scroll-state screenshots captured")

    await context.close()
    return states


async def verify(original_url, clone_url, output_dir, iteration=1, quick=False):
    """Run the full verification comparison."""
    mode = "quick" if quick else "full (with scroll-state comparison)"
    print(f"\n{'=' * 55}")
    print(f"  Clone Verification — Iteration {iteration} [{mode}]")
    print(f"  Original: {original_url}")
    print(f"  Clone:    {clone_url}")
    print(f"{'=' * 55}")

    output = Path(output_dir)
    output.mkdir(parents=True, exist_ok=True)

    start = time.time()

    async with async_playwright() as p:
        browser = await p.chromium.launch(headless=True)

        # Capture both sites (sections + waited screenshots)
        original_sections, original_height = await capture_site(
            browser, original_url, output, "original"
        )
        clone_sections, clone_height = await capture_site(
            browser, clone_url, output, "clone"
        )

        # Scroll-state comparison (skip in quick mode)
        original_scroll_states = []
        clone_scroll_states = []
        if not quick:
            print("\nCapturing scroll states (animation comparison)...")
            original_scroll_states = await capture_scroll_states(
                browser, original_url, output, "original", original_height
            )
            clone_scroll_states = await capture_scroll_states(
                browser, clone_url, output, "clone", clone_height
            )

        await browser.close()

    # Generate comparison manifest
    manifest = {
        "original_url": original_url,
        "clone_url": clone_url,
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ"),
        "iteration": iteration,
        "quick_mode": quick,
        "duration_seconds": round(time.time() - start, 1),
        "full_page": {
            "original": "original/full-page.png",
            "clone": "clone/full-page.png",
        },
        "waited_screenshots": {
            "original": "original/waited-8s.png",
            "clone": "clone/waited-8s.png",
            "note": "Captured 8s after load — compare with full-page to detect auto-cycling tabs/carousels",
        },
        "sections": [
            {
                "index": s["index"],
                "scroll_y": s["scroll_y"],
                "original": f"original/sections/section-{s['index']:02d}.png",
                "clone": f"clone/sections/section-{s['index']:02d}.png",
            }
            for s in original_sections
        ],
        "section_count": len(original_sections),
    }

    # Add scroll states if captured
    if original_scroll_states:
        manifest["scroll_states"] = [
            {
                "index": s["index"],
                "scroll_y": s["scroll_y"],
                "original": f"original/scroll-states/scroll-{s['index']:02d}-y{s['scroll_y']}.png",
                "clone": f"clone/scroll-states/scroll-{s['index']:02d}-y{s['scroll_y']}.png",
            }
            for s in original_scroll_states
        ]
        manifest["scroll_state_count"] = len(original_scroll_states)

    manifest["instructions"] = (
        "Compare each original/sections/section-XX.png with its matching "
        "clone/sections/section-XX.png. Also compare scroll-states for animation "
        "differences and waited-8s.png for auto-cycling elements. "
        "List EVERY visual difference. Fix the top 3-5, then re-run with --iteration {next}."
    )

    manifest_path = output / "comparison-manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2))

    elapsed = time.time() - start
    scroll_msg = f"  Scroll states: {len(original_scroll_states)}" if not quick else ""
    print(f"\n{'=' * 55}")
    print(f"  Verification complete in {elapsed:.1f}s")
    print(f"  Sections: {len(original_sections)}")
    if scroll_msg:
        print(scroll_msg)
    print(f"  Output:   {output}")
    print(f"")
    print(f"  To compare: read original/sections/section-00.png")
    print(f"              and  clone/sections/section-00.png")
    print(f"              side by side for each section index.")
    if not quick:
        print(f"  Scroll:   compare scroll-states/ for animation diffs")
    print(f"  Auto-cycle: compare waited-8s.png vs full-page.png")
    print(f"{'=' * 55}")

    return manifest


def main():
    parser = argparse.ArgumentParser(
        description="Clone Verification — screenshot comparison for self-healing loop"
    )
    parser.add_argument("original_url", help="Original website URL")
    parser.add_argument("clone_url", help="Clone dev server URL (e.g., http://localhost:3001)")
    parser.add_argument("output", help="Output directory for comparison screenshots")
    parser.add_argument(
        "--iteration", type=int, default=1,
        help="Iteration number for tracking (default: 1)"
    )
    parser.add_argument(
        "--quick", action="store_true",
        help="Quick mode: sections only, no scroll-state comparison"
    )

    args = parser.parse_args()

    asyncio.run(verify(
        original_url=args.original_url,
        clone_url=args.clone_url,
        output_dir=args.output,
        iteration=args.iteration,
        quick=args.quick,
    ))


if __name__ == "__main__":
    main()
