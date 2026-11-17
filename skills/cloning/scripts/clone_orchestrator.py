#!/usr/bin/env python3
"""
Clone Orchestrator v6.0

Deterministic extraction pipeline using Playwright.
Runs ALL phases automatically — nothing can be skipped.

Usage:
    python clone_orchestrator.py https://example.com /tmp/clone-output
    python clone_orchestrator.py https://example.com /tmp/clone-output --no-video
    python clone_orchestrator.py https://example.com /tmp/clone-output --visible
"""

import asyncio
import argparse
import json
import sys
import time
import re
from pathlib import Path
from urllib.parse import urlparse

try:
    from playwright.async_api import async_playwright
except ImportError:
    print("Error: playwright not installed")
    print("Install with: pip install playwright && playwright install chromium")
    sys.exit(1)

# Viewports for multi-viewport capture
VIEWPORTS = [
    {"name": "mobile", "width": 375, "height": 812},
    {"name": "tablet", "width": 768, "height": 1024},
    {"name": "desktop", "width": 1440, "height": 900},
    {"name": "wide", "width": 1920, "height": 1080},
]

# All extraction scripts mapped to output keys
EXTRACTION_SCRIPTS = {
    "frameworks": "detect_frameworks.js",
    "design-tokens": "extract_design_tokens_v4.js",
    "layout": "analyze_layout.js",
    "components": "analyze_components.js",
    "svgs": "extract_svgs.js",
    "html-content": "extract_html_content.js",
    "measurements": "extract_computed_measurements.js",
    "fonts": "extract_font_assets.js",
    "animations": "extract_js_animations.js",
    "animation-map": "map_animations_v4.js",
    "hover-matrix": "capture_hover_matrix.js",
}

SCRIPTS_DIR = Path(__file__).parent


class CloneOrchestrator:
    """Runs the complete website extraction pipeline."""

    def __init__(self, url, output_dir, headless=True, record_video=True):
        self.url = url
        self.output_dir = Path(output_dir)
        self.headless = headless
        self.record_video = record_video
        self.extraction_data = {}
        self.timings = {}

    def setup_dirs(self):
        """Create output directory structure."""
        dirs = [
            self.output_dir / "screenshots" / "sections",
            self.output_dir / "videos",
            self.output_dir / "extraction",
            self.output_dir / "assets" / "images",
            self.output_dir / "assets" / "fonts",
        ]
        for d in dirs:
            d.mkdir(parents=True, exist_ok=True)

    async def navigate(self, page, url=None):
        """Navigate with networkidle fallback for Webflow/Framer sites."""
        target = url or self.url
        try:
            await page.goto(target, wait_until="networkidle", timeout=30000)
        except Exception:
            print("       networkidle timed out, trying commit...")
            try:
                await page.goto(target, wait_until="commit", timeout=90000)
            except Exception:
                print("       commit timed out, using domcontentloaded...")
                await page.goto(target, wait_until="domcontentloaded", timeout=90000)
        # Let fonts, images, and animations settle
        await page.wait_for_timeout(5000)

    async def inject_script(self, page, script_name):
        """Read a JS extraction script from disk and evaluate it in page context."""
        script_path = SCRIPTS_DIR / script_name
        if not script_path.exists():
            print(f"       Warning: {script_name} not found, skipping")
            return None
        script = script_path.read_text()
        try:
            result = await page.evaluate(script)
            # Some scripts return JSON strings, some return objects
            if isinstance(result, str):
                try:
                    return json.loads(result)
                except json.JSONDecodeError:
                    return result
            return result
        except Exception as e:
            print(f"       Warning: {script_name} failed: {e}")
            return None

    # ── Phase 1: Multi-Viewport Screenshots ─────────────────────────

    async def take_screenshots(self, page):
        """Take full-page screenshots at all 4 viewports."""
        print("\n[Phase 1] Multi-viewport screenshots...")
        t = time.time()

        for vp in VIEWPORTS:
            await page.set_viewport_size({"width": vp["width"], "height": vp["height"]})
            await page.wait_for_timeout(500)
            path = self.output_dir / "screenshots" / f"{vp['name']}-full.png"
            await page.screenshot(path=str(path), full_page=True)
            size_kb = path.stat().st_size / 1024
            print(f"       {vp['name']} ({vp['width']}x{vp['height']}): {size_kb:.0f}KB")

        # Reset to desktop for remaining phases
        await page.set_viewport_size({"width": 1440, "height": 900})
        self.timings["screenshots"] = round(time.time() - t, 1)

    # ── Phase 1.75: Section Close-Up Screenshots ────────────────────

    async def take_section_closeups(self, page):
        """Take individual screenshots of each major page section."""
        print("\n[Phase 1.75] Section close-up screenshots...")
        t = time.time()

        sections = await page.evaluate("""
            (() => {
                const secs = [];
                const seen = new Set();
                document.querySelectorAll('section, header, footer, main > div, [class*="section"]').forEach((el, i) => {
                    const rect = el.getBoundingClientRect();
                    if (rect.height < 100 || rect.width < 200) return;
                    const key = Math.round(rect.top) + ':' + Math.round(rect.height);
                    if (seen.has(key)) return;
                    seen.add(key);
                    secs.push({
                        index: secs.length,
                        tag: el.tagName.toLowerCase(),
                        id: el.id || '',
                        className: (el.className || '').toString().split(' ')[0] || '',
                        height: rect.height
                    });
                });
                return secs.slice(0, 15);
            })()
        """)

        count = 0
        for sec in sections:
            if sec["id"]:
                selector = f"#{sec['id']}"
            elif sec["className"]:
                selector = f".{sec['className']}"
            else:
                selector = f"{sec['tag']}:nth-of-type({sec['index'] + 1})"

            label = sec["id"] or sec["className"] or sec["tag"]
            try:
                el = await page.query_selector(selector)
                if el and await el.is_visible():
                    path = self.output_dir / "screenshots" / "sections" / f"section-{sec['index']:02d}-{label}.png"
                    await el.screenshot(path=str(path))
                    print(f"       {path.name}")
                    count += 1
            except Exception:
                pass

        print(f"       {count} sections captured")
        self.timings["section_closeups"] = round(time.time() - t, 1)

    # ── Phase 1.25a: Scroll Video Recording ─────────────────────────

    async def record_scroll_video(self, browser):
        """Record a smooth scroll from top to bottom."""
        print("\n[Phase 1.25a] Recording scroll video...")
        t = time.time()

        context = await browser.new_context(
            viewport={"width": 1440, "height": 900},
            device_scale_factor=2,
            record_video_dir=str(self.output_dir / "videos"),
            record_video_size={"width": 1440, "height": 900},
        )
        page = await context.new_page()
        await self.navigate(page)

        page_height = await page.evaluate("document.body.scrollHeight")
        scroll_duration = 10  # seconds
        total_steps = scroll_duration * 60  # ~60fps
        scroll_step = page_height / total_steps

        for i in range(int(total_steps)):
            await page.evaluate(f"window.scrollTo(0, {int(scroll_step * i)})")
            await page.wait_for_timeout(16)
            if i > 0 and i % (total_steps // 4) == 0:
                print(f"       Scroll: {int((i / total_steps) * 100)}%")

        # Pause at bottom for final animations
        await page.wait_for_timeout(1000)

        await page.close()
        await context.close()

        self._rename_latest_video("scroll-recording.webm")
        self.timings["scroll_video"] = round(time.time() - t, 1)

    # ── Phase 1.25b: Interaction Video Recording ────────────────────

    async def record_interaction_video(self, browser):
        """Record clicking through tabs, accordions, steps, carousels."""
        print("\n[Phase 1.25b] Recording interaction video...")
        t = time.time()

        context = await browser.new_context(
            viewport={"width": 1440, "height": 900},
            device_scale_factor=2,
            record_video_dir=str(self.output_dir / "videos"),
            record_video_size={"width": 1440, "height": 900},
        )
        page = await context.new_page()
        await self.navigate(page)

        # Auto-detect interactive components
        components = await page.evaluate("""
            (() => {
                const comps = [];
                // Tabs
                const tabs = document.querySelectorAll('[role="tab"], [data-tab], .tab-btn, .tab-trigger');
                if (tabs.length >= 2)
                    comps.push({selector: '[role="tab"], [data-tab], .tab-btn, .tab-trigger', type: 'tabs', count: tabs.length});
                // Accordions
                const acc = document.querySelectorAll('button[aria-expanded], details > summary, [class*="accordion"]');
                if (acc.length >= 2)
                    comps.push({selector: 'button[aria-expanded], details > summary', type: 'accordion', count: Math.min(acc.length, 6)});
                // Carousel arrows
                const arrows = document.querySelectorAll('[class*="arrow"], [class*="next"], [class*="prev"], .slick-next, .swiper-button-next');
                if (arrows.length >= 1)
                    comps.push({selector: '[class*="next"], .slick-next, .swiper-button-next', type: 'carousel', count: Math.min(arrows.length, 5)});
                return comps;
            })()
        """)

        if components:
            print(f"       Found {len(components)} interactive component types")
            for comp in components:
                try:
                    elements = await page.query_selector_all(comp["selector"])
                    for i, el in enumerate(elements[:comp["count"]]):
                        if await el.is_visible():
                            await el.scroll_into_view_if_needed()
                            await page.wait_for_timeout(300)
                            await el.click()
                            await page.wait_for_timeout(1500)
                            print(f"       {comp['type']} state {i + 1}/{min(len(elements), comp['count'])}")
                except Exception as e:
                    print(f"       Warning: {comp['type']} interaction failed: {e}")
        else:
            print("       No interactive components found, doing slow scroll")
            page_height = await page.evaluate("document.body.scrollHeight")
            for i in range(200):
                await page.evaluate(f"window.scrollTo(0, {int((page_height / 200) * i)})")
                await page.wait_for_timeout(25)

        await page.wait_for_timeout(1000)
        await page.close()
        await context.close()

        self._rename_latest_video("interaction-recording.webm")
        self.timings["interaction_video"] = round(time.time() - t, 1)

    # ── Phase 1.25c: Hover Video Recording ──────────────────────────

    async def record_hover_video(self, browser):
        """Record hover states on buttons, links, cards."""
        print("\n[Phase 1.25c] Recording hover video...")
        t = time.time()

        context = await browser.new_context(
            viewport={"width": 1440, "height": 900},
            device_scale_factor=2,
            record_video_dir=str(self.output_dir / "videos"),
            record_video_size={"width": 1440, "height": 900},
        )
        page = await context.new_page()
        await self.navigate(page)

        hover_selectors = [
            "button",
            "a",
            "[class*='card']",
            "[class*='btn']",
            "nav a",
            "[class*='feature']",
        ]
        hovered = 0
        for selector in hover_selectors:
            try:
                elements = await page.query_selector_all(selector)
                for el in elements[:5]:
                    if await el.is_visible():
                        await el.scroll_into_view_if_needed()
                        await page.wait_for_timeout(200)
                        await el.hover()
                        await page.wait_for_timeout(500)
                        await page.mouse.move(0, 0)
                        await page.wait_for_timeout(200)
                        hovered += 1
            except Exception:
                pass

        print(f"       Hovered {hovered} elements")
        await page.close()
        await context.close()

        self._rename_latest_video("hover-recording.webm")
        self.timings["hover_video"] = round(time.time() - t, 1)

    def _rename_latest_video(self, target_name):
        """Find the most recent .webm in videos/ and rename it."""
        video_dir = self.output_dir / "videos"
        video_files = list(video_dir.glob("*.webm"))
        if video_files:
            latest = max(video_files, key=lambda f: f.stat().st_mtime)
            final_path = video_dir / target_name
            if latest != final_path:
                latest.rename(final_path)
            size_kb = final_path.stat().st_size / 1024
            print(f"       Saved: {target_name} ({size_kb:.0f}KB)")
        else:
            print(f"       Warning: no video file created for {target_name}")

    # ── Phases 0-6.5: Extraction Scripts ────────────────────────────

    async def run_extractions(self, page):
        """Inject and run all JavaScript extraction scripts."""
        print("\n[Phases 0-6.5] Running extraction scripts...")
        t = time.time()

        for key, script_name in EXTRACTION_SCRIPTS.items():
            print(f"       Running {script_name}...")
            result = await self.inject_script(page, script_name)
            if result is not None:
                self.extraction_data[key] = result
                out_path = self.output_dir / "extraction" / f"{key}.json"
                with open(out_path, "w") as f:
                    json.dump(result, f, indent=2, default=str)
                print(f"         -> {key}.json saved")
            else:
                print(f"         -> {key}: failed or empty")

        self.timings["extractions"] = round(time.time() - t, 1)

    # ── Phase 1.5: Asset Downloading ────────────────────────────────

    async def download_assets(self, page):
        """Download images and font files using the browser context."""
        print("\n[Phase 1.5] Downloading assets...")
        t = time.time()

        # ── Images ──
        image_data = await page.evaluate("""
            (() => {
                const imgs = [...document.querySelectorAll('img')]
                    .filter(img => {
                        const rect = img.getBoundingClientRect();
                        return (rect.width > 50 || rect.height > 50) && img.src && !img.src.startsWith('data:');
                    })
                    .map(img => img.src);

                const bgs = [...document.querySelectorAll('*')]
                    .map(el => {
                        const bg = getComputedStyle(el).backgroundImage;
                        if (bg && bg !== 'none' && !bg.includes('data:')) {
                            const match = bg.match(/url\\(['"]?(.*?)['"]?\\)/);
                            return match ? match[1] : null;
                        }
                        return null;
                    })
                    .filter(Boolean);

                return [...new Set([...imgs, ...bgs])];
            })()
        """)

        downloaded = 0
        for url in (image_data or [])[:100]:
            try:
                parsed = urlparse(url)
                ext = Path(parsed.path).suffix or ".png"
                name = Path(parsed.path).stem or f"image-{downloaded}"
                name = re.sub(r"[^\w\-.]", "_", name)[:60]
                out_path = self.output_dir / "assets" / "images" / f"{name}{ext}"
                if not out_path.exists():
                    response = await page.request.get(url)
                    if response.ok:
                        out_path.write_bytes(await response.body())
                        downloaded += 1
            except Exception:
                pass

        print(f"       Downloaded {downloaded} images")

        # ── Fonts ──
        font_data = self.extraction_data.get("fonts", {})
        font_urls = []
        if isinstance(font_data, dict):
            for face in font_data.get("fontFaces", font_data.get("fonts", [])):
                if isinstance(face, dict):
                    sources = face.get("sources", face.get("src", []))
                    if isinstance(sources, list):
                        for src in sources:
                            furl = src.get("url", src) if isinstance(src, dict) else src
                            if isinstance(furl, str) and furl.startswith("http"):
                                font_urls.append(furl)

        font_count = 0
        for url in font_urls[:20]:
            try:
                parsed = urlparse(url)
                name = Path(parsed.path).name
                out_path = self.output_dir / "assets" / "fonts" / name
                if not out_path.exists():
                    response = await page.request.get(url)
                    if response.ok:
                        out_path.write_bytes(await response.body())
                        font_count += 1
            except Exception:
                pass

        print(f"       Downloaded {font_count} fonts")
        self.timings["assets"] = round(time.time() - t, 1)

    # ── Full Page HTML ──────────────────────────────────────────────

    async def extract_full_html(self, page):
        """Save the complete rendered HTML."""
        print("\n[HTML] Extracting full page source...")
        html = await page.content()
        html_path = self.output_dir / "full-page.html"
        html_path.write_text(html)
        print(f"       Saved full-page.html ({len(html) / 1024:.0f}KB)")

    # ── Clone Contract ──────────────────────────────────────────────

    def generate_clone_contract(self):
        """Generate clone contract JSON from all extraction data."""
        print("\n[Contract] Generating clone contract...")

        html_content = self.extraction_data.get("html-content", {})
        frameworks = self.extraction_data.get("frameworks", {})

        sections = html_content.get("sections", []) if isinstance(html_content, dict) else []

        images_dir = self.output_dir / "assets" / "images"
        fonts_dir = self.output_dir / "assets" / "fonts"
        image_count = len(list(images_dir.glob("*"))) if images_dir.exists() else 0
        font_count = len(list(fonts_dir.glob("*"))) if fonts_dir.exists() else 0

        contract = {
            "url": self.url,
            "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ"),
            "expected_sections": len(sections),
            "expected_assets": {
                "images": image_count,
                "fonts": font_count,
            },
            "expected_animations": {
                "library": frameworks.get("animation", "css") if isinstance(frameworks, dict) else "css",
                "scroll_triggered": True,
                "hover_states": True,
            },
            "thresholds": {
                "layout_fidelity": 90,
                "asset_fidelity": 95,
                "animation_fidelity": 85,
                "content_fidelity": 95,
                "overall": 90,
            },
            "extraction_phases_completed": list(self.extraction_data.keys()),
            "timings": self.timings,
        }

        contract_path = self.output_dir / "clone-contract.json"
        contract_path.write_text(json.dumps(contract, indent=2))
        print(f"       Contract saved: {len(contract['extraction_phases_completed'])} phases completed")

    # ── Main Pipeline ───────────────────────────────────────────────

    async def run(self):
        """Run the complete extraction pipeline."""
        print(f"{'=' * 50}")
        print(f"  Clone Orchestrator v6.0")
        print(f"  URL: {self.url}")
        print(f"  Output: {self.output_dir}")
        print(f"  Video: {'yes' if self.record_video else 'no'}")
        print(f"  Headless: {self.headless}")
        print(f"{'=' * 50}")

        start = time.time()
        self.setup_dirs()

        async with async_playwright() as p:
            browser = await p.chromium.launch(headless=self.headless)

            # ── Main context (no video) for screenshots + extraction ──
            main_context = await browser.new_context(
                viewport={"width": 1440, "height": 900},
                device_scale_factor=2,
                user_agent="Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36",
            )
            page = await main_context.new_page()

            print("\n[Navigate] Loading page...")
            await self.navigate(page)
            title = await page.title()
            print(f"       Page loaded: {title}")

            # Phase 1: Multi-viewport screenshots
            await self.take_screenshots(page)

            # Phase 1.75: Section close-ups
            await self.take_section_closeups(page)

            # Phases 0-6.5: All extraction scripts
            await self.run_extractions(page)

            # Phase 1.5: Asset downloading
            await self.download_assets(page)

            # Full page HTML
            await self.extract_full_html(page)

            await main_context.close()

            # ── Video recordings (separate contexts) ──
            if self.record_video:
                await self.record_scroll_video(browser)
                await self.record_interaction_video(browser)
                await self.record_hover_video(browser)
            else:
                print("\n[Video] Skipped (--no-video)")

            await browser.close()

        # Generate clone contract
        self.generate_clone_contract()

        # ── Summary ──
        elapsed = time.time() - start
        screenshot_count = len(list((self.output_dir / "screenshots").rglob("*.png")))
        video_count = len(list((self.output_dir / "videos").glob("*.webm")))
        asset_count = len(list((self.output_dir / "assets").rglob("*.*")))

        print(f"\n{'=' * 50}")
        print(f"  EXTRACTION COMPLETE in {elapsed:.1f}s")
        print(f"  Output:       {self.output_dir}")
        print(f"  Screenshots:  {screenshot_count}")
        print(f"  Videos:       {video_count}")
        print(f"  Extractions:  {len(self.extraction_data)}")
        print(f"  Assets:       {asset_count}")
        print(f"{'=' * 50}")


def main():
    parser = argparse.ArgumentParser(
        description="Clone Orchestrator v6.0 — deterministic extraction pipeline"
    )
    parser.add_argument("url", help="URL to clone")
    parser.add_argument("output", help="Output directory path")
    parser.add_argument("--no-video", action="store_true", help="Skip video recording (faster)")
    parser.add_argument("--visible", action="store_true", help="Show browser window")

    args = parser.parse_args()

    orchestrator = CloneOrchestrator(
        url=args.url,
        output_dir=args.output,
        headless=not args.visible,
        record_video=not args.no_video,
    )
    asyncio.run(orchestrator.run())


if __name__ == "__main__":
    main()
