#!/usr/bin/env python3
"""
Scraping Toolkit - Generates Playwright scraping script skeletons.

Takes a URL pattern and CSS selectors as input and produces a ready-to-run
Playwright scraping script with pagination support, error handling, and
anti-detection patterns baked in.

No external dependencies - uses only Python standard library.
"""

import argparse
import json
import os
import sys
import textwrap
from datetime import datetime


def build_scraping_script(url, selectors, paginate=False, output_format="script"):
    """Build a Playwright scraping script from the given parameters."""

    selector_list = [s.strip() for s in selectors.split(",") if s.strip()]
    if not selector_list:
        return None, "No valid selectors provided."

    field_names = []
    for sel in selector_list:
        # Derive field name from selector: .product-title -> product_title
        name = sel.strip("#.[]()>:+~ ")
        name = name.replace("-", "_").replace(" ", "_").replace(".", "_")
        # Remove non-alphanumeric
        name = "".join(c if c.isalnum() or c == "_" else "" for c in name)
        if not name:
            name = f"field_{len(field_names)}"
        field_names.append(name)

    field_map = dict(zip(field_names, selector_list))

    if output_format == "json":
        config = {
            "url": url,
            "selectors": field_map,
            "pagination": {
                "enabled": paginate,
                "next_selector": "a:has-text('Next'), button:has-text('Next')",
                "max_pages": 50,
            },
            "anti_detection": {
                "random_delay_ms": [800, 2500],
                "user_agent_rotation": True,
                "viewport": {"width": 1920, "height": 1080},
            },
            "output": {
                "format": "jsonl",
                "deduplicate_by": field_names[0] if field_names else None,
            },
            "generated_at": datetime.now().isoformat(),
        }
        return config, None

    # Build Python script
    fields_dict_str = "{\n"
    for name, sel in field_map.items():
        fields_dict_str += f'        "{name}": "{sel}",\n'
    fields_dict_str += "    }"

    pagination_block = ""
    if paginate:
        pagination_block = textwrap.dedent("""\

        # --- Pagination ---
        async def scrape_all_pages(page, container, fields, next_sel, max_pages=50):
            all_items = []
            for page_num in range(max_pages):
                print(f"Scraping page {page_num + 1}...")
                items = await extract_items(page, container, fields)
                all_items.extend(items)

                next_btn = page.locator(next_sel)
                if await next_btn.count() == 0:
                    break
                try:
                    is_disabled = await next_btn.is_disabled()
                except Exception:
                    is_disabled = True
                if is_disabled:
                    break

                await next_btn.click()
                await page.wait_for_load_state("networkidle")
                await asyncio.sleep(random.uniform(0.8, 2.5))

            return all_items
""")

    main_call = "scrape_all_pages(page, CONTAINER, FIELDS, NEXT_SELECTOR)" if paginate else "extract_items(page, CONTAINER, FIELDS)"

    script = textwrap.dedent(f'''\
#!/usr/bin/env python3
"""
Auto-generated Playwright scraping script.
Target: {url}
Generated: {datetime.now().isoformat()}

Requirements:
    pip install playwright
    playwright install chromium
"""

import asyncio
import json
import random
from playwright.async_api import async_playwright

# --- Configuration ---
URL = "{url}"
CONTAINER = "body"  # Adjust to the repeating item container selector
FIELDS = {fields_dict_str}
NEXT_SELECTOR = "a:has-text('Next'), button:has-text('Next')"

USER_AGENTS = [
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
]


async def extract_items(page, container_selector, field_map):
    """Extract structured data from repeating elements."""
    items = []
    cards = await page.query_selector_all(container_selector)
    for card in cards:
        item = {{}}
        for name, selector in field_map.items():
            el = await card.query_selector(selector)
            if el:
                item[name] = (await el.text_content() or "").strip()
            else:
                item[name] = None
        items.append(item)
    return items

{pagination_block}
async def main():
    async with async_playwright() as p:
        browser = await p.chromium.launch(headless=True)
        context = await browser.new_context(
            viewport={{"width": 1920, "height": 1080}},
            user_agent=random.choice(USER_AGENTS),
        )
        page = await context.new_page()

        # Remove WebDriver flag
        await page.add_init_script(
            "Object.defineProperty(navigator, \'webdriver\', {{get: () => undefined}});"
        )

        print(f"Navigating to {{URL}}...")
        await page.goto(URL, wait_until="networkidle")

        data = await {main_call}
        print(json.dumps(data, indent=2, ensure_ascii=False))

        await browser.close()


if __name__ == "__main__":
    asyncio.run(main())
''')

    return script, None


def main():
    parser = argparse.ArgumentParser(
        description="Generate Playwright scraping script skeletons from URL and selectors.",
        epilog=(
            "Examples:\n"
            "  %(prog)s --url https://example.com/products --selectors '.title,.price,.rating'\n"
            "  %(prog)s --url https://example.com/search --selectors '.name,.desc' --paginate\n"
            "  %(prog)s --url https://example.com --selectors '.item' --json\n"
            "  %(prog)s --url https://example.com --selectors '.item' --output scraper.py\n"
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument(
        "--url",
        required=True,
        help="Target URL to scrape",
    )
    parser.add_argument(
        "--selectors",
        required=True,
        help="Comma-separated CSS selectors for data fields (e.g. '.title,.price,.rating')",
    )
    parser.add_argument(
        "--paginate",
        action="store_true",
        default=False,
        help="Include pagination handling in generated script",
    )
    parser.add_argument(
        "--output",
        help="Output file path (default: stdout)",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        dest="json_output",
        default=False,
        help="Output JSON configuration instead of Python script",
    )

    args = parser.parse_args()

    output_format = "json" if args.json_output else "script"
    result, error = build_scraping_script(
        url=args.url,
        selectors=args.selectors,
        paginate=args.paginate,
        output_format=output_format,
    )

    if error:
        print(f"Error: {error}", file=sys.stderr)
        sys.exit(2)

    if args.json_output:
        output_text = json.dumps(result, indent=2)
    else:
        output_text = result

    if args.output:
        output_path = os.path.abspath(args.output)
        with open(output_path, "w") as f:
            f.write(output_text)
        if not args.json_output:
            os.chmod(output_path, 0o755)
        print(f"Written to {output_path}", file=sys.stderr)
        sys.exit(0)
    else:
        print(output_text)
        sys.exit(0)


if __name__ == "__main__":
    main()
