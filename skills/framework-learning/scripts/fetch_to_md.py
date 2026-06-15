#!/usr/bin/env python3
"""
fetch_to_md.py — Fetch and convert top-k ranked pages to clean markdown.

Usage:
  python fetch_to_md.py --topk artifacts/topk.json --out artifacts/topk_pages/

Output:
  artifacts/topk_pages/*.md with clean markdown versions of each top page.
  File names: page_0.md, page_1.md, etc.
"""

import asyncio
import json
import argparse
import os
from pathlib import Path

try:
    from crawl4ai import AsyncWebCrawler, BrowserConfig, CrawlerRunConfig, CacheMode
    from crawl4ai.async_crawler_strategy import AsyncPlaywrightCrawlerStrategy
except ImportError:
    print("ERROR: crawl4ai not installed. Run: pip install crawl4ai")
    exit(1)


async def fetch_and_convert(topk_file: str, out_dir: str) -> None:
    """
    Fetch each URL from topk.json and save as clean markdown.
    """
    with open(topk_file, "r") as f:
        topk = json.load(f)

    os.makedirs(out_dir, exist_ok=True)

    browser_config = BrowserConfig(headless=True, verbose=False)
    run_config = CrawlerRunConfig(
        scraping_strategy=AsyncPlaywrightCrawlerStrategy(),
        cache_mode=CacheMode.ENABLED
    )

    async with AsyncWebCrawler(config=browser_config) as crawler:
        for idx, result in enumerate(topk.get("results", [])):
            url = result["url"]
            title = result["title"]
            score = result["score"]

            print(f"[{idx+1}/{len(topk['results'])}] Fetching: {title}")

            try:
                crawl_result = await crawler.arun(url=url, config=run_config)

                if crawl_result.success and crawl_result.markdown and crawl_result.markdown.raw_markdown.strip():
                    raw_md = crawl_result.markdown.raw_markdown

                    # Attempt to clean boilerplate: remove "Keyboard shortcuts" and initial navigation
                    # This is a heuristic based on the observed pattern in Rust Book documentation
                    lines = raw_md.split('\n')
                    clean_lines = []
                    skip_header_block = False
                    for line in lines:
                        if "## Keyboard shortcuts" in line:
                            skip_header_block = True
                            continue
                        if skip_header_block and (line.startswith("Press `") or line.strip().startswith('1. [')):
                            continue # Still part of the boilerplate navigation links
                        elif skip_header_block and line.strip() == "":
                            # Allow empty lines within boilerplate if it helps transition
                            continue
                        elif skip_header_block and not line.strip():
                            # If we encounter an empty line after header block, it might be the end of boilerplate
                            # or just an empty line before real content. We need a better heuristic.
                            # For now, if we found header block, and this is an empty line, just skip
                            continue
                        elif line.strip() == "" and not skip_header_block:
                            # Keep meaningful empty lines
                            clean_lines.append(line)
                        elif not skip_header_block:
                            # Not skipping, so add the line
                            clean_lines.append(line)
                        else:
                            # End of boilerplate if we hit content that's not empty and not a "Press `" line
                            skip_header_block = False
                            clean_lines.append(line)

                    # A more robust approach: find the first actual heading (H1, H2, etc.) that isn't boilerplate.
                    # Or, split after the first significant content block.
                    # Given the "---" separator we add for metadata, we can try splitting after the first "---"
                    # and then cleaning the raw content.

                    # Let's try splitting by the first major heading (e.g., '# What is Ownership?').
                    # The boilerplate often comes before the actual content heading.
                    clean_raw_markdown = raw_md
                    header_line_index = -1
                    for i, line in enumerate(lines):
                        if line.strip().startswith('#') and not ("Keyboard shortcuts" in line or "The Rust Programming Language" in line or "Source:" in line or "Relevance Score:" in line):
                            header_line_index = i
                            break
                    
                    if header_line_index != -1:
                        clean_raw_markdown = "\n".join(lines[header_line_index:]).strip()
                    else:
                        # Fallback to a simpler split if no clear heading found,
                        # try to skip initial known boilerplate
                        if "## Keyboard shortcuts" in clean_raw_markdown:
                            clean_raw_markdown = clean_raw_markdown.split("## Keyboard shortcuts", 1)[-1]
                            # Remove initial navigation links if still present
                            clean_raw_markdown = "\n".join([
                                l for l in clean_raw_markdown.split('\n') 
                                if not (l.startswith("Press `") or l.strip().startswith('1. ['))
                            ]).strip()


                    # Build markdown with metadata header
                    md_content = f"""# {title}

**Source:** [{url}]({url})  
**Relevance Score:** {score:.2f}

---

{clean_raw_markdown}
"""

                    # Save to file
                    out_file = os.path.join(out_dir, f"page_{idx}.md")
                    with open(out_file, "w", encoding="utf-8") as f:
                        f.write(md_content)

                    print(f"  ✓ Saved to: {out_file}")
                else:
                    print(f"  ✗ Failed to fetch or parse: {url}")
                    if crawl_result.markdown and crawl_result.markdown.raw_markdown:
                        print(f"    Raw Markdown (length {len(crawl_result.markdown.raw_markdown)}):\n{crawl_result.markdown.raw_markdown[:500]}...") # Print first 500 chars
                    elif crawl_result.raw_html:
                        print(f"    Raw HTML (length {len(crawl_result.raw_html)}):\n{crawl_result.raw_html[:500]}...") # Print first 500 chars

            except Exception as e:
                print(f"  ✗ Error fetching {url}: {str(e)[:60]}")


def main():
    parser = argparse.ArgumentParser(
        description="Fetch and convert top-k pages to markdown."
    )
    parser.add_argument(
        "--topk",
        required=True,
        help="Top-k results JSON (from bm25_rank.py)"
    )
    parser.add_argument(
        "--out",
        required=True,
        help="Output directory for markdown files"
    )

    args = parser.parse_args()

    print(f"Fetching top-k pages from: {args.topk}")
    print(f"Output directory: {args.out}\n")

    asyncio.run(fetch_and_convert(args.topk, args.out))

    print(f"\n✓ Conversion complete. Markdown files saved to: {args.out}")


if __name__ == "__main__":
    main()
