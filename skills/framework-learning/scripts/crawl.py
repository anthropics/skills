#!/usr/bin/env python3
"""
crawl.py — Deep crawl documentation from a seed domain using Crawl4AI's BFSDeepCrawlStrategy.

Usage:
  python crawl.py --seed https://docs.example.com/ --out artifacts/discovered.json --max-pages 100

Output:
  artifacts/discovered.json with structure:
  {
    "domain": "docs.example.com",
    "seed_url": "https://docs.example.com/",
    "urls": [
      {
        "url": "https://docs.example.com/guide/intro",
        "title": "Introduction",
        "headings": ["Getting Started", "Installation"],
        "snippet": "Learn the basics...",
        "depth": 0
      },
      ...
    ],
    "crawl_time": "2026-01-11T10:59:00Z",
    "total_discovered": 100
  }
"""

import asyncio
import json
import argparse
import os
from datetime import datetime
from urllib.parse import urlparse

try:
    from crawl4ai import AsyncWebCrawler, BrowserConfig, CrawlerRunConfig, CacheMode
    from crawl4ai.deep_crawling import BFSDeepCrawlStrategy
    from crawl4ai.deep_crawling.filters import FilterChain, DomainFilter
    from crawl4ai.async_crawler_strategy import AsyncPlaywrightCrawlerStrategy
except ImportError:
    print("ERROR: crawl4ai not installed. Run: pip install crawl4ai")
    exit(1)


async def crawl_docs(seed_url: str, max_pages: int = 100, max_depth: int = 3) -> dict:
    """
    Deep crawl documentation from seed_url using Crawl4AI's built-in BFSDeepCrawlStrategy.
    Returns discovered URLs with metadata.
    """
    parsed_seed = urlparse(seed_url)
    domain = parsed_seed.netloc
    scheme = parsed_seed.scheme

    print(f"Starting deep crawl of {domain} (max_depth={max_depth}, max_pages={max_pages})")

    # Create filter to stay within the same domain
    filter_chain = FilterChain([
        DomainFilter(
            allowed_domains=[domain],
            blocked_domains=[]
        )
    ])

    # Configure deep crawl strategy
    deep_crawl_strategy = BFSDeepCrawlStrategy(
        max_depth=max_depth,
        include_external=False,  # Stay within domain
        max_pages=max_pages,
        filter_chain=filter_chain
    )

    # Browser and crawler configuration
    browser_config = BrowserConfig(
        headless=True,
        verbose=False
    )

    run_config = CrawlerRunConfig(
        deep_crawl_strategy=deep_crawl_strategy,
        scraping_strategy=AsyncPlaywrightCrawlerStrategy(),
        cache_mode=CacheMode.ENABLED,
        word_count_threshold=10,
        stream=False,  # Get all results at once
        verbose=True
    )

    discovered = []

    async with AsyncWebCrawler(config=browser_config) as crawler:
        # Run deep crawl (returns list of CrawlResult objects)
        results = await crawler.arun(url=seed_url, config=run_config)

        print(f"\nProcessing {len(results)} crawled pages...")

        for idx, result in enumerate(results, 1):
            if not result.success:
                print(f"  [{idx}/{len(results)}] Failed: {result.url}")
                continue

            print(f"  [{idx}/{len(results)}] Processing: {result.url}")

            # Extract title
            title = ""
            if result.metadata:
                title = result.metadata.get("title", "")

            # Extract headings from markdown
            headings = []
            if result.markdown:
                lines = result.markdown.raw_markdown.split("\n")
                for line in lines[:30]:
                    if line.startswith("#"):
                        heading_text = line.lstrip("#").strip()
                        if heading_text:
                            headings.append(heading_text)

            # Create snippet (first 200 chars of markdown)
            snippet = ""
            if result.markdown:
                text = result.markdown.raw_markdown.replace("#", "").strip()
                snippet = text[:200].strip()

            # Get depth from metadata (set by deep crawl strategy)
            depth = result.metadata.get("depth", 0) if result.metadata else 0

            discovered.append({
                "url": result.url,
                "title": title or result.url.split("/")[-1] or "Home",
                "headings": headings[:5],
                "snippet": snippet,
                "depth": depth
            })

    return {
        "domain": domain,
        "seed_url": seed_url,
        "urls": discovered,
        "crawl_time": datetime.utcnow().isoformat() + "Z",
        "total_discovered": len(discovered)
    }


async def main():
    parser = argparse.ArgumentParser(
        description="Deep crawl documentation from a seed URL using Crawl4AI's BFSDeepCrawlStrategy."
    )
    parser.add_argument(
        "--seed",
        required=True,
        help="Seed URL (e.g., https://docs.example.com/)"
    )
    parser.add_argument(
        "--out",
        required=True,
        help="Output JSON file (e.g., artifacts/discovered.json)"
    )
    parser.add_argument(
        "--max-pages",
        type=int,
        default=100,
        help="Maximum pages to crawl (default: 100)"
    )
    parser.add_argument(
        "--max-depth",
        type=int,
        default=3,
        help="Maximum crawl depth (default: 3)"
    )

    args = parser.parse_args()

    print(f"Starting deep crawl from: {args.seed}")
    print(f"Max pages: {args.max_pages}")
    print(f"Max depth: {args.max_depth}\n")

    result = await crawl_docs(
        args.seed,
        max_pages=args.max_pages,
        max_depth=args.max_depth
    )

    os.makedirs(os.path.dirname(args.out) or ".", exist_ok=True)

    with open(args.out, "w") as f:
        json.dump(result, f, indent=2)

    print(f"\n✓ Discovered {result['total_discovered']} pages")
    print(f"✓ Saved to: {args.out}")

    # Print depth distribution
    depth_counts = {}
    for url_info in result["urls"]:
        d = url_info["depth"]
        depth_counts[d] = depth_counts.get(d, 0) + 1

    print("\nPages by depth:")
    for depth in sorted(depth_counts.keys()):
        print(f"  Depth {depth}: {depth_counts[depth]} pages")


if __name__ == "__main__":
    asyncio.run(main())
