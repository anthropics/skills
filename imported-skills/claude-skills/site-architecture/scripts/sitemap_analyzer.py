#!/usr/bin/env python3
"""
sitemap_analyzer.py — Analyzes sitemap.xml files for structure, depth, and potential issues.

Usage:
    python3 sitemap_analyzer.py [sitemap.xml]
    python3 sitemap_analyzer.py https://example.com/sitemap.xml  (fetches via urllib)
    cat sitemap.xml | python3 sitemap_analyzer.py

If no file is provided, runs on embedded sample sitemap for demonstration.

Output: Structural analysis with depth distribution, URL patterns, orphan candidates,
        duplicate path detection, and JSON summary.
Stdlib only — no external dependencies.
"""

import json
import sys
import re
import select
import urllib.request
import urllib.error
from collections import Counter, defaultdict
from urllib.parse import urlparse
import xml.etree.ElementTree as ET


# ─── Namespaces used in sitemaps ─────────────────────────────────────────────

SITEMAP_NAMESPACES = {
    "sm": "http://www.sitemaps.org/schemas/sitemap/0.9",
    "image": "http://www.google.com/schemas/sitemap-image/1.1",
    "video": "http://www.google.com/schemas/sitemap-video/1.1",
    "news": "http://www.google.com/schemas/sitemap-news/0.9",
    "xhtml": "http://www.w3.org/1999/xhtml",
}

# ─── Sample sitemap (embedded) ────────────────────────────────────────────────

SAMPLE_SITEMAP = """<?xml version="1.0" encoding="UTF-8"?>
<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">

  <!-- Homepage -->
  <url>
    <loc>https://example.com/</loc>
    <changefreq>daily</changefreq>
    <priority>1.0</priority>
  </url>

  <!-- Top-level pages -->
  <url><loc>https://example.com/pricing</loc></url>
  <url><loc>https://example.com/about</loc></url>
  <url><loc>https://example.com/contact</loc></url>
  <url><loc>https://example.com/blog</loc></url>

  <!-- Features section -->
  <url><loc>https://example.com/features</loc></url>
  <url><loc>https://example.com/features/email-automation</loc></url>
  <url><loc>https://example.com/features/crm-integration</loc></url>
  <url><loc>https://example.com/features/analytics</loc></url>

  <!-- Solutions section -->
  <url><loc>https://example.com/solutions/sales-teams</loc></url>
  <url><loc>https://example.com/solutions/marketing-teams</loc></url>

  <!-- Blog posts (various topics) -->
  <url><loc>https://example.com/blog/cold-email-guide</loc></url>
  <url><loc>https://example.com/blog/email-open-rates</loc></url>
  <url><loc>https://example.com/blog/crm-comparison</loc></url>
  <url><loc>https://example.com/blog/sales-process-optimization</loc></url>

  <!-- Deeply nested pages (potential issue) -->
  <url><loc>https://example.com/resources/guides/email/cold-outreach/advanced/templates</loc></url>
  <url><loc>https://example.com/resources/guides/email/cold-outreach/advanced/scripts</loc></url>

  <!-- Duplicate path patterns (potential issue) -->
  <url><loc>https://example.com/blog/email-tips</loc></url>
  <url><loc>https://example.com/resources/email-tips</loc></url>

  <!-- Dynamic-looking URL (potential issue) -->
  <url><loc>https://example.com/search?q=cold+email&amp;sort=recent</loc></url>

  <!-- Case studies -->
  <url><loc>https://example.com/customers/acme-corp</loc></url>
  <url><loc>https://example.com/customers/globex</loc></url>

  <!-- Legal pages (often over-linked) -->
  <url><loc>https://example.com/privacy</loc></url>
  <url><loc>https://example.com/terms</loc></url>

</urlset>
"""


# ─── URL Analysis ─────────────────────────────────────────────────────────────

def get_depth(path: str) -> int:
    """Return depth of a URL path. / = 0, /blog = 1, /blog/post = 2, etc."""
    parts = [p for p in path.strip("/").split("/") if p]
    return len(parts)


def get_path_pattern(path: str) -> str:
    """Replace variable segments with {slug} for pattern detection."""
    parts = path.strip("/").split("/")
    normalized = []
    for p in parts:
        if p:
            # Keep static segments (likely structure), replace dynamic-looking ones
            if re.match(r'^[a-z][-a-z]+$', p) and len(p) < 30:
                normalized.append(p)
            else:
                normalized.append("{slug}")
    return "/" + "/".join(normalized) if normalized else "/"


def has_query_params(url: str) -> bool:
    return "?" in url


def looks_like_dynamic_url(url: str) -> bool:
    parsed = urlparse(url)
    return bool(parsed.query)


def detect_path_siblings(urls: list) -> list:
    """Find URLs with same slug in different parent directories (potential duplicates)."""
    slug_to_paths = defaultdict(list)
    for url in urls:
        path = urlparse(url).path.strip("/")
        slug = path.split("/")[-1] if path else ""
        if slug:
            slug_to_paths[slug].append(url)

    duplicates = []
    for slug, paths in slug_to_paths.items():
        if len(paths) > 1:
            # Only flag if they're in different directories
            parents = set("/".join(urlparse(p).path.strip("/").split("/")[:-1]) for p in paths)
            if len(parents) > 1:
                duplicates.append({"slug": slug, "urls": paths})
    return duplicates


# ─── Sitemap Parser ──────────────────────────────────────────────────────────

def parse_sitemap(content: str) -> list:
    """Parse sitemap XML and return list of URL dicts."""
    urls = []

    # Strip namespace declarations for simpler parsing
    content_clean = re.sub(r'xmlns[^=]*="[^"]*"', '', content)

    try:
        root = ET.fromstring(content_clean)
    except ET.ParseError as e:
        print(f"❌ XML parse error: {e}", file=sys.stderr)
        return []

    # Handle sitemap index (points to other sitemaps)
    if root.tag.endswith("sitemapindex") or root.tag == "sitemapindex":
        print("ℹ️  This is a sitemap index file — it points to child sitemaps.")
        print("   Child sitemaps:")
        for sitemap in root.findall(".//{http://www.sitemaps.org/schemas/sitemap/0.9}loc") or root.findall(".//loc"):
            print(f"   - {sitemap.text}")
        print("   Run this tool on each child sitemap for full analysis.")
        return []

    # Regular urlset
    for url_el in root.findall(".//{http://www.sitemaps.org/schemas/sitemap/0.9}url") or root.findall(".//url"):
        loc_el = url_el.find("{http://www.sitemaps.org/schemas/sitemap/0.9}loc") or url_el.find("loc")
        lastmod_el = url_el.find("{http://www.sitemaps.org/schemas/sitemap/0.9}lastmod") or url_el.find("lastmod")
        priority_el = url_el.find("{http://www.sitemaps.org/schemas/sitemap/0.9}priority") or url_el.find("priority")

        if loc_el is not None and loc_el.text:
            urls.append({
                "url": loc_el.text.strip(),
                "lastmod": lastmod_el.text.strip() if lastmod_el is not None and lastmod_el.text else None,
                "priority": float(priority_el.text.strip()) if priority_el is not None and priority_el.text else None,
            })

    return urls


# ─── Analysis Engine ─────────────────────────────────────────────────────────

def analyze_urls(urls: list) -> dict:
    raw_urls = [u["url"] for u in urls]
    paths = [urlparse(u).path for u in raw_urls]

    depths = [get_depth(p) for p in paths]
    depth_counter = Counter(depths)

    dynamic_urls = [u for u in raw_urls if looks_like_dynamic_url(u)]

    patterns = Counter(get_path_pattern(urlparse(u).path) for u in raw_urls)
    top_patterns = patterns.most_common(10)

    duplicate_slugs = detect_path_siblings(raw_urls)

    deep_urls = [(u, get_depth(urlparse(u).path)) for u in raw_urls if get_depth(urlparse(u).path) >= 4]

    # Extract top-level directories
    top_dirs = Counter()
    for p in paths:
        parts = p.strip("/").split("/")
        if parts and parts[0]:
            top_dirs[parts[0]] += 1

    return {
        "total_urls": len(urls),
        "depth_distribution": dict(sorted(depth_counter.items())),
        "top_directories": dict(top_dirs.most_common(15)),
        "dynamic_urls": dynamic_urls,
        "deep_pages": deep_urls,
        "duplicate_slug_candidates": duplicate_slugs,
        "top_url_patterns": [{"pattern": p, "count": c} for p, c in top_patterns],
    }


# ─── Report Printer ──────────────────────────────────────────────────────────

def grade_depth_distribution(dist: dict) -> str:
    deep = sum(v for k, v in dist.items() if k >= 4)
    total = sum(dist.values())
    if total == 0:
        return "N/A"
    pct = deep / total * 100
    if pct < 5:
        return "🟢 Excellent"
    if pct < 15:
        return "🟡 Acceptable"
    return "🔴 Too many deep pages"


def print_report(analysis: dict) -> None:
    print("\n" + "═" * 62)
    print("  SITEMAP STRUCTURE ANALYSIS")
    print("═" * 62)
    print(f"\n  Total URLs: {analysis['total_urls']}")

    print("\n── Depth Distribution ──")
    dist = analysis["depth_distribution"]
    total = analysis["total_urls"]
    for depth, count in sorted(dist.items()):
        pct = count / total * 100 if total else 0
        bar = "█" * int(pct / 2)
        label = "homepage" if depth == 0 else f"{'  ' * min(depth, 3)}/{'…/' * (depth - 1)}page"
        print(f"   Depth {depth}: {count:4d} pages ({pct:5.1f}%)  {bar}  {label}")

    print(f"\n   Rating: {grade_depth_distribution(dist)}")
    deep_pct = sum(v for k, v in dist.items() if k >= 4) / total * 100 if total else 0
    if deep_pct >= 5:
        print("   ⚠️  More than 5% of pages are 4+ levels deep.")
        print("      Consider flattening structure or adding shortcut links.")

    print("\n── Top-Level Directories ──")
    for d, count in analysis["top_directories"].items():
        pct = count / total * 100 if total else 0
        print(f"   /{d:<30s}  {count:4d} URLs ({pct:.1f}%)")

    print("\n── URL Pattern Analysis ──")
    for p in analysis["top_url_patterns"]:
        print(f"   {p['pattern']:<45s}  {p['count']:4d} URLs")

    if analysis["dynamic_urls"]:
        print(f"\n── Dynamic URLs Detected ({len(analysis['dynamic_urls'])}) ──")
        print("   ⚠️  URLs with query parameters should usually be excluded from sitemap.")
        print("      Use canonical tags or robots.txt to prevent duplicate content indexing.")
        for u in analysis["dynamic_urls"][:5]:
            print(f"   {u}")
        if len(analysis["dynamic_urls"]) > 5:
            print(f"   ... and {len(analysis['dynamic_urls']) - 5} more")

    if analysis["deep_pages"]:
        print(f"\n── Deep Pages (4+ Levels) ({len(analysis['deep_pages'])}) ──")
        print("   ⚠️  Pages this deep may have weak crawl equity. Add internal shortcuts.")
        for url, depth in analysis["deep_pages"][:5]:
            print(f"   Depth {depth}: {url}")
        if len(analysis["deep_pages"]) > 5:
            print(f"   ... and {len(analysis['deep_pages']) - 5} more")

    if analysis["duplicate_slug_candidates"]:
        print(f"\n── Potential Duplicate Path Issues ({len(analysis['duplicate_slug_candidates'])}) ──")
        print("   ⚠️  Same slug appears in multiple directories — possible duplicate content.")
        for item in analysis["duplicate_slug_candidates"][:5]:
            print(f"   Slug: '{item['slug']}'")
            for u in item["urls"]:
                print(f"     - {u}")
        if len(analysis["duplicate_slug_candidates"]) > 5:
            print(f"   ... and {len(analysis['duplicate_slug_candidates']) - 5} more")

    print("\n── Recommendations ──")
    has_issues = False
    if analysis["dynamic_urls"]:
        print("   1. Remove dynamic URLs (with ?) from sitemap.")
        has_issues = True
    if analysis["deep_pages"]:
        print(f"   {'2' if has_issues else '1'}. Flatten deep URL structures or add internal shortcut links.")
        has_issues = True
    if analysis["duplicate_slug_candidates"]:
        print(f"   {'3' if has_issues else '1'}. Review duplicate slug paths — consolidate or add canonical tags.")
        has_issues = True
    if not has_issues:
        print("   ✅ No major structural issues detected in this sitemap.")

    print("\n" + "═" * 62)


# ─── Main ─────────────────────────────────────────────────────────────────────

def load_content(source: str) -> str:
    """Load sitemap from file path, URL, or stdin."""
    if source.startswith("http://") or source.startswith("https://"):
        try:
            with urllib.request.urlopen(source, timeout=10) as resp:
                return resp.read().decode("utf-8")
        except urllib.error.URLError as e:
            print(f"Error fetching URL: {e}", file=sys.stderr)
            sys.exit(1)
    else:
        try:
            with open(source, "r", encoding="utf-8") as f:
                return f.read()
        except FileNotFoundError:
            print(f"Error: File not found: {source}", file=sys.stderr)
            sys.exit(1)


def main():
    import argparse

    parser = argparse.ArgumentParser(
        description="Analyzes sitemap.xml files for structure, depth, and potential issues. "
                    "Reports depth distribution, URL patterns, orphan candidates, and duplicates."
    )
    parser.add_argument(
        "file", nargs="?", default=None,
        help="Path to a sitemap.xml file or URL (https://...). "
             "Use '-' to read from stdin. If omitted, runs embedded sample."
    )
    args = parser.parse_args()

    if args.file:
        if args.file == "-":
            content = sys.stdin.read()
        else:
            content = load_content(args.file)
    else:
        print("No file or URL provided — running on embedded sample sitemap.\n")
        content = SAMPLE_SITEMAP

    urls = parse_sitemap(content)
    if not urls:
        print("No URLs found in sitemap.", file=sys.stderr)
        sys.exit(1)

    analysis = analyze_urls(urls)
    print_report(analysis)

    # JSON output
    print("\n── JSON Summary ──")
    summary = {
        "total_urls": analysis["total_urls"],
        "depth_distribution": analysis["depth_distribution"],
        "dynamic_url_count": len(analysis["dynamic_urls"]),
        "deep_page_count": len(analysis["deep_pages"]),
        "duplicate_slug_count": len(analysis["duplicate_slug_candidates"]),
        "top_directories": analysis["top_directories"],
    }
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
