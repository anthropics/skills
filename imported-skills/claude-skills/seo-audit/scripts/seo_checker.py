#!/usr/bin/env python3
"""
seo_checker.py — On-page SEO analyzer
Usage:
  python3 seo_checker.py [--file page.html] [--url https://...] [--json]
  python3 seo_checker.py          # demo mode with embedded sample HTML
"""

import argparse
import json
import math
import re
import sys
import urllib.request
from html.parser import HTMLParser


# ---------------------------------------------------------------------------
# HTML Parser
# ---------------------------------------------------------------------------

class SEOParser(HTMLParser):
    def __init__(self):
        super().__init__()
        self.title = ""
        self._in_title = False
        self.meta_description = ""
        self.h_tags = []          # list of (level, text)
        self._current_h = None
        self._current_h_text = []
        self.images = []          # list of {"src": ..., "alt": ...}
        self._in_body = False
        self.links = []           # list of {"href": ..., "text": ...}
        self._current_link_text = []
        self._current_link_href = ""
        self._in_link = False
        self.body_text_parts = []
        self._in_script = False
        self._in_style = False
        self.viewport_meta = False

    def handle_starttag(self, tag, attrs):
        attrs_dict = dict(attrs)
        tag = tag.lower()

        if tag == "title":
            self._in_title = True
        elif tag == "meta":
            name = attrs_dict.get("name", "").lower()
            prop = attrs_dict.get("property", "").lower()
            if name == "description":
                self.meta_description = attrs_dict.get("content", "")
            if name == "viewport":
                self.viewport_meta = True
            if prop == "og:description" and not self.meta_description:
                self.meta_description = attrs_dict.get("content", "")
        elif tag in ("h1", "h2", "h3", "h4", "h5", "h6"):
            self._current_h = int(tag[1])
            self._current_h_text = []
        elif tag == "img":
            self.images.append({
                "src": attrs_dict.get("src", ""),
                "alt": attrs_dict.get("alt", None),
            })
        elif tag == "a":
            self._in_link = True
            self._current_link_href = attrs_dict.get("href", "")
            self._current_link_text = []
        elif tag == "body":
            self._in_body = True
        elif tag == "script":
            self._in_script = True
        elif tag == "style":
            self._in_style = True

    def handle_endtag(self, tag):
        tag = tag.lower()
        if tag == "title":
            self._in_title = False
        elif tag in ("h1", "h2", "h3", "h4", "h5", "h6"):
            if self._current_h is not None:
                self.h_tags.append((self._current_h, " ".join(self._current_h_text).strip()))
            self._current_h = None
            self._current_h_text = []
        elif tag == "a":
            if self._in_link:
                self.links.append({
                    "href": self._current_link_href,
                    "text": " ".join(self._current_link_text).strip(),
                })
            self._in_link = False
            self._current_link_text = []
            self._current_link_href = ""
        elif tag == "script":
            self._in_script = False
        elif tag == "style":
            self._in_style = False

    def handle_data(self, data):
        if self._in_title:
            self.title += data
        if self._current_h is not None:
            self._current_h_text.append(data)
        if self._in_link:
            self._current_link_text.append(data)
        if self._in_body and not self._in_script and not self._in_style:
            self.body_text_parts.append(data)


# ---------------------------------------------------------------------------
# Analysis helpers
# ---------------------------------------------------------------------------

def _is_external(href, base_domain=""):
    if not href:
        return False
    return href.startswith("http://") or href.startswith("https://")


def analyze_html(html: str, base_domain: str = "") -> dict:
    parser = SEOParser()
    parser.feed(html)

    results = {}

    # --- Title ---
    title = parser.title.strip()
    title_len = len(title)
    title_ok = 50 <= title_len <= 60
    results["title"] = {
        "value": title,
        "length": title_len,
        "optimal_range": "50-60 chars",
        "pass": title_ok,
        "score": 100 if title_ok else (50 if title else 0),
        "note": "Good length" if title_ok else (
            f"Too {'short' if title_len < 50 else 'long'} ({title_len} chars)" if title else "Missing title tag"
        ),
    }

    # --- Meta description ---
    desc = parser.meta_description.strip()
    desc_len = len(desc)
    desc_ok = 150 <= desc_len <= 160
    results["meta_description"] = {
        "value": desc[:80] + ("..." if len(desc) > 80 else ""),
        "length": desc_len,
        "optimal_range": "150-160 chars",
        "pass": desc_ok,
        "score": 100 if desc_ok else (50 if 100 <= desc_len < 150 or 160 < desc_len <= 200 else (30 if desc else 0)),
        "note": "Good length" if desc_ok else (
            f"Too {'short' if desc_len < 150 else 'long'} ({desc_len} chars)" if desc else "Missing meta description"
        ),
    }

    # --- H1 ---
    h1s = [t for lvl, t in parser.h_tags if lvl == 1]
    h1_count = len(h1s)
    h1_ok = h1_count == 1
    results["h1"] = {
        "count": h1_count,
        "values": h1s,
        "pass": h1_ok,
        "score": 100 if h1_ok else (50 if h1_count > 1 else 0),
        "note": "Exactly one H1 ✓" if h1_ok else (
            f"Multiple H1s ({h1_count})" if h1_count > 1 else "No H1 found"
        ),
    }

    # --- Heading hierarchy ---
    heading_issues = []
    prev_level = 0
    for lvl, _ in parser.h_tags:
        if prev_level and lvl > prev_level + 1:
            heading_issues.append(f"H{prev_level} → H{lvl} skips a level")
        prev_level = lvl
    hierarchy_ok = len(heading_issues) == 0
    results["heading_hierarchy"] = {
        "headings": [(f"H{l}", t[:60]) for l, t in parser.h_tags],
        "issues": heading_issues,
        "pass": hierarchy_ok,
        "score": max(0, 100 - len(heading_issues) * 25),
        "note": "Hierarchy OK" if hierarchy_ok else f"{len(heading_issues)} level-skip issue(s)",
    }

    # --- Image alt text ---
    total_imgs = len(parser.images)
    imgs_with_alt = sum(1 for img in parser.images if img["alt"] is not None and img["alt"].strip())
    alt_pct = (imgs_with_alt / total_imgs * 100) if total_imgs else 100
    alt_ok = alt_pct == 100
    results["image_alt_text"] = {
        "total_images": total_imgs,
        "with_alt": imgs_with_alt,
        "coverage_pct": round(alt_pct, 1),
        "pass": alt_ok,
        "score": round(alt_pct),
        "note": "All images have alt text" if alt_ok else f"{total_imgs - imgs_with_alt} image(s) missing alt",
    }

    # --- Link ratio ---
    total_links = len(parser.links)
    ext_links = sum(1 for l in parser.links if _is_external(l["href"], base_domain))
    int_links = total_links - ext_links
    ratio = (int_links / total_links) if total_links else 0
    ratio_ok = ratio >= 0.5 or total_links == 0
    results["link_ratio"] = {
        "total_links": total_links,
        "internal": int_links,
        "external": ext_links,
        "internal_pct": round(ratio * 100, 1),
        "pass": ratio_ok,
        "score": 100 if ratio_ok else round(ratio * 100),
        "note": "Good internal/external balance" if ratio_ok else "More external than internal links",
    }

    # --- Word count ---
    body_text = " ".join(parser.body_text_parts)
    words = re.findall(r"\b\w+\b", body_text)
    word_count = len(words)
    wc_ok = word_count >= 300
    results["word_count"] = {
        "count": word_count,
        "minimum": 300,
        "pass": wc_ok,
        "score": min(100, round(word_count / 300 * 100)) if not wc_ok else 100,
        "note": f"{word_count} words (good)" if wc_ok else f"Only {word_count} words — need 300+",
    }

    # --- Viewport meta ---
    results["viewport_meta"] = {
        "present": parser.viewport_meta,
        "pass": parser.viewport_meta,
        "score": 100 if parser.viewport_meta else 0,
        "note": "Mobile viewport tag present" if parser.viewport_meta else "Missing viewport meta tag",
    }

    return results


def compute_overall_score(results: dict) -> int:
    weights = {
        "title": 20,
        "meta_description": 15,
        "h1": 15,
        "heading_hierarchy": 10,
        "image_alt_text": 10,
        "link_ratio": 10,
        "word_count": 15,
        "viewport_meta": 5,
    }
    total_w = sum(weights.values())
    score = sum(results[k]["score"] * w for k, w in weights.items() if k in results)
    return round(score / total_w)


# ---------------------------------------------------------------------------
# Demo HTML
# ---------------------------------------------------------------------------

DEMO_HTML = """<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>10 Ways to Boost Your Marketing ROI in 2024</title>
  <meta name="description" content="Discover ten proven strategies to maximize your marketing return on investment, reduce wasted ad spend, and grow revenue faster with data-driven techniques.">
</head>
<body>
  <h1>10 Ways to Boost Your Marketing ROI in 2024</h1>
  <p>Marketing budgets are tight. Every dollar counts. Here is how to make yours work harder.</p>
  <h2>1. Audit Your Current Spend</h2>
  <p>Before adding channels, understand where money goes. Most companies waste 30% of budget on low-ROI tactics.</p>
  <img src="audit-chart.png" alt="Marketing spend audit chart showing channel breakdown">
  <h2>2. Double Down on SEO</h2>
  <p>Organic traffic compounds. Paid stops the moment you stop spending. Invest in content that ranks.</p>
  <img src="seo-graph.png" alt="SEO traffic growth over 12 months">
  <h3>On-Page Optimization</h3>
  <p>Start with title tags, meta descriptions, and heading structure before anything else.</p>
  <h2>3. Improve Email Open Rates</h2>
  <p>Subject lines determine 80% of open rates. Test at least three variants per campaign.</p>
  <a href="/email-templates">Email templates library</a>
  <a href="https://mailchimp.com">Mailchimp</a>
  <h2>4. Use Retargeting Wisely</h2>
  <p>Retargeting works best with frequency caps. Show the same ad more than 7 times and you hurt brand perception.</p>
  <h2>5. Build Landing Pages That Convert</h2>
  <p>A single focused landing page beats a homepage for paid traffic every time. Remove navigation. Add a clear CTA.</p>
  <a href="/landing-page-guide">Landing page guide</a>
  <a href="/cro-checklist">CRO checklist</a>
  <a href="https://unbounce.com">Unbounce</a>
  <p>With these strategies you should see measurable improvement within 90 days. Start with the audit — it reveals the quickest wins.</p>
</body>
</html>"""


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="On-page SEO checker — scores an HTML page 0-100."
    )
    parser.add_argument("--file", help="Path to HTML file")
    parser.add_argument("--url", help="URL to fetch and analyze")
    parser.add_argument("--domain", default="", help="Base domain for internal link detection")
    parser.add_argument("--json", action="store_true", help="Output as JSON")
    args = parser.parse_args()

    if args.file:
        with open(args.file, "r", encoding="utf-8", errors="replace") as f:
            html = f.read()
    elif args.url:
        with urllib.request.urlopen(args.url, timeout=10) as resp:
            html = resp.read().decode("utf-8", errors="replace")
    else:
        html = DEMO_HTML
        if not args.json:
            print("No input provided — running in demo mode.\n")

    results = analyze_html(html, base_domain=args.domain)
    overall = compute_overall_score(results)

    if args.json:
        output = {"overall_score": overall, "checks": results}
        print(json.dumps(output, indent=2))
        return

    # Human-readable output
    ICONS = {True: "✅", False: "❌"}
    print("=" * 60)
    print(f"  SEO AUDIT RESULTS   Overall Score: {overall}/100")
    print("=" * 60)

    checks = [
        ("Title Tag",           "title"),
        ("Meta Description",    "meta_description"),
        ("H1 Tag",              "h1"),
        ("Heading Hierarchy",   "heading_hierarchy"),
        ("Image Alt Text",      "image_alt_text"),
        ("Link Ratio",          "link_ratio"),
        ("Word Count",          "word_count"),
        ("Viewport Meta",       "viewport_meta"),
    ]

    for label, key in checks:
        r = results[key]
        icon = ICONS[r["pass"]]
        score = r["score"]
        note = r["note"]
        print(f"  {icon}  {label:<22} [{score:>3}/100]  {note}")

    print("=" * 60)

    # Grade
    grade = "A" if overall >= 90 else "B" if overall >= 75 else "C" if overall >= 60 else "D" if overall >= 40 else "F"
    print(f"  Grade: {grade}   Score: {overall}/100")
    print("=" * 60)


if __name__ == "__main__":
    main()
