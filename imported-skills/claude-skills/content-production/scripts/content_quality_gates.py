#!/usr/bin/env python3
"""
content_quality_gates.py — Non-negotiable quality checks before publishing.

Hard stops that BLOCK publication. These aren't suggestions — they're rules.
Inspired by the quality gate pattern used in high-traction content tools.

Gates (all must pass):
  1. Heading hierarchy: H1 → H2 → H3 only (no skips, no H4+ without H3)
  2. No paragraphs > 150 words (wall of text)
  3. All images/figures have alt text references
  4. Source citations: any statistic must have a [source] marker
  5. Title length: 50-60 characters
  6. Meta description: 150-160 characters (if present)
  7. No self-promotional mentions beyond 1
  8. dateModified or "Updated" marker present for evergreen content

Usage:
    python content_quality_gates.py article.md
    python content_quality_gates.py article.md --json
    python content_quality_gates.py --demo

Score bands (from the gate results):
    All pass         → PUBLISH (ready to ship)
    1-2 warnings     → TARGET (fix specific items)
    Any gate failure  → BLOCK (fix before publishing)
"""
from __future__ import annotations
import argparse
import json
import re
import sys
from pathlib import Path

HEADING_RE = re.compile(r"^(#{1,6})\s+(.+)$", re.MULTILINE)
STAT_RE = re.compile(r"\b\d+(?:\.\d+)?%|\$\d+|\d+(?:,\d{3})+|\d+x\b", re.IGNORECASE)
SOURCE_RE = re.compile(r"\[(?:source|citation|ref|via|from)\b.*?\]|\(https?://\S+\)", re.IGNORECASE)
IMAGE_RE = re.compile(r"!\[([^\]]*)\]\(", re.MULTILINE)
TITLE_RE = re.compile(r"^#\s+(.+)$", re.MULTILINE)
META_DESC_RE = re.compile(r"^description:\s*[\"']?(.+?)[\"']?\s*$", re.MULTILINE)
SELF_PROMO_RE = re.compile(r"\b(?:our product|we offer|sign up|try free|get started|our platform|our solution)\b", re.IGNORECASE)
DATE_RE = re.compile(r"(?:updated|modified|reviewed|published).*?\d{4}", re.IGNORECASE)
FRONTMATTER_DATE_RE = re.compile(r"^(?:date_?modified|updated|last_updated):\s*\d{4}", re.MULTILINE)

DEMO_CONTENT = """---
title: "How to Optimize Your Landing Page for Conversions"
description: "Learn the 7 proven techniques to boost landing page conversion rates by 40% or more."
dateModified: 2026-03-15
---

# How to Optimize Your Landing Page for Conversions

Landing pages are the backbone of any digital marketing campaign. Getting them right means more leads, more sales, and better ROI on every dollar you spend on ads.

## Start With a Clear Value Proposition

Your headline should communicate the core benefit in under 10 words. According to a study by Marketing Experiments, clarity beats persuasion by 104% in headline tests [source: marketingexperiments.com].

The subheadline expands on the promise. Keep it under 25 words.

## Optimize Your Form Length

Fewer fields mean higher conversions. HubSpot found that reducing form fields from 4 to 3 increased conversions by 50% [source: HubSpot 2025 Benchmark Report].

### When to Use Long Forms

Long forms work for high-value B2B offers where lead quality matters more than volume. The key is progressive profiling — ask for more information over time, not all at once.

## Add Social Proof Above the Fold

Show logos, testimonials, or user counts where visitors can see them without scrolling. 72% of consumers say positive reviews increase their trust [source: BrightLocal 2025].

![Customer testimonials section](testimonials.png)

## Test Your CTA Button

The button text matters more than the color. "Get My Free Guide" outperforms "Submit" by 3x on average.

Our platform makes A/B testing effortless — try it free today.

## Measure and Iterate

Track these metrics weekly: conversion rate, bounce rate, time on page, scroll depth. Set up goals in Google Analytics 4 and review them every Friday.
"""


def check_heading_hierarchy(text):
    """Gate 1: H1 → H2 → H3 only, no skips."""
    findings = []
    headings = [(m.start(), len(m.group(1)), m.group(2)) for m in HEADING_RE.finditer(text)]
    prev_level = 0
    for _, level, title in headings:
        if level > prev_level + 1 and prev_level > 0:
            findings.append(f"Heading skip: H{prev_level} → H{level} at '{title[:40]}'. Don't skip levels.")
        prev_level = level
    return {"gate": "heading-hierarchy", "passed": len(findings) == 0, "findings": findings}


def check_paragraph_length(text):
    """Gate 2: No paragraph > 150 words."""
    findings = []
    body = re.sub(r"^---.*?---\s*", "", text, count=1, flags=re.DOTALL)
    paragraphs = re.split(r"\n\s*\n", body)
    for i, para in enumerate(paragraphs, 1):
        para = para.strip()
        if not para or para.startswith("#") or para.startswith("```") or para.startswith("|"):
            continue
        words = len(para.split())
        if words > 150:
            findings.append(f"Paragraph {i}: {words} words (max 150). Break it up.")
    return {"gate": "paragraph-length", "passed": len(findings) == 0, "findings": findings}


def check_image_alt_text(text):
    """Gate 3: All images have alt text."""
    findings = []
    for m in IMAGE_RE.finditer(text):
        alt = m.group(1).strip()
        if not alt:
            findings.append(f"Image missing alt text: ![](...) — add descriptive alt.")
    return {"gate": "image-alt-text", "passed": len(findings) == 0, "findings": findings}


def check_source_citations(text):
    """Gate 4: Statistics must have source markers."""
    findings = []
    body = re.sub(r"^---.*?---\s*", "", text, count=1, flags=re.DOTALL)
    lines = body.splitlines()
    for i, line in enumerate(lines, 1):
        if line.strip().startswith("#") or line.strip().startswith("```"):
            continue
        stats = STAT_RE.findall(line)
        if stats and not SOURCE_RE.search(line):
            stat_str = ", ".join(stats[:3])
            findings.append(f"Line {i}: statistic ({stat_str}) without [source] marker.")
    return {"gate": "source-citations", "passed": len(findings) == 0, "findings": findings}


def check_title_length(text):
    """Gate 5: Title 50-60 characters."""
    findings = []
    m = TITLE_RE.search(text)
    if m:
        title = m.group(1).strip()
        length = len(title)
        if length < 50:
            findings.append(f"Title too short: {length} chars (aim for 50-60). Title: '{title}'")
        elif length > 60:
            findings.append(f"Title too long: {length} chars (aim for 50-60). Title: '{title}'")
    else:
        findings.append("No H1 title found.")
    return {"gate": "title-length", "passed": len(findings) == 0, "findings": findings}


def check_meta_description(text):
    """Gate 6: Meta description 150-160 chars (if present)."""
    findings = []
    m = META_DESC_RE.search(text)
    if m:
        desc = m.group(1).strip()
        length = len(desc)
        if length < 150:
            findings.append(f"Meta description too short: {length} chars (aim for 150-160).")
        elif length > 160:
            findings.append(f"Meta description too long: {length} chars (aim for 150-160). Will be truncated.")
    return {"gate": "meta-description", "passed": len(findings) == 0, "findings": findings}


def check_self_promotion(text):
    """Gate 7: Max 1 self-promotional mention."""
    findings = []
    matches = SELF_PROMO_RE.findall(text)
    if len(matches) > 1:
        findings.append(f"{len(matches)} self-promotional mentions found (max 1): {', '.join(matches[:5])}")
    return {"gate": "self-promotion", "passed": len(findings) == 0, "findings": findings}


def check_freshness(text):
    """Gate 8: dateModified or update marker present."""
    findings = []
    has_date = bool(FRONTMATTER_DATE_RE.search(text)) or bool(DATE_RE.search(text))
    if not has_date:
        findings.append("No dateModified or 'Updated' marker. Evergreen content needs freshness signals.")
    return {"gate": "freshness-signal", "passed": len(findings) == 0, "findings": findings}


ALL_GATES = [
    check_heading_hierarchy,
    check_paragraph_length,
    check_image_alt_text,
    check_source_citations,
    check_title_length,
    check_meta_description,
    check_self_promotion,
    check_freshness,
]


def run_gates(text):
    results = [gate(text) for gate in ALL_GATES]
    passed = sum(1 for r in results if r["passed"])
    failed = [r for r in results if not r["passed"]]
    total = len(results)

    if len(failed) == 0:
        verdict = "PUBLISH"
    elif all(len(r["findings"]) <= 1 for r in failed) and len(failed) <= 2:
        verdict = "TARGET"
    else:
        verdict = "BLOCK"

    return {
        "status": "ok",
        "gates_passed": passed,
        "gates_total": total,
        "verdict": verdict,
        "results": results,
    }


def main():
    p = argparse.ArgumentParser(
        description="Non-negotiable quality gates for content publishing.",
        epilog="All gates must pass before publishing. Run with --demo for a sample article.",
    )
    p.add_argument("file", nargs="?", help="Markdown file to check")
    p.add_argument("--json", action="store_true", help="JSON output")
    p.add_argument("--demo", action="store_true", help="Run with demo content")
    args = p.parse_args()

    if args.demo:
        text = DEMO_CONTENT
    elif args.file:
        path = Path(args.file)
        if not path.exists():
            print(f"[error] {path} not found", file=sys.stderr)
            sys.exit(1)
        text = path.read_text(encoding="utf-8", errors="replace")
    else:
        p.print_help()
        sys.exit(0)

    result = run_gates(text)

    if args.json:
        print(json.dumps(result, indent=2))
        return

    print(f"Content Quality Gates — {result['gates_passed']}/{result['gates_total']} passed")
    print(f"Verdict: {result['verdict']}")
    print()
    for r in result["results"]:
        icon = "✅" if r["passed"] else "❌"
        print(f"  {icon} {r['gate']}")
        for f in r["findings"]:
            print(f"     → {f}")
    print()
    if result["verdict"] == "PUBLISH":
        print("  All gates pass. Ready to publish.")
    elif result["verdict"] == "TARGET":
        print("  Minor issues. Fix the flagged items, then publish.")
    else:
        print("  BLOCKED. Fix all gate failures before publishing.")


if __name__ == "__main__":
    main()
