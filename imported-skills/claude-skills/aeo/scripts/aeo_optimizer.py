#!/usr/bin/env python3
"""
aeo_optimizer.py — Generate AEO-optimized content variants.

Takes markdown content + audit recommendations, produces an optimized variant
with: structure fixes, citation slots, schema.org JSON-LD, fact-first lede.

Three modes:
  conservative — touch <10% of words; add only schema + citation markers
  balanced     — touch <30%; rewrite intro for fact-density; add structure
  aggressive   — full restructure for maximum AEO

Stdlib only. Deterministic transformations — does NOT call any LLM (the
recommendations come from aeo_audit.py).

Usage:
  python3 aeo_optimizer.py --input post.md --mode balanced --output post-aeo.md
  python3 aeo_optimizer.py --input post.md --industry healthcare --mode aggressive
  python3 aeo_optimizer.py --sample
  python3 aeo_optimizer.py --input post.md --mode balanced --output-format json

Source: distilled from aeo-box optimizer.py.
"""

import argparse
import json
import re
import sys
from datetime import datetime
from pathlib import Path
from typing import Any


MODES = ["conservative", "balanced", "aggressive"]


def extract_title(text: str) -> str:
    """Extract H1 or first non-empty line."""
    h1_match = re.search(r"^#\s+(.+)$", text, flags=re.MULTILINE)
    if h1_match:
        return h1_match.group(1).strip()
    for line in text.splitlines():
        if line.strip():
            return line.strip()[:120]
    return "Untitled"


def extract_headings(text: str) -> list:
    """Return list of (level, text) for H2-H6."""
    headings = []
    for m in re.finditer(r"^(#{2,6})\s+(.+)$", text, flags=re.MULTILINE):
        headings.append((len(m.group(1)), m.group(2).strip()))
    return headings


def generate_jsonld(title: str, headings: list, industry: str, url: str | None = None) -> str:
    """Generate schema.org JSON-LD for Article + FAQPage (if H2s look like questions)."""
    article = {
        "@context": "https://schema.org",
        "@type": "Article",
        "headline": title,
        "datePublished": datetime.utcnow().strftime("%Y-%m-%d"),
        "author": {"@type": "Person", "name": "{{AUTHOR_NAME}}"},
        "publisher": {"@type": "Organization", "name": "{{PUBLISHER}}"},
    }
    if url:
        article["url"] = url
        article["mainEntityOfPage"] = {"@type": "WebPage", "@id": url}

    # Detect question-style H2s for FAQPage schema
    question_h2s = [h[1] for h in headings if h[0] == 2 and (
        h[1].endswith("?") or re.match(r"^(what|why|how|when|where|who|which|is|are|does|do|can)\b", h[1], re.IGNORECASE)
    )]
    blocks = [json.dumps(article, indent=2)]
    if len(question_h2s) >= 2:
        faq = {
            "@context": "https://schema.org",
            "@type": "FAQPage",
            "mainEntity": [
                {
                    "@type": "Question",
                    "name": q,
                    "acceptedAnswer": {"@type": "Answer", "text": "{{ANSWER_" + str(i) + "}}"},
                }
                for i, q in enumerate(question_h2s, 1)
            ],
        }
        blocks.append(json.dumps(faq, indent=2))

    return "\n\n".join(f'<script type="application/ld+json">\n{b}\n</script>' for b in blocks)


def add_citation_markers(text: str, density: int = 3) -> tuple[str, int]:
    """Insert [N]-style citation markers after factual-looking sentences.

    Heuristic: a sentence with a number/percentage/year is likely a fact.
    Density caps insertions per 1000 words.
    """
    word_count = len(text.split())
    max_insertions = max(density, word_count // 250)
    insertions = 0

    def replace_fact(m):
        nonlocal insertions
        if insertions >= max_insertions:
            return m.group(0)
        sentence = m.group(0)
        # Only mark if it has a fact-like signal
        if re.search(r"\b(\d+(\.\d+)?%|\$\d|20\d{2}|\d{2,})\b", sentence) and "[" not in sentence:
            insertions += 1
            return sentence.rstrip(".") + f" [{insertions}]."
        return sentence

    new = re.sub(r"[^.!?]*[.!?]", replace_fact, text)
    return new, insertions


def add_corrections_footer(text: str, industry: str) -> str:
    """Append a corrections + disclosure footer."""
    footer = "\n\n---\n\n## Editorial Notes\n\n"
    footer += "- **Corrections:** This article will be updated as new information becomes available. Email corrections@example.com.\n"
    if industry in ("healthcare", "finance", "legal"):
        footer += f"- **{industry.title()} Disclaimer:** This article is for informational purposes only and does not constitute professional {industry} advice. Consult a licensed professional for your specific situation.\n"
    footer += "- **Disclosure:** {{INSERT_DISCLOSURE: affiliations, sponsorships, conflicts of interest}}\n"
    return text.rstrip() + footer


def fact_first_lede(text: str, title: str) -> str:
    """Move the first verifiable fact into the lede position (after H1)."""
    # Find first paragraph with a number/year/percentage
    lines = text.splitlines()
    h1_idx = -1
    for i, line in enumerate(lines):
        if line.startswith("# "):
            h1_idx = i
            break
    if h1_idx == -1:
        return text

    # Find first fact-bearing paragraph after H1
    fact_idx = -1
    for i in range(h1_idx + 1, len(lines)):
        if re.search(r"\b(\d+(\.\d+)?%|\$\d|\b20\d{2}\b|\d{2,}\s+(percent|pages|customers|users))\b", lines[i]):
            fact_idx = i
            break

    if fact_idx == -1 or fact_idx == h1_idx + 1 or fact_idx <= h1_idx + 2:
        # Already near top
        return text

    # Move that paragraph to right after H1
    fact_line = lines.pop(fact_idx)
    lines.insert(h1_idx + 2, fact_line)
    return "\n".join(lines)


def restructure_headings(text: str) -> str:
    """Promote bold-then-paragraph to H3, and ensure consistent H2 spacing."""
    # Convert lines that look like **Bold heading** followed by a paragraph into H3
    pattern = re.compile(r"^\*\*([A-Z][^*]+)\*\*\s*$", re.MULTILINE)
    text = pattern.sub(r"### \1", text)
    return text


def optimize(text: str, mode: str, industry: str, url: str | None = None) -> dict:
    """Apply optimizations based on mode. Returns dict with optimized text + changelog."""
    title = extract_title(text)
    headings = extract_headings(text)
    changelog = []

    result_text = text

    # All modes: add schema JSON-LD at the end (or top)
    jsonld = generate_jsonld(title, headings, industry, url)
    schema_block = f"\n\n---\n\n<!-- AEO Schema.org markup -->\n{jsonld}\n"

    if mode == "conservative":
        # Schema + corrections footer only — no body changes
        result_text = add_corrections_footer(result_text, industry)
        result_text = result_text.rstrip() + schema_block
        changelog.append("Added schema.org JSON-LD (Article + FAQPage if applicable)")
        changelog.append("Added editorial notes / corrections / disclosure footer")

    elif mode == "balanced":
        # Schema + corrections + citation markers + heading restructure
        result_text = restructure_headings(result_text)
        result_text, insertions = add_citation_markers(result_text, density=5)
        result_text = add_corrections_footer(result_text, industry)
        result_text = result_text.rstrip() + schema_block
        changelog.append("Promoted bold-paragraph patterns to H3 for LLM parsability")
        changelog.append(f"Added {insertions} citation markers at factual claims")
        changelog.append("Added schema.org JSON-LD")
        changelog.append("Added editorial notes / corrections / disclosure footer")

    elif mode == "aggressive":
        # All of balanced + fact-first lede
        result_text = fact_first_lede(result_text, title)
        result_text = restructure_headings(result_text)
        result_text, insertions = add_citation_markers(result_text, density=10)
        result_text = add_corrections_footer(result_text, industry)
        result_text = result_text.rstrip() + schema_block
        changelog.append("Moved first factual claim to fact-first lede position")
        changelog.append("Promoted bold-paragraph patterns to H3")
        changelog.append(f"Added {insertions} citation markers at factual claims")
        changelog.append("Added schema.org JSON-LD")
        changelog.append("Added editorial notes / corrections / disclosure footer")

    return {
        "mode": mode,
        "industry": industry,
        "title": title,
        "optimized_at": datetime.utcnow().isoformat() + "Z",
        "original_word_count": len(text.split()),
        "optimized_word_count": len(result_text.split()),
        "changelog": changelog,
        "optimized_content": result_text,
    }


SAMPLE_CONTENT = """# Why AEO Matters

Answer Engine Optimization helps content get cited by LLMs.

**Key trends in 2026**

The industry has seen 47% growth in LLM citations vs 2024.

**Tactical recommendations**

Add schema, dated examples, and author credentials.
"""


def main():
    p = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    p.add_argument("--input", help="Markdown file to optimize")
    p.add_argument("--output", help="Output file path (default: stdout)")
    p.add_argument("--mode", default="balanced", choices=MODES,
                   help="Optimization aggressiveness (default: balanced)")
    p.add_argument("--industry", default="saas",
                   choices=["saas", "healthcare", "finance", "legal", "ecommerce", "b2b", "media", "education"],
                   help="Industry-aware optimizations (default: saas)")
    p.add_argument("--url", help="Canonical URL to inject into schema.org markup")
    p.add_argument("--output-format", choices=["markdown", "json"], default="markdown",
                   help="Output format (default: markdown — emits the optimized content directly)")
    p.add_argument("--sample", action="store_true", help="Run with built-in sample content")
    args = p.parse_args()

    if args.sample:
        text = SAMPLE_CONTENT
    elif args.input:
        text = Path(args.input).read_text(encoding="utf-8")
    else:
        p.error("must specify --input or --sample")

    result = optimize(text, args.mode, args.industry, args.url)

    if args.output_format == "json":
        out = json.dumps(result, indent=2, default=str)
    else:
        # Markdown mode: emit the optimized content + the changelog as a comment
        out = result["optimized_content"]
        out += "\n\n<!--\nAEO Optimization Changelog:\n"
        for c in result["changelog"]:
            out += f"  - {c}\n"
        out += f"  Mode: {result['mode']}, Industry: {result['industry']}\n"
        out += f"  Original: {result['original_word_count']} words → Optimized: {result['optimized_word_count']} words\n"
        out += "-->\n"

    if args.output:
        Path(args.output).write_text(out, encoding="utf-8")
        sys.stderr.write(f"[aeo_optimizer] wrote {args.output}\n")
    else:
        print(out)


if __name__ == "__main__":
    main()
