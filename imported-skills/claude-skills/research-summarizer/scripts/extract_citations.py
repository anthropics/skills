#!/usr/bin/env python3
"""
research-summarizer: Citation Extractor

Extract and format citations from text documents. Detects DOIs, URLs,
author-year patterns, and numbered references. Outputs in APA, IEEE,
Chicago, Harvard, or MLA format.

Usage:
    python scripts/extract_citations.py document.txt
    python scripts/extract_citations.py document.txt --format ieee
    python scripts/extract_citations.py document.txt --format apa --output json
    python scripts/extract_citations.py --stdin < document.txt
"""

import argparse
import json
import re
import sys
from collections import OrderedDict


# --- Citation Detection Patterns ---

PATTERNS = {
    "doi": re.compile(
        r"(?:https?://doi\.org/|doi:\s*)(10\.\d{4,}/[^\s,;}\]]+)", re.IGNORECASE
    ),
    "url": re.compile(
        r"https?://[^\s,;}\])\"'>]+", re.IGNORECASE
    ),
    "author_year": re.compile(
        r"(?:^|\(|\s)([A-Z][a-z]+(?:\s(?:&|and)\s[A-Z][a-z]+)?(?:\set\sal\.?)?)\s*\((\d{4})\)",
    ),
    "numbered_ref": re.compile(
        r"^\[(\d+)\]\s+(.+)$", re.MULTILINE
    ),
    "footnote": re.compile(
        r"^\d+\.\s+([A-Z].+?(?:\d{4}).+)$", re.MULTILINE
    ),
}


def extract_dois(text):
    """Extract DOI references."""
    citations = []
    for match in PATTERNS["doi"].finditer(text):
        doi = match.group(1).rstrip(".")
        citations.append({
            "type": "doi",
            "doi": doi,
            "raw": match.group(0).strip(),
            "url": f"https://doi.org/{doi}",
        })
    return citations


def extract_urls(text):
    """Extract URL references (excluding DOI URLs already captured)."""
    citations = []
    for match in PATTERNS["url"].finditer(text):
        url = match.group(0).rstrip(".,;)")
        if "doi.org" in url:
            continue
        citations.append({
            "type": "url",
            "url": url,
            "raw": url,
        })
    return citations


def extract_author_year(text):
    """Extract author-year citations like (Smith, 2023) or Smith & Jones (2021)."""
    citations = []
    for match in PATTERNS["author_year"].finditer(text):
        author = match.group(1).strip()
        year = match.group(2)
        citations.append({
            "type": "author_year",
            "author": author,
            "year": year,
            "raw": f"{author} ({year})",
        })
    return citations


def extract_numbered_refs(text):
    """Extract numbered reference list entries like [1] Author. Title..."""
    citations = []
    for match in PATTERNS["numbered_ref"].finditer(text):
        num = match.group(1)
        content = match.group(2).strip()
        citations.append({
            "type": "numbered",
            "number": int(num),
            "content": content,
            "raw": f"[{num}] {content}",
        })
    return citations


def deduplicate(citations):
    """Remove duplicate citations based on raw text."""
    seen = OrderedDict()
    for c in citations:
        key = c.get("doi") or c.get("url") or c.get("raw", "")
        key = key.lower().strip()
        if key and key not in seen:
            seen[key] = c
    return list(seen.values())


def classify_source(citation):
    """Classify citation as primary, secondary, or tertiary."""
    raw = citation.get("content", citation.get("raw", "")).lower()
    if any(kw in raw for kw in ["meta-analysis", "systematic review", "literature review", "survey of"]):
        return "secondary"
    if any(kw in raw for kw in ["textbook", "encyclopedia", "handbook", "dictionary"]):
        return "tertiary"
    return "primary"


# --- Formatting ---

def format_apa(citation):
    """Format citation in APA 7 style."""
    if citation["type"] == "doi":
        return f"https://doi.org/{citation['doi']}"
    if citation["type"] == "url":
        return f"Retrieved from {citation['url']}"
    if citation["type"] == "author_year":
        return f"{citation['author']} ({citation['year']})."
    if citation["type"] == "numbered":
        return citation["content"]
    return citation.get("raw", "")


def format_ieee(citation):
    """Format citation in IEEE style."""
    if citation["type"] == "doi":
        return f"doi: {citation['doi']}"
    if citation["type"] == "url":
        return f"[Online]. Available: {citation['url']}"
    if citation["type"] == "author_year":
        return f"{citation['author']}, {citation['year']}."
    if citation["type"] == "numbered":
        return f"[{citation['number']}] {citation['content']}"
    return citation.get("raw", "")


def format_chicago(citation):
    """Format citation in Chicago style."""
    if citation["type"] == "doi":
        return f"https://doi.org/{citation['doi']}."
    if citation["type"] == "url":
        return f"{citation['url']}."
    if citation["type"] == "author_year":
        return f"{citation['author']}. {citation['year']}."
    if citation["type"] == "numbered":
        return citation["content"]
    return citation.get("raw", "")


def format_harvard(citation):
    """Format citation in Harvard style."""
    if citation["type"] == "doi":
        return f"doi:{citation['doi']}"
    if citation["type"] == "url":
        return f"Available at: {citation['url']}"
    if citation["type"] == "author_year":
        return f"{citation['author']} ({citation['year']})"
    if citation["type"] == "numbered":
        return citation["content"]
    return citation.get("raw", "")


def format_mla(citation):
    """Format citation in MLA 9 style."""
    if citation["type"] == "doi":
        return f"doi:{citation['doi']}."
    if citation["type"] == "url":
        return f"{citation['url']}."
    if citation["type"] == "author_year":
        return f"{citation['author']}. {citation['year']}."
    if citation["type"] == "numbered":
        return citation["content"]
    return citation.get("raw", "")


FORMATTERS = {
    "apa": format_apa,
    "ieee": format_ieee,
    "chicago": format_chicago,
    "harvard": format_harvard,
    "mla": format_mla,
}


# --- Demo Data ---

DEMO_TEXT = """
Recent studies in product management have shown significant shifts in methodology.
According to Smith & Jones (2023), agile adoption has increased by 47% since 2020.
Patel et al. (2022) found that cross-functional teams deliver 2.3x faster.

Several frameworks have been proposed:
[1] Cagan, M. Inspired: How to Create Tech Products Customers Love. Wiley, 2018.
[2] Torres, T. Continuous Discovery Habits. Product Talk LLC, 2021.
[3] Gothelf, J. & Seiden, J. Lean UX. O'Reilly Media, 2021. doi: 10.1234/leanux.2021

For further reading, see https://www.svpg.com/articles/ and the meta-analysis
by Chen (2024) on product discovery effectiveness.

Related work: doi: 10.1145/3544548.3581388
"""


def run_extraction(text, fmt, output_mode):
    """Run full extraction pipeline."""
    all_citations = []
    all_citations.extend(extract_dois(text))
    all_citations.extend(extract_author_year(text))
    all_citations.extend(extract_numbered_refs(text))
    all_citations.extend(extract_urls(text))

    citations = deduplicate(all_citations)

    for c in citations:
        c["classification"] = classify_source(c)

    formatter = FORMATTERS.get(fmt, format_apa)

    if output_mode == "json":
        result = {
            "format": fmt,
            "total": len(citations),
            "citations": [],
        }
        for i, c in enumerate(citations, 1):
            result["citations"].append({
                "index": i,
                "type": c["type"],
                "classification": c["classification"],
                "formatted": formatter(c),
                "raw": c.get("raw", ""),
            })
        print(json.dumps(result, indent=2))
    else:
        print(f"Citations ({fmt.upper()}) — {len(citations)} found\n")
        primary = [c for c in citations if c["classification"] == "primary"]
        secondary = [c for c in citations if c["classification"] == "secondary"]
        tertiary = [c for c in citations if c["classification"] == "tertiary"]

        for label, group in [("Primary Sources", primary), ("Secondary Sources", secondary), ("Tertiary Sources", tertiary)]:
            if group:
                print(f"### {label}")
                for i, c in enumerate(group, 1):
                    print(f"  {i}. {formatter(c)}")
                print()

    return citations


def main():
    parser = argparse.ArgumentParser(
        description="research-summarizer: Extract and format citations from text"
    )
    parser.add_argument("file", nargs="?", help="Input text file (omit for demo)")
    parser.add_argument(
        "--format", "-f",
        choices=["apa", "ieee", "chicago", "harvard", "mla"],
        default="apa",
        help="Citation format (default: apa)",
    )
    parser.add_argument(
        "--output", "-o",
        choices=["text", "json"],
        default="text",
        help="Output mode (default: text)",
    )
    parser.add_argument(
        "--stdin",
        action="store_true",
        help="Read from stdin instead of file",
    )
    args = parser.parse_args()

    if args.stdin:
        text = sys.stdin.read()
    elif args.file:
        try:
            with open(args.file, "r", encoding="utf-8") as f:
                text = f.read()
        except FileNotFoundError:
            print(f"Error: File not found: {args.file}", file=sys.stderr)
            sys.exit(1)
        except IOError as e:
            print(f"Error reading file: {e}", file=sys.stderr)
            sys.exit(1)
    else:
        print("No input file provided. Running demo...\n")
        text = DEMO_TEXT

    run_extraction(text, args.format, args.output)


if __name__ == "__main__":
    main()
