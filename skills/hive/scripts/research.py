#!/usr/bin/env python3
"""
Hive Research Tools - Academic paper search from arXiv, PubMed, Semantic Scholar.

Usage:
    python research.py "query"                  # Search all sources
    python research.py "query" --source arxiv   # arXiv only
    python research.py "query" --source pubmed  # PubMed only
    python research.py "query" -n 20            # More results
"""

import argparse
import json
import os
import sys
from datetime import datetime

SOURCES = {
    "arxiv": {
        "name": "arXiv",
        "description": "Open-access preprint repository",
        "categories": ["cs", "math", "physics", "q-bio", "q-fin", "stat"]
    },
    "pubmed": {
        "name": "PubMed",
        "description": "Biomedical and life sciences literature",
        "env": "NCBI_API_KEY"
    },
    "semantic_scholar": {
        "name": "Semantic Scholar",
        "description": "AI-powered academic search",
        "env": "SEMANTIC_SCHOLAR_API_KEY"
    },
    "crossref": {
        "name": "CrossRef",
        "description": "DOI and citation metadata"
    }
}

def search_papers(query: str, source: str = "all", max_results: int = 10,
                  year_from: int = None, year_to: int = None) -> dict:
    """Search academic papers."""
    sources_to_search = list(SOURCES.keys()) if source == "all" else [source]

    if source != "all" and source not in SOURCES:
        return {"error": f"Unknown source: {source}", "available": list(SOURCES.keys())}

    results = {
        "query": query,
        "sources": sources_to_search,
        "filters": {
            "year_from": year_from,
            "year_to": year_to
        },
        "papers": []
    }

    for src in sources_to_search:
        src_info = SOURCES[src]
        print(f"Searching {src_info['name']}...")

        # Mock results (would call actual APIs)
        mock_papers = [
            {
                "source": src,
                "title": f"Sample Paper {i+1}: {query}",
                "authors": ["Author A", "Author B"],
                "year": 2024 - i,
                "abstract": f"This paper investigates {query}...",
                "url": f"https://{src}.org/paper{i+1}",
                "citations": 100 - (i * 10),
                "doi": f"10.1234/{src}.{i+1}"
            }
            for i in range(min(3, max_results))
        ]
        results["papers"].extend(mock_papers)

    results["total"] = len(results["papers"])
    results["note"] = "This is a demonstration. Connect to actual APIs for real results."

    return results

def format_output(results: dict, output_format: str) -> str:
    """Format results for display."""
    if output_format == "json":
        return json.dumps(results, indent=2)

    if "error" in results:
        return f"Error: {results['error']}"

    lines = [
        f"Query: {results['query']}",
        f"Sources: {', '.join(results['sources'])}",
        f"Papers found: {results['total']}",
        "-" * 50
    ]

    for i, paper in enumerate(results["papers"], 1):
        lines.append(f"\n{i}. {paper['title']}")
        lines.append(f"   Authors: {', '.join(paper['authors'])}")
        lines.append(f"   Year: {paper['year']} | Citations: {paper['citations']}")
        lines.append(f"   Source: {paper['source']}")
        lines.append(f"   URL: {paper['url']}")
        if paper.get("abstract"):
            abstract = paper["abstract"][:150] + "..." if len(paper["abstract"]) > 150 else paper["abstract"]
            lines.append(f"   Abstract: {abstract}")

    if results.get("note"):
        lines.append(f"\nNote: {results['note']}")

    return "\n".join(lines)

def main():
    parser = argparse.ArgumentParser(
        description="Hive Research Tools - Academic paper search",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python research.py "transformer attention"     Search all sources
  python research.py "CRISPR" --source pubmed    PubMed only
  python research.py "quantum computing" --source arxiv  arXiv only
  python research.py "topic" --year-from 2020    Recent papers only
  python research.py "topic" -n 30 --json        30 results as JSON

Sources:
  arxiv            - arXiv preprints (physics, math, CS)
  pubmed           - PubMed biomedical literature
  semantic_scholar - Semantic Scholar (all fields)
  crossref         - CrossRef DOI metadata
  all              - Search all sources (default)
        """
    )

    parser.add_argument("query", help="Search query")
    parser.add_argument("--source", "-s", choices=list(SOURCES.keys()) + ["all"],
                       default="all", help="Source to search (default: all)")
    parser.add_argument("--num-results", "-n", type=int, default=10,
                       help="Max results per source (default: 10)")
    parser.add_argument("--year-from", type=int, help="Filter: papers from this year")
    parser.add_argument("--year-to", type=int, help="Filter: papers up to this year")
    parser.add_argument("--json", action="store_true", help="Output as JSON")
    parser.add_argument("--output", "-o", help="Save results to file")
    parser.add_argument("--bibtex", action="store_true", help="Export as BibTeX")

    args = parser.parse_args()

    output_format = "json" if args.json else "text"
    results = search_papers(
        args.query,
        args.source,
        args.num_results,
        args.year_from,
        args.year_to
    )

    if args.bibtex:
        output = export_bibtex(results)
    else:
        output = format_output(results, output_format)

    if args.output:
        with open(args.output, "w") as f:
            f.write(output)
        print(f"Results saved to: {args.output}")
    else:
        print(output)

def export_bibtex(results: dict) -> str:
    """Export results as BibTeX entries."""
    entries = []
    for i, paper in enumerate(results.get("papers", []), 1):
        entry = f"""@article{{{paper['source']}{i},
  title = {{{paper['title']}}},
  author = {{{' and '.join(paper['authors'])}}},
  year = {{{paper['year']}}},
  url = {{{paper['url']}}},
  doi = {{{paper.get('doi', '')}}}
}}"""
        entries.append(entry)
    return "\n\n".join(entries)

if __name__ == "__main__":
    main()
