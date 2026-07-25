#!/usr/bin/env python3
"""cross_search_aggregator.py — Cross-search intelligence for litreview.

Stdlib-only. Reads all search results recorded across a litreview session
and computes three signals that transform a per-search paper list into
field-level intelligence:

  1. Repeat-hit papers: same paper in 3+ sub-area searches (foundational signal)
  2. Recurring authors: same author across multiple searches (dominant group)
  3. Citation-per-year: normalizes raw citation count by paper age (seminal work)

Reads from a search-results JSON file (one entry per search, each with
papers list including url, title, authors, year, citations).

Outputs feed the DOCX guide's "Start Here" + "Key Research Groups"
sections.

NO LLM CALLS. Pure aggregation + ranking.

Input file format (`--results-file`):
{
  "session": "litreview-20260515",
  "searches": [
    {
      "query": "...",
      "sub_area": "Intervention",
      "papers": [
        {"url": "https://...", "title": "...", "authors": ["..."], "year": 2023, "citations": 150}
      ]
    }
  ]
}

Usage:
    python cross_search_aggregator.py --results-file /tmp/results.json
    python cross_search_aggregator.py --results-file /tmp/results.json --output json
    python cross_search_aggregator.py --sample
"""

import argparse
import json
import sys
from collections import Counter
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List


REPEAT_HIT_THRESHOLD = 3  # paper must appear in 3+ sub-areas
TOP_AUTHORS_N = 5
TOP_REPEAT_HITS_N = 8


SAMPLE_RESULTS = {
    "session": "litreview-sample",
    "searches": [
        {
            "query": "LLM clinical reasoning benchmarks",
            "sub_area": "Intervention",
            "papers": [
                {"url": "https://consensus.app/paper/abc1", "title": "Med-PaLM benchmark", "authors": ["Singhal", "Tu", "Gottweis"], "year": 2023, "citations": 250},
                {"url": "https://consensus.app/paper/abc2", "title": "LLMs vs physicians on USMLE", "authors": ["Kung", "Cheatham"], "year": 2023, "citations": 800},
                {"url": "https://consensus.app/paper/abc3", "title": "Reasoning evaluation framework", "authors": ["Lievin"], "year": 2024, "citations": 120},
            ],
        },
        {
            "query": "clinical reasoning evaluation methodology",
            "sub_area": "Outcome",
            "papers": [
                {"url": "https://consensus.app/paper/abc1", "title": "Med-PaLM benchmark", "authors": ["Singhal", "Tu", "Gottweis"], "year": 2023, "citations": 250},
                {"url": "https://consensus.app/paper/abc4", "title": "Diagnostic accuracy AI", "authors": ["Toma", "Lawler"], "year": 2024, "citations": 90},
                {"url": "https://consensus.app/paper/abc5", "title": "AI in medicine review", "authors": ["Singhal", "Azizi"], "year": 2023, "citations": 200},
            ],
        },
        {
            "query": "GPT-4 medical Q&A",
            "sub_area": "Population",
            "papers": [
                {"url": "https://consensus.app/paper/abc1", "title": "Med-PaLM benchmark", "authors": ["Singhal", "Tu", "Gottweis"], "year": 2023, "citations": 250},
                {"url": "https://consensus.app/paper/abc2", "title": "LLMs vs physicians on USMLE", "authors": ["Kung", "Cheatham"], "year": 2023, "citations": 800},
                {"url": "https://consensus.app/paper/abc6", "title": "GPT-4 USMLE performance", "authors": ["Nori", "King"], "year": 2023, "citations": 400},
            ],
        },
    ],
}


def aggregate(results: Dict[str, Any]) -> Dict[str, Any]:
    paper_appearances: Dict[str, Dict[str, Any]] = {}
    author_appearances: Counter = Counter()
    author_paper_sub_areas: Dict[str, set] = {}

    for search in results.get("searches", []):
        sub_area = search.get("sub_area", "uncategorized")
        for paper in search.get("papers", []):
            url = paper.get("url", "")
            if not url:
                continue
            if url not in paper_appearances:
                paper_appearances[url] = {
                    "url": url,
                    "title": paper.get("title", ""),
                    "authors": paper.get("authors", []),
                    "year": paper.get("year"),
                    "citations": paper.get("citations", 0),
                    "sub_areas": set(),
                }
            paper_appearances[url]["sub_areas"].add(sub_area)

            for author in paper.get("authors", []):
                author_appearances[author] += 1
                if author not in author_paper_sub_areas:
                    author_paper_sub_areas[author] = set()
                author_paper_sub_areas[author].add(sub_area)

    # Tracker 1: Repeat-hit papers
    repeat_hits: List[Dict[str, Any]] = []
    for url, p in paper_appearances.items():
        if len(p["sub_areas"]) >= REPEAT_HIT_THRESHOLD:
            entry = {
                "url": p["url"],
                "title": p["title"],
                "authors": p["authors"],
                "year": p["year"],
                "citations": p["citations"],
                "sub_areas": sorted(p["sub_areas"]),
                "sub_area_count": len(p["sub_areas"]),
            }
            repeat_hits.append(entry)
    repeat_hits.sort(key=lambda x: (-x["sub_area_count"], -(x["citations"] or 0)))

    # Tracker 2: Recurring authors
    recurring_authors: List[Dict[str, Any]] = []
    for author, count in author_appearances.most_common(TOP_AUTHORS_N):
        if count >= 2:
            recurring_authors.append({
                "author": author,
                "appearances": count,
                "sub_areas": sorted(author_paper_sub_areas.get(author, set())),
            })

    # Tracker 3: Citation-per-year
    current_year = datetime.now().year
    cited_per_year: List[Dict[str, Any]] = []
    for url, p in paper_appearances.items():
        year = p.get("year")
        cites = p.get("citations", 0) or 0
        if year and year <= current_year and cites > 0:
            age = max(current_year - year, 1)
            cpy = cites / age
            cited_per_year.append({
                "url": p["url"],
                "title": p["title"],
                "year": year,
                "citations": cites,
                "age_years": age,
                "citations_per_year": round(cpy, 1),
            })
    cited_per_year.sort(key=lambda x: -x["citations_per_year"])

    return {
        "session": results.get("session", "(unknown)"),
        "total_searches": len(results.get("searches", [])),
        "unique_papers": len(paper_appearances),
        "repeat_hit_papers": repeat_hits[:TOP_REPEAT_HITS_N],
        "repeat_hit_count": len(repeat_hits),
        "recurring_authors": recurring_authors,
        "citations_per_year_top_5": cited_per_year[:5],
    }


def render_human(result: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append(f"Cross-search intelligence — session {result['session']}")
    out.append(f"  Total searches:           {result['total_searches']}")
    out.append(f"  Unique papers:            {result['unique_papers']}")
    out.append(f"  Repeat-hit papers (≥{REPEAT_HIT_THRESHOLD} sub-areas): {result['repeat_hit_count']}")
    out.append("")

    if result["repeat_hit_papers"]:
        out.append("Repeat-Hit Papers (foundational signal):")
        for p in result["repeat_hit_papers"]:
            authors_str = ", ".join(p["authors"][:3]) + (" et al." if len(p["authors"]) > 3 else "")
            out.append(f"  - {p['title']} ({authors_str}, {p['year']}) — {p['sub_area_count']} sub-areas, {p['citations']} cites")
            out.append(f"    Sub-areas: {', '.join(p['sub_areas'])}")
            out.append(f"    URL: {p['url']}")
    else:
        out.append("Repeat-Hit Papers: (none — increase search budget or check sub-area diversity)")
    out.append("")

    if result["recurring_authors"]:
        out.append(f"Recurring Authors (top {len(result['recurring_authors'])}):")
        for a in result["recurring_authors"]:
            out.append(f"  - {a['author']}: {a['appearances']} appearances across {len(a['sub_areas'])} sub-area(s)")
            out.append(f"    Sub-areas: {', '.join(a['sub_areas'])}")
    else:
        out.append("Recurring Authors: (none above threshold)")
    out.append("")

    if result["citations_per_year_top_5"]:
        out.append("Citations-per-Year top 5 (seminal-work heuristic):")
        for p in result["citations_per_year_top_5"]:
            out.append(f"  - {p['title']} ({p['year']}) — {p['citations']} cites / {p['age_years']} yr = {p['citations_per_year']}/yr")
    else:
        out.append("Citations-per-Year: (insufficient data)")

    return "\n".join(out)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--results-file", help="Path to search-results JSON file")
    parser.add_argument("--sample", action="store_true", help="Run on embedded sample results")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    if args.sample:
        result = aggregate(SAMPLE_RESULTS)
    elif args.results_file:
        p = Path(args.results_file)
        if not p.exists():
            print(f"error: {args.results_file} not found", file=sys.stderr); return 2
        try:
            data = json.loads(p.read_text(encoding="utf-8"))
        except json.JSONDecodeError as e:
            print(f"error: invalid JSON in {args.results_file}: {e}", file=sys.stderr); return 2
        result = aggregate(data)
    else:
        parser.print_help(); return 0

    if args.output == "json":
        print(json.dumps(result, indent=2, default=str))
    else:
        print(render_human(result))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
