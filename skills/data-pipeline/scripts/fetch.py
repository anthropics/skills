#!/usr/bin/env python3
"""
Data Fetching Script

Fetch data from 17 integrated sources:
- arxiv, semantic_scholar, pubmed (academic)
- wikipedia, openlibrary (reference)
- github, youtube, news (content)
- nasa, weather, census (public data)
- finance, wolfram, archive (specialized)
- fec, judiciary, mal (niche)
"""

import argparse
import json
import sys
from datetime import datetime
from pathlib import Path

# Add shared library path
sys.path.insert(0, "/home/coolhand/shared")

try:
    from data_fetching import ClientFactory

    HAS_SHARED = True
except ImportError:
    HAS_SHARED = False


# Mock data generators for when shared library unavailable
MOCK_DATA = {
    "arxiv": lambda q, n: {
        "source": "arxiv",
        "query": q,
        "count": n,
        "results": [
            {
                "id": f"2401.{10000+i}",
                "title": f"Paper {i+1} about {q}",
                "authors": ["Author"],
                "abstract": "...",
            }
            for i in range(min(n, 5))
        ],
        "note": "Mock data - shared library not available",
    },
    "github": lambda q, n: {
        "source": "github",
        "query": q,
        "count": n,
        "results": [
            {
                "name": f"repo-{i+1}",
                "owner": "user",
                "stars": 100 - i * 10,
                "url": f"https://github.com/user/repo-{i+1}",
            }
            for i in range(min(n, 5))
        ],
        "note": "Mock data - shared library not available",
    },
    "wikipedia": lambda q, n: {
        "source": "wikipedia",
        "query": q,
        "count": n,
        "results": [
            {
                "title": f"{q} (article {i+1})",
                "url": f"https://en.wikipedia.org/wiki/{q.replace(' ', '_')}",
                "snippet": "...",
            }
            for i in range(min(n, 5))
        ],
        "note": "Mock data - shared library not available",
    },
}


def fetch_data(
    source: str,
    query: str,
    max_results: int = 10,
    use_cache: bool = True,
    verbose: bool = False,
) -> dict:
    """Fetch data from specified source."""

    if not HAS_SHARED:
        if verbose:
            print("[WARNING] Shared library not available, returning mock data")
        mock_fn = MOCK_DATA.get(source, MOCK_DATA["arxiv"])
        return mock_fn(query, max_results)

    try:
        client = ClientFactory.create_client(source)

        if verbose:
            print(f"[INFO] Fetching from {source}: {query}")

        results = client.search(query=query, max_results=max_results)

        return {
            "source": source,
            "query": query,
            "count": len(results)
            if isinstance(results, list)
            else results.get("count", 0),
            "timestamp": datetime.now().isoformat(),
            "results": results
            if isinstance(results, list)
            else results.get("results", []),
        }

    except Exception as e:
        if verbose:
            print(f"[ERROR] Fetch failed: {e}")
        return {
            "source": source,
            "query": query,
            "count": 0,
            "error": str(e),
            "results": [],
        }


def format_output(data: dict, format_type: str = "json") -> str:
    """Format data for output."""
    if format_type == "json":
        return json.dumps(data, indent=2, default=str)

    elif format_type == "csv":
        results = data.get("results", [])
        if not results:
            return "No results"

        # Get headers from first result
        if isinstance(results[0], dict):
            headers = list(results[0].keys())
            lines = [",".join(headers)]
            for r in results:
                values = [
                    str(r.get(h, "")).replace(",", ";").replace("\n", " ")[:100]
                    for h in headers
                ]
                lines.append(",".join(values))
            return "\n".join(lines)
        else:
            return "\n".join(str(r) for r in results)

    else:  # markdown
        lines = [
            f"# Search Results: {data.get('query', 'N/A')}",
            "",
            f"**Source**: {data.get('source', 'N/A')}",
            f"**Count**: {data.get('count', 0)}",
            f"**Date**: {data.get('timestamp', 'N/A')}",
            "",
        ]

        if "note" in data:
            lines.append(f"*{data['note']}*")
            lines.append("")

        if "error" in data:
            lines.append(f"**Error**: {data['error']}")
            lines.append("")

        results = data.get("results", [])
        for i, r in enumerate(results[:20]):  # Limit display
            if isinstance(r, dict):
                title = r.get("title") or r.get("name") or f"Result {i+1}"
                lines.append(f"## {title}")
                for k, v in r.items():
                    if k not in ["title", "name"] and v:
                        lines.append(f"- **{k}**: {str(v)[:200]}")
                lines.append("")
            else:
                lines.append(f"- {str(r)[:200]}")

        if len(results) > 20:
            lines.append(f"*... and {len(results) - 20} more results*")

        return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description="Fetch data from integrated sources")
    parser.add_argument("query", nargs="?", help="Search query")
    parser.add_argument(
        "--source",
        "-s",
        default="arxiv",
        choices=[
            "arxiv",
            "semantic_scholar",
            "pubmed",
            "openlibrary",
            "wikipedia",
            "github",
            "news",
            "youtube",
            "nasa",
            "weather",
            "census",
            "fec",
            "judiciary",
            "finance",
            "wolfram",
            "archive",
            "mal",
        ],
        help="Data source (default: arxiv)",
    )
    parser.add_argument(
        "--max", "-m", type=int, default=10, help="Maximum results (default: 10)"
    )
    parser.add_argument("--output", "-o", help="Save output to file")
    parser.add_argument(
        "--format",
        "-f",
        choices=["json", "csv", "markdown"],
        default="json",
        help="Output format (default: json)",
    )
    parser.add_argument(
        "--cache", action="store_true", help="Use cached results if available"
    )
    parser.add_argument(
        "--no-cache", action="store_true", help="Force fresh fetch (ignore cache)"
    )
    parser.add_argument(
        "--verbose", "-v", action="store_true", help="Show detailed progress"
    )
    parser.add_argument(
        "--list-sources", action="store_true", help="List all available sources"
    )

    args = parser.parse_args()

    if args.list_sources:
        sources = """
Available Data Sources:

Academic:
  arxiv           - Papers and preprints
  semantic_scholar - Paper metadata, citations
  pubmed          - Medical/biology research

Reference:
  wikipedia       - Encyclopedia articles
  openlibrary     - Book catalog

Content:
  github          - Repositories, users, code
  youtube         - Video search, metadata
  news            - Headlines, articles

Public Data:
  nasa            - Space, astronomy
  weather         - Forecasts, conditions
  census          - Demographics, ACS

Specialized:
  finance         - Stocks, markets
  wolfram         - Computation engine
  archive         - Internet Archive

Niche:
  fec             - Election data
  judiciary       - Legal decisions
  mal             - Anime database
"""
        print(sources)
        return

    if not args.query:
        parser.error("Query is required (or use --list-sources)")

    # Fetch data
    data = fetch_data(
        source=args.source,
        query=args.query,
        max_results=args.max,
        use_cache=args.cache and not args.no_cache,
        verbose=args.verbose,
    )

    # Format output
    output = format_output(data, args.format)

    # Save or print
    if args.output:
        Path(args.output).write_text(output)
        print(f"Results saved to: {args.output}")
        print(f"Found {data.get('count', 0)} results from {args.source}")
    else:
        print(output)

    # Exit code
    if "error" in data:
        sys.exit(1)


if __name__ == "__main__":
    main()
