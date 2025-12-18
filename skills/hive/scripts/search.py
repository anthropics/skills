#!/usr/bin/env python3
"""
Hive Search Tools - Web, image, and map search.

Usage:
    python search.py "query"                    # Web search
    python search.py "query" --type image       # Image search
    python search.py "query" --provider brave   # Specific provider
    python search.py "query" -n 20              # More results
"""

import argparse
import json
import os
import sys

PROVIDERS = {
    "brave": {"name": "Brave Search", "env": "BRAVE_API_KEY", "types": ["web", "image"]},
    "tavily": {"name": "Tavily", "env": "TAVILY_API_KEY", "types": ["web"]},
    "serpapi": {"name": "SerpAPI", "env": "SERPAPI_API_KEY", "types": ["web", "image"]},
    "google": {"name": "Google", "env": "GOOGLE_API_KEY", "types": ["web", "image", "map"]}
}

def search(query: str, search_type: str = "web", provider: str = "brave",
           num_results: int = 10, output_format: str = "text") -> dict:
    """Execute search query."""
    # Validate provider
    if provider not in PROVIDERS:
        return {"error": f"Unknown provider: {provider}", "available": list(PROVIDERS.keys())}

    provider_info = PROVIDERS[provider]

    # Check API key
    api_key = os.environ.get(provider_info["env"])
    if not api_key:
        return {
            "error": f"Missing API key: {provider_info['env']}",
            "hint": f"Set {provider_info['env']} environment variable"
        }

    # Validate search type for provider
    if search_type not in provider_info["types"]:
        return {
            "error": f"Provider {provider} doesn't support {search_type} search",
            "supported": provider_info["types"]
        }

    # Execute search (placeholder - would call actual API)
    print(f"Searching ({search_type}): {query}")
    print(f"Provider: {provider_info['name']}")
    print(f"Results requested: {num_results}")

    # Mock results
    results = {
        "query": query,
        "type": search_type,
        "provider": provider,
        "results": [
            {
                "title": f"Result {i+1} for: {query}",
                "url": f"https://example.com/result{i+1}",
                "snippet": f"This is a sample result snippet for '{query}'..."
            }
            for i in range(min(3, num_results))
        ],
        "total_results": num_results,
        "note": "This is a demonstration. Connect to actual search APIs for real results."
    }

    return results

def format_output(results: dict, output_format: str) -> str:
    """Format results for display."""
    if output_format == "json":
        return json.dumps(results, indent=2)

    if "error" in results:
        return f"Error: {results['error']}\n{results.get('hint', '')}"

    lines = [
        f"Search: {results['query']}",
        f"Type: {results['type']}",
        f"Provider: {results['provider']}",
        f"Results: {len(results['results'])}",
        "-" * 40
    ]

    for i, r in enumerate(results["results"], 1):
        lines.append(f"\n{i}. {r['title']}")
        lines.append(f"   {r['url']}")
        lines.append(f"   {r['snippet']}")

    if results.get("note"):
        lines.append(f"\nNote: {results['note']}")

    return "\n".join(lines)

def main():
    parser = argparse.ArgumentParser(
        description="Hive Search Tools - Web, image, and map search",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python search.py "latest AI news"           Web search
  python search.py "cats" --type image        Image search
  python search.py "coffee shops" --type map  Map search
  python search.py "query" --provider tavily  Use Tavily
  python search.py "query" -n 20 --json       20 results as JSON

Providers:
  brave   - Brave Search (web, image)
  tavily  - Tavily AI Search (web)
  serpapi - SerpAPI Google proxy (web, image)
  google  - Google APIs (web, image, map)
        """
    )

    parser.add_argument("query", help="Search query")
    parser.add_argument("--type", "-t", choices=["web", "image", "map"],
                       default="web", help="Search type (default: web)")
    parser.add_argument("--provider", "-p", choices=list(PROVIDERS.keys()),
                       default="brave", help="Search provider (default: brave)")
    parser.add_argument("--num-results", "-n", type=int, default=10,
                       help="Number of results (default: 10)")
    parser.add_argument("--json", action="store_true", help="Output as JSON")
    parser.add_argument("--output", "-o", help="Save results to file")

    args = parser.parse_args()

    output_format = "json" if args.json else "text"
    results = search(args.query, args.type, args.provider, args.num_results, output_format)
    output = format_output(results, output_format)

    if args.output:
        with open(args.output, "w") as f:
            f.write(output)
        print(f"Results saved to: {args.output}")
    else:
        print(output)

if __name__ == "__main__":
    main()
