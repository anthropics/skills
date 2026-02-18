#!/usr/bin/env python3
"""
Dream Swarm Multi-Domain Search Launcher

Starts a parallel search workflow across multiple data domains via MCP server.

Usage:
    python swarm-search.py "AI safety research" --domains arxiv github news
    python swarm-search.py "climate change" --agents 10 --parallel 5
    python swarm-search.py "quantum computing" --all-domains

Author: Luke Steuber
"""

import argparse
import json
import sys
import requests
from typing import List, Optional

MCP_BASE_URL = "http://localhost:5060"

# Available domains
ALL_DOMAINS = [
    "arxiv", "github", "news", "wikipedia", "pubmed", "semantic_scholar",
    "census", "nasa", "youtube", "weather", "openlibrary", "fec",
    "judiciary", "archive", "finance", "mal", "wolfram"
]

DEFAULT_DOMAINS = ["arxiv", "news", "wikipedia"]


def start_search(
    query: str,
    domains: List[str],
    num_agents: int = 5,
    max_parallel: int = 3,
    provider: str = "xai",
    model: Optional[str] = None,
    max_results: int = 10,
    stream: bool = False,
    output_format: str = "stdout"
) -> dict:
    """
    Start a Dream Swarm search workflow.

    Args:
        query: Search query
        domains: List of domains to search
        num_agents: Number of parallel agents (1-20)
        max_parallel: Max concurrent searches (1-10)
        provider: LLM provider for synthesis
        model: Specific model to use
        max_results: Results per domain
        stream: Enable SSE streaming
        output_format: Output format

    Returns:
        Workflow info dict
    """
    # Validate domains
    invalid = [d for d in domains if d not in ALL_DOMAINS]
    if invalid:
        return {"error": f"Invalid domains: {', '.join(invalid)}. Valid: {', '.join(ALL_DOMAINS)}"}

    payload = {
        "query": query,
        "num_agents": num_agents,
        "allowed_agent_types": domains,
        "provider_name": provider,
        "generate_documents": True,
        "document_formats": ["markdown"]
    }

    if model:
        payload["model"] = model

    try:
        response = requests.post(
            f"{MCP_BASE_URL}/mcp",
            json={
                "jsonrpc": "2.0",
                "id": 1,
                "method": "tools/call",
                "params": {
                    "name": "dream_orchestrate_search",
                    "arguments": payload
                }
            },
            timeout=30
        )
        response.raise_for_status()
        result = response.json()

        if "error" in result:
            return {"error": result["error"]["message"]}

        return result.get("result", result)

    except requests.exceptions.ConnectionError:
        return {"error": "Cannot connect to MCP server. Start with: sm start mcp-orchestrator"}
    except requests.exceptions.Timeout:
        return {"error": "Request timed out"}
    except Exception as e:
        return {"error": str(e)}


def stream_results(task_id: str):
    """Stream SSE events for a running search."""
    try:
        import sseclient
    except ImportError:
        print("SSE streaming requires: pip install sseclient-py", file=sys.stderr)
        return

    try:
        response = requests.get(f"{MCP_BASE_URL}/stream/{task_id}", stream=True)
        client = sseclient.SSEClient(response)

        for event in client.events():
            if event.event == "task_completed":
                data = json.loads(event.data)
                print(f"\n{'='*60}")
                print("SEARCH COMPLETED")
                print('='*60)
                print(json.dumps(data, indent=2))
                break
            elif event.event == "error":
                print(f"Error: {event.data}", file=sys.stderr)
                break
            else:
                print(f"[{event.event}] {event.data}")

    except KeyboardInterrupt:
        print("\nStreaming interrupted")
    except Exception as e:
        print(f"Streaming error: {e}", file=sys.stderr)


def format_output(result: dict, output_format: str) -> str:
    """Format the result for output."""
    if output_format == "json":
        return json.dumps(result, indent=2)
    elif output_format == "markdown":
        lines = [
            "# Search Results",
            "",
            f"**Task ID**: {result.get('task_id', 'N/A')}",
            f"**Status**: {result.get('status', 'N/A')}",
            ""
        ]
        if "results" in result:
            for domain, items in result["results"].items():
                lines.append(f"## {domain.title()}")
                lines.append("")
                for item in items[:5]:  # Show top 5 per domain
                    title = item.get("title", item.get("name", "Untitled"))
                    url = item.get("url", "")
                    lines.append(f"- [{title}]({url})")
                lines.append("")
        return "\n".join(lines)
    else:
        lines = [
            f"Task ID: {result.get('task_id', 'N/A')}",
            f"Status: {result.get('status', 'N/A')}"
        ]
        if "stream_url" in result:
            lines.append(f"Stream: {MCP_BASE_URL}{result['stream_url']}")
        if "message" in result:
            lines.append(f"Message: {result['message']}")
        if "error" in result:
            lines.append(f"Error: {result['error']}")
        return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="Launch Dream Swarm parallel multi-domain search",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=f"""
Available domains:
  {', '.join(ALL_DOMAINS)}

Examples:
  %(prog)s "AI safety" --domains arxiv github news
  %(prog)s "climate change" --agents 10 --parallel 5
  %(prog)s "quantum computing" --all-domains
  %(prog)s "market trends" --domains finance news --output json
        """
    )

    parser.add_argument(
        "query",
        help="Search query"
    )
    parser.add_argument(
        "--domains", "-d",
        default=",".join(DEFAULT_DOMAINS),
        help=f"Comma-separated domains (default: {','.join(DEFAULT_DOMAINS)})"
    )
    parser.add_argument(
        "--all-domains",
        action="store_true",
        help="Search all available domains"
    )
    parser.add_argument(
        "--agents", "-a",
        type=int,
        default=5,
        help="Number of parallel agents (1-20, default: 5)"
    )
    parser.add_argument(
        "--parallel", "-p",
        type=int,
        default=3,
        help="Max concurrent domain searches (1-10, default: 3)"
    )
    parser.add_argument(
        "--provider",
        default="xai",
        help="LLM provider for synthesis (default: xai)"
    )
    parser.add_argument(
        "--model", "-m",
        help="Specific model to use"
    )
    parser.add_argument(
        "--max-results",
        type=int,
        default=10,
        help="Max results per domain (default: 10)"
    )
    parser.add_argument(
        "--stream", "-s",
        action="store_true",
        help="Enable SSE streaming"
    )
    parser.add_argument(
        "--output", "-o",
        choices=["stdout", "json", "markdown"],
        default="stdout",
        help="Output format (default: stdout)"
    )
    parser.add_argument(
        "--list-domains",
        action="store_true",
        help="List all available domains and exit"
    )

    args = parser.parse_args()

    if args.list_domains:
        print("Available search domains:")
        for domain in ALL_DOMAINS:
            print(f"  - {domain}")
        sys.exit(0)

    # Parse domains
    if args.all_domains:
        domains = ALL_DOMAINS
    else:
        domains = [d.strip() for d in args.domains.split(",")]

    # Validate
    if not 1 <= args.agents <= 20:
        print("Error: agents must be between 1 and 20", file=sys.stderr)
        sys.exit(1)
    if not 1 <= args.parallel <= 10:
        print("Error: parallel must be between 1 and 10", file=sys.stderr)
        sys.exit(1)

    print(f"Starting Dream Swarm search...", file=sys.stderr)
    print(f"Query: {args.query}", file=sys.stderr)
    print(f"Domains: {', '.join(domains)}", file=sys.stderr)
    print(f"Agents: {args.agents}, Parallel: {args.parallel}", file=sys.stderr)
    print("", file=sys.stderr)

    result = start_search(
        query=args.query,
        domains=domains,
        num_agents=args.agents,
        max_parallel=args.parallel,
        provider=args.provider,
        model=args.model,
        max_results=args.max_results,
        stream=args.stream,
        output_format=args.output
    )

    print(format_output(result, args.output))

    if args.stream and "task_id" in result and "error" not in result:
        print("\nStreaming results...", file=sys.stderr)
        stream_results(result["task_id"])

    if "error" in result:
        sys.exit(1)


if __name__ == "__main__":
    main()
