#!/usr/bin/env python3
"""
Dream Cascade/Swarm Workflow Status Script

Check status of running or completed research workflows.
Supports cancellation and results retrieval.
"""

import argparse
import json
import sys

# MCP client for workflow management
try:
    import requests

    HAS_REQUESTS = True
except ImportError:
    HAS_REQUESTS = False

MCP_BASE_URL = "http://localhost:5060"


def check_mcp_available() -> bool:
    """Check if MCP server is running."""
    if not HAS_REQUESTS:
        return False
    try:
        response = requests.get(f"{MCP_BASE_URL}/health", timeout=2)
        return response.status_code == 200
    except:
        return False


def get_status(task_id: str) -> dict:
    """Get workflow status from MCP server."""
    if not HAS_REQUESTS:
        return {"error": "requests library not available"}

    if not check_mcp_available():
        return {
            "error": "MCP server not available. Start with: sm start mcp-orchestrator"
        }

    try:
        response = requests.post(
            f"{MCP_BASE_URL}/tools/call",
            json={"name": "dreamwalker_status", "arguments": {"task_id": task_id}},
            timeout=30,
        )
        return response.json()
    except Exception as e:
        return {"error": str(e)}


def cancel_workflow(task_id: str) -> dict:
    """Cancel a running workflow."""
    if not HAS_REQUESTS:
        return {"error": "requests library not available"}

    if not check_mcp_available():
        return {
            "error": "MCP server not available. Start with: sm start mcp-orchestrator"
        }

    try:
        response = requests.post(
            f"{MCP_BASE_URL}/tools/call",
            json={"name": "dreamwalker_cancel", "arguments": {"task_id": task_id}},
            timeout=30,
        )
        return response.json()
    except Exception as e:
        return {"error": str(e)}


def get_results(task_id: str) -> dict:
    """Get full results of a completed workflow."""
    status = get_status(task_id)

    if "error" in status:
        return status

    if status.get("status") != "completed":
        return {
            "error": f"Workflow not completed. Current status: {status.get('status', 'unknown')}",
            "status": status,
        }

    # Results are included in status for completed workflows
    return status.get("result", {"error": "No results available"})


def format_status(status: dict, format_type: str = "text") -> str:
    """Format status for display."""
    if format_type == "json":
        return json.dumps(status, indent=2, default=str)

    if "error" in status:
        return f"Error: {status['error']}"

    lines = [
        f"Task ID: {status.get('task_id', 'N/A')}",
        f"Status: {status.get('status', 'unknown').upper()}",
        f"Type: {status.get('orchestrator_type', 'N/A')}",
        "",
    ]

    if status.get("status") == "running":
        result = status.get("result", {})
        progress = result.get("progress", 0)
        lines.extend(
            [
                f"Progress: {progress}%",
                f"Agents completed: {result.get('agents_completed', '?')}/{result.get('total_agents', '?')}",
                f"Execution time: {result.get('execution_time', 0):.1f}s",
                f"Estimated cost: ${result.get('estimated_cost', 0):.4f}",
            ]
        )
    elif status.get("status") == "completed":
        result = status.get("result", {})
        lines.extend(
            [
                f"Execution time: {result.get('execution_time', 0):.1f}s",
                f"Total cost: ${result.get('total_cost', 0):.4f}",
                f"Agents: {result.get('agent_count', 'N/A')}",
                f"Documents generated: {result.get('documents_generated', 0)}",
            ]
        )
    elif status.get("status") == "failed":
        lines.append(f"Error: {status.get('error', 'Unknown error')}")

    lines.extend(
        [
            "",
            f"Created: {status.get('created_at', 'N/A')}",
            f"Started: {status.get('started_at', 'N/A')}",
            f"Completed: {status.get('completed_at', 'N/A')}",
        ]
    )

    return "\n".join(lines)


def format_results(results: dict, format_type: str = "markdown") -> str:
    """Format full results for display."""
    if format_type == "json":
        return json.dumps(results, indent=2, default=str)

    if "error" in results:
        return f"Error: {results['error']}"

    lines = [
        "# Research Results",
        "",
        f"**Task ID**: {results.get('task_id', 'N/A')}",
        "",
        "## Executive Summary",
        "",
        results.get("executive_summary", "*No summary available*"),
        "",
    ]

    # Add sections if available
    sections = results.get("sections", [])
    if sections:
        lines.append("## Detailed Findings")
        lines.append("")
        for i, section in enumerate(sections):
            if isinstance(section, dict):
                lines.append(f"### {section.get('title', f'Section {i+1}')}")
                lines.append(section.get("content", ""))
            else:
                lines.append(f"### Section {i+1}")
                lines.append(str(section))
            lines.append("")

    # Metadata
    meta = results.get("metadata", {})
    if meta:
        lines.extend(
            [
                "## Metadata",
                "",
                f"- Agents: {meta.get('agent_count', 'N/A')}",
                f"- Execution time: {meta.get('execution_time', 0):.1f}s",
                f"- Total cost: ${meta.get('total_cost', 0):.4f}",
            ]
        )

    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="Check status of Dream Cascade/Swarm workflows"
    )
    parser.add_argument("task_id", help="Workflow task ID to check")
    parser.add_argument(
        "--cancel", "-c", action="store_true", help="Cancel the workflow"
    )
    parser.add_argument(
        "--results",
        "-r",
        action="store_true",
        help="Get full results (for completed workflows)",
    )
    parser.add_argument("--output", "-o", help="Save output to file")
    parser.add_argument(
        "--format",
        "-f",
        choices=["text", "json", "markdown"],
        default="text",
        help="Output format (default: text)",
    )

    args = parser.parse_args()

    # Execute requested action
    if args.cancel:
        result = cancel_workflow(args.task_id)
        output = (
            json.dumps(result, indent=2)
            if args.format == "json"
            else (
                f"Workflow {args.task_id} cancelled"
                if result.get("cancelled")
                else f"Error: {result.get('error', 'Unknown')}"
            )
        )
    elif args.results:
        result = get_results(args.task_id)
        output = format_results(result, args.format)
    else:
        result = get_status(args.task_id)
        output = format_status(result, args.format)

    # Output
    if args.output:
        from pathlib import Path

        Path(args.output).write_text(output)
        print(f"Saved to: {args.output}")
    else:
        print(output)

    # Exit code
    if "error" in result:
        sys.exit(1)


if __name__ == "__main__":
    main()
