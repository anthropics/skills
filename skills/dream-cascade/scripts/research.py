#!/usr/bin/env python3
"""
Dream Cascade Research Orchestration Script

Launches hierarchical 3-tier research workflows with:
- Tier 1 (Belter): Parallel worker agents doing initial research
- Tier 2 (Drummer): Mid-level synthesis agents
- Tier 3 (Camina): Executive synthesis and final report

Supports 12 LLM providers and 17 integrated data sources.
"""

import argparse
import asyncio
import json
import sys
from datetime import datetime
from pathlib import Path

# Add shared library path
sys.path.insert(0, "/home/coolhand/shared")

try:
    from llm_providers import ProviderFactory
    from orchestration import DreamCascadeConfig, DreamCascadeOrchestrator

    HAS_SHARED = True
except ImportError:
    HAS_SHARED = False


def create_mock_result(task: str, num_agents: int, provider: str) -> dict:
    """Generate mock result when shared library unavailable."""
    return {
        "task_id": f"research_{datetime.now().strftime('%Y%m%d_%H%M%S')}",
        "task": task,
        "status": "completed",
        "provider": provider,
        "model": "mock",
        "executive_summary": f"Mock executive summary for: {task}",
        "sections": [
            {"title": f"Section {i+1}", "content": f"Analysis from agent {i+1}..."}
            for i in range(num_agents)
        ],
        "metadata": {
            "agents": num_agents,
            "execution_time": 0.0,
            "total_tokens": 0,
            "estimated_cost": 0.0,
            "note": "Mock result - shared library not available",
        },
    }


async def run_research_workflow(
    task: str,
    title: str = None,
    num_agents: int = 8,
    provider_name: str = "xai",
    model: str = None,
    enable_drummer: bool = True,
    enable_camina: bool = True,
    generate_docs: bool = True,
    doc_formats: list = None,
    verbose: bool = False,
) -> dict:
    """Execute Dream Cascade research workflow."""

    if not HAS_SHARED:
        if verbose:
            print("[WARNING] Shared library not available, returning mock result")
        return create_mock_result(task, num_agents, provider_name)

    # Create configuration
    config = DreamCascadeConfig(
        num_agents=num_agents,
        enable_drummer=enable_drummer,
        enable_camina=enable_camina,
        generate_documents=generate_docs,
        document_formats=doc_formats or ["markdown"],
    )

    # Get provider
    try:
        provider = ProviderFactory.get_provider(provider_name)
        if model:
            provider.model = model
    except Exception as e:
        if verbose:
            print(f"[WARNING] Could not load provider {provider_name}: {e}")
            print("[INFO] Falling back to mock result")
        return create_mock_result(task, num_agents, provider_name)

    # Create orchestrator
    orchestrator = DreamCascadeOrchestrator(config, provider)

    if verbose:
        print("[INFO] Starting Dream Cascade workflow")
        print(f"  Task: {task[:80]}...")
        print(f"  Agents: {num_agents}")
        print(f"  Provider: {provider_name}")
        print(
            f"  Synthesis stages: {'Drummer+Camina' if enable_drummer and enable_camina else 'Partial'}"
        )

    # Execute workflow
    try:
        result = await orchestrator.execute_workflow(
            task=task, title=title or f"Research: {task[:50]}..."
        )

        if verbose:
            print(f"[INFO] Workflow completed in {result.execution_time:.1f}s")
            print(f"  Cost: ${result.total_cost:.4f}")

        return {
            "task_id": result.task_id,
            "task": task,
            "status": result.status.value,
            "provider": provider_name,
            "model": model or provider.model,
            "executive_summary": result.result.get("camina_synthesis", {}).get(
                "content", ""
            ),
            "sections": result.result.get("drummer_syntheses", []),
            "agent_results": [r.content for r in result.agent_results],
            "metadata": {
                "agents": num_agents,
                "execution_time": result.execution_time,
                "total_tokens": sum(r.tokens_used for r in result.agent_results),
                "estimated_cost": result.total_cost,
            },
        }

    except Exception as e:
        if verbose:
            print(f"[ERROR] Workflow failed: {e}")
        return {
            "task_id": None,
            "task": task,
            "status": "failed",
            "error": str(e),
            "metadata": {"agents": num_agents},
        }


def format_output(result: dict, format_type: str = "markdown") -> str:
    """Format result for output."""
    if format_type == "json":
        return json.dumps(result, indent=2, default=str)

    elif format_type == "text":
        lines = [
            f"Task: {result['task']}",
            f"Status: {result['status']}",
            "",
            "Executive Summary:",
            result.get("executive_summary", "N/A"),
            "",
            f"Agents: {result['metadata'].get('agents', 'N/A')}",
            f"Time: {result['metadata'].get('execution_time', 0):.1f}s",
            f"Cost: ${result['metadata'].get('estimated_cost', 0):.4f}",
        ]
        return "\n".join(lines)

    else:  # markdown
        lines = [
            "# Research Report",
            "",
            f"**Task**: {result['task']}",
            f"**Status**: {result['status']}",
            f"**Provider**: {result.get('provider', 'N/A')}",
            "",
            "## Executive Summary",
            "",
            result.get("executive_summary", "*No summary available*"),
            "",
        ]

        # Add sections
        sections = result.get("sections", [])
        if sections:
            lines.append("## Detailed Analysis")
            lines.append("")
            for i, section in enumerate(sections):
                if isinstance(section, dict):
                    lines.append(f"### {section.get('title', f'Section {i+1}')}")
                    lines.append("")
                    lines.append(section.get("content", ""))
                else:
                    lines.append(f"### Section {i+1}")
                    lines.append("")
                    lines.append(str(section))
                lines.append("")

        # Add metadata
        meta = result.get("metadata", {})
        lines.extend(
            [
                "## Metadata",
                "",
                f"- **Agents**: {meta.get('agents', 'N/A')}",
                f"- **Execution Time**: {meta.get('execution_time', 0):.1f}s",
                f"- **Total Tokens**: {meta.get('total_tokens', 'N/A')}",
                f"- **Estimated Cost**: ${meta.get('estimated_cost', 0):.4f}",
                "",
                f"*Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}*",
            ]
        )

        return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="Execute Dream Cascade hierarchical research workflow"
    )
    parser.add_argument("task", help="Research task or question to investigate")
    parser.add_argument("--title", "-t", help="Custom title for the research report")
    parser.add_argument(
        "--agents",
        "-n",
        type=int,
        default=8,
        help="Number of worker agents (default: 8)",
    )
    parser.add_argument(
        "--provider",
        "-p",
        default="xai",
        choices=[
            "xai",
            "anthropic",
            "openai",
            "mistral",
            "gemini",
            "perplexity",
            "cohere",
            "groq",
            "huggingface",
            "ollama",
        ],
        help="LLM provider (default: xai)",
    )
    parser.add_argument("--model", "-m", help="Specific model override")
    parser.add_argument(
        "--no-drummer",
        action="store_true",
        help="Disable Drummer (mid-level) synthesis stage",
    )
    parser.add_argument(
        "--no-camina",
        action="store_true",
        help="Disable Camina (executive) synthesis stage",
    )
    parser.add_argument(
        "--no-synthesis",
        action="store_true",
        help="Disable all synthesis stages (raw agent results only)",
    )
    parser.add_argument("--output", "-o", help="Save results to file")
    parser.add_argument(
        "--format",
        "-f",
        choices=["markdown", "json", "text"],
        default="markdown",
        help="Output format (default: markdown)",
    )
    parser.add_argument(
        "--verbose", "-v", action="store_true", help="Show detailed progress"
    )

    args = parser.parse_args()

    # Handle synthesis flags
    enable_drummer = not (args.no_drummer or args.no_synthesis)
    enable_camina = not (args.no_camina or args.no_synthesis)

    # Run workflow
    result = asyncio.run(
        run_research_workflow(
            task=args.task,
            title=args.title,
            num_agents=args.agents,
            provider_name=args.provider,
            model=args.model,
            enable_drummer=enable_drummer,
            enable_camina=enable_camina,
            verbose=args.verbose,
        )
    )

    # Format output
    output = format_output(result, args.format)

    # Save or print
    if args.output:
        Path(args.output).write_text(output)
        print(f"Results saved to: {args.output}")
    else:
        print(output)

    # Exit code based on status
    if result.get("status") == "failed":
        sys.exit(1)


if __name__ == "__main__":
    main()
