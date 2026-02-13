#!/usr/bin/env python3
"""Scaffold a new Strands Agents project with uv in the user's working directory."""

import argparse
import os
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description="Scaffold a Strands Agents project")
    parser.add_argument("name", help="Project name (will create directory)")
    parser.add_argument("--path", default=".", help="Parent directory (default: current)")
    parser.add_argument(
        "--extras",
        nargs="*",
        default=[],
        choices=["bedrock-agentcore", "evals", "fastapi", "mcp", "bidi"],
        help="Optional extras to include",
    )
    args = parser.parse_args()

    project_dir = os.path.join(os.path.abspath(args.path), args.name)

    if os.path.exists(project_dir):
        print(f"[ERROR] Directory already exists: {project_dir}")
        sys.exit(1)

    print(f"[START] Creating Strands Agents project: {args.name}")
    print(f"   Location: {project_dir}")

    # Initialize uv project
    subprocess.run(["uv", "init", "--python", "3.12", project_dir], check=True)

    # Core dependencies (no version pins - always latest)
    deps = [
        "strands-agents",
        "strands-agents-tools",
        "strands-agents-builder",
        "boto3",
    ]

    # Optional extras
    if "bedrock-agentcore" in args.extras:
        deps.extend(["bedrock-agentcore", "bedrock-agentcore-starter-toolkit"])
    if "evals" in args.extras:
        deps.append("strands-agents-evals")
    if "fastapi" in args.extras:
        deps.extend(["fastapi", "uvicorn[standard]", "pydantic", "httpx"])
    if "mcp" in args.extras:
        deps.append("strands-agents[mcp]")
    if "bidi" in args.extras:
        deps.append("strands-agents[bidi-all]")

    # Add dependencies
    print(f"[OK] Adding dependencies: {', '.join(deps)}")
    subprocess.run(["uv", "add"] + deps, cwd=project_dir, check=True)

    # Create project structure
    src_dir = os.path.join(project_dir, "src")
    tools_dir = os.path.join(project_dir, "tools")
    tests_dir = os.path.join(project_dir, "tests")

    for d in [src_dir, tools_dir, tests_dir]:
        os.makedirs(d, exist_ok=True)

    # Create starter agent file
    agent_py = os.path.join(src_dir, "agent.py")
    with open(agent_py, "w") as f:
        f.write('''"""Strands Agent - main entry point."""

from strands import Agent, tool
from strands_tools import calculator, current_time


@tool
def greet(name: str) -> str:
    """Greet a user by name.

    Args:
        name: The name of the user to greet
    """
    return f"Hello, {name}! Welcome to Strands Agents."


agent = Agent(
    tools=[calculator, current_time, greet],
    system_prompt="You are a helpful assistant powered by Strands Agents.",
)

if __name__ == "__main__":
    agent("Hello! What can you do?")
''')

    # Create __init__.py files
    for d in [src_dir, tools_dir, tests_dir]:
        with open(os.path.join(d, "__init__.py"), "w") as f:
            f.write("")

    # Create example custom tool
    with open(os.path.join(tools_dir, "example_tool.py"), "w") as f:
        f.write('''"""Example custom tool for your Strands Agent."""

from strands import tool


@tool
def search_knowledge(query: str, max_results: int = 5) -> str:
    """Search a knowledge base for relevant information.

    Args:
        query: The search query
        max_results: Maximum number of results to return
    """
    # Replace with your actual implementation
    return f"Found {max_results} results for: {query}"
''')

    print(f"[OK] Created project structure")
    print(f"[OK] Strands Agents project '{args.name}' is ready at {project_dir}")
    print()
    print("Next steps:")
    print(f"  cd {project_dir}")
    print(f"  uv run python src/agent.py")


if __name__ == "__main__":
    main()
