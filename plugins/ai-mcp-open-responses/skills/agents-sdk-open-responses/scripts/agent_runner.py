#!/usr/bin/env python3
"""
Agent Runner Script

A configurable runner for OpenAI Agents SDK with Open Responses support.
Supports local and cloud providers with automatic fallback.

Usage:
    python agent_runner.py --task "Research quantum computing"
    python agent_runner.py --config agent_config.yaml --task "Write a report"
    python agent_runner.py --interactive
"""

import argparse
import asyncio
import json
import os
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

import yaml

try:
    from agents import Agent, Runner, function_tool, handoff, RunConfig
    from openai import AsyncOpenAI
    from pydantic import Field
except ImportError:
    print("Error: Required packages not installed.")
    print("Run: pip install openai-agents openai pydantic")
    sys.exit(1)


# =============================================================================
# Configuration
# =============================================================================

@dataclass
class ProviderConfig:
    """Configuration for an LLM provider."""
    name: str
    base_url: str
    api_key_env: str
    default_model: str


@dataclass
class AgentConfig:
    """Configuration for an agent."""
    name: str
    instructions: str
    model: str
    tools: list[str]
    max_turns: int = 10
    max_tool_calls: int = 50
    timeout: int = 300


DEFAULT_PROVIDERS = {
    "openai": ProviderConfig(
        name="openai",
        base_url="https://api.openai.com/v1",
        api_key_env="OPENAI_API_KEY",
        default_model="gpt-4o",
    ),
    "anthropic": ProviderConfig(
        name="anthropic",
        base_url="https://api.anthropic.com/v1",
        api_key_env="ANTHROPIC_API_KEY",
        default_model="claude-sonnet-4-20250514",
    ),
    "local": ProviderConfig(
        name="local",
        base_url="http://localhost:8080/v1",
        api_key_env="LOCAL_API_KEY",
        default_model="local/llama3.2",
    ),
    "ollama": ProviderConfig(
        name="ollama",
        base_url="http://localhost:11434/v1",
        api_key_env="OLLAMA_API_KEY",
        default_model="llama3.2",
    ),
}


# =============================================================================
# Tools
# =============================================================================

@function_tool
def web_search(
    query: str = Field(..., description="Search query"),
    max_results: int = Field(5, ge=1, le=20, description="Maximum results"),
) -> str:
    """Search the web for information."""
    # Placeholder implementation
    return f"Search results for '{query}': [No results - implement actual search]"


@function_tool
def read_file(
    path: str = Field(..., description="File path to read"),
    encoding: str = Field("utf-8", description="File encoding"),
) -> str:
    """Read contents of a file."""
    try:
        with open(path, "r", encoding=encoding) as f:
            content = f.read()
        return content[:10000] + ("..." if len(content) > 10000 else "")
    except Exception as e:
        return f"Error reading file: {e}"


@function_tool
def write_file(
    path: str = Field(..., description="File path to write"),
    content: str = Field(..., description="Content to write"),
    encoding: str = Field("utf-8", description="File encoding"),
) -> str:
    """Write content to a file."""
    try:
        with open(path, "w", encoding=encoding) as f:
            f.write(content)
        return f"Successfully wrote {len(content)} characters to {path}"
    except Exception as e:
        return f"Error writing file: {e}"


@function_tool
def execute_code(
    code: str = Field(..., description="Python code to execute"),
    timeout: int = Field(30, ge=1, le=300, description="Timeout in seconds"),
) -> str:
    """Execute Python code in a sandboxed environment."""
    # WARNING: This is a placeholder. Use proper sandboxing in production!
    return "Code execution disabled for safety. Implement sandboxed execution."


AVAILABLE_TOOLS = {
    "web_search": web_search,
    "read_file": read_file,
    "write_file": write_file,
    "execute_code": execute_code,
}


# =============================================================================
# Agent Factory
# =============================================================================

def create_agent(config: AgentConfig) -> Agent:
    """Create an agent from configuration."""
    tools = [AVAILABLE_TOOLS[name] for name in config.tools if name in AVAILABLE_TOOLS]

    return Agent(
        name=config.name,
        instructions=config.instructions,
        model=config.model,
        tools=tools,
    )


def create_client(provider: str) -> AsyncOpenAI:
    """Create an OpenAI-compatible client for the specified provider."""
    if provider not in DEFAULT_PROVIDERS:
        raise ValueError(f"Unknown provider: {provider}")

    config = DEFAULT_PROVIDERS[provider]
    api_key = os.environ.get(config.api_key_env, "dummy-key")

    return AsyncOpenAI(
        base_url=config.base_url,
        api_key=api_key,
    )


# =============================================================================
# Runner
# =============================================================================

async def run_agent(
    task: str,
    agent_config: AgentConfig,
    provider: str = "local",
    verbose: bool = False,
) -> str:
    """Run an agent on a task."""

    agent = create_agent(agent_config)
    client = create_client(provider)

    run_config = RunConfig(
        max_turns=agent_config.max_turns,
        max_tool_calls=agent_config.max_tool_calls,
        timeout=agent_config.timeout,
    )

    if verbose:
        print(f"Running agent '{agent.name}' on task: {task[:100]}...")
        print(f"Provider: {provider}")
        print(f"Model: {agent_config.model}")
        print("-" * 60)

    runner = Runner(agent=agent, client=client, config=run_config)
    result = await runner.run(task)

    if verbose:
        print("-" * 60)
        print(f"Completed in {len(result.trace)} turns")

    return result.final_output


async def interactive_mode(agent_config: AgentConfig, provider: str):
    """Run agent in interactive mode."""
    print("=" * 60)
    print(f"Interactive Agent: {agent_config.name}")
    print(f"Provider: {provider} | Model: {agent_config.model}")
    print("Type 'exit' or 'quit' to end session")
    print("=" * 60)

    while True:
        try:
            task = input("\nYou: ").strip()
            if task.lower() in ("exit", "quit", "q"):
                print("Goodbye!")
                break
            if not task:
                continue

            result = await run_agent(task, agent_config, provider, verbose=False)
            print(f"\nAgent: {result}")

        except KeyboardInterrupt:
            print("\nGoodbye!")
            break
        except Exception as e:
            print(f"\nError: {e}")


# =============================================================================
# Configuration Loading
# =============================================================================

def load_config(config_path: str) -> AgentConfig:
    """Load agent configuration from YAML file."""
    with open(config_path, "r") as f:
        data = yaml.safe_load(f)

    return AgentConfig(
        name=data.get("name", "Assistant"),
        instructions=data.get("instructions", "You are a helpful assistant."),
        model=data.get("model", "local/llama3.2"),
        tools=data.get("tools", []),
        max_turns=data.get("max_turns", 10),
        max_tool_calls=data.get("max_tool_calls", 50),
        timeout=data.get("timeout", 300),
    )


def get_default_config() -> AgentConfig:
    """Get default agent configuration."""
    return AgentConfig(
        name="Assistant",
        instructions="""You are a helpful AI assistant.

Your capabilities:
- Answer questions accurately and concisely
- Help with research and analysis
- Assist with writing and editing
- Provide explanations and tutorials

Guidelines:
- Be helpful, harmless, and honest
- Acknowledge when you don't know something
- Ask clarifying questions when needed""",
        model="local/llama3.2",
        tools=["web_search", "read_file"],
    )


# =============================================================================
# Main
# =============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="OpenAI Agents SDK Runner with Open Responses",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s --task "Explain quantum computing"
  %(prog)s --provider openai --task "Write a haiku"
  %(prog)s --config my_agent.yaml --interactive
  %(prog)s --list-providers
        """,
    )

    parser.add_argument("--task", "-t", help="Task for the agent to perform")
    parser.add_argument("--config", "-c", help="Path to agent configuration YAML")
    parser.add_argument(
        "--provider",
        "-p",
        default="local",
        choices=list(DEFAULT_PROVIDERS.keys()),
        help="LLM provider to use",
    )
    parser.add_argument(
        "--interactive",
        "-i",
        action="store_true",
        help="Run in interactive mode",
    )
    parser.add_argument("--verbose", "-v", action="store_true", help="Verbose output")
    parser.add_argument(
        "--list-providers",
        action="store_true",
        help="List available providers",
    )

    args = parser.parse_args()

    if args.list_providers:
        print("Available providers:")
        for name, config in DEFAULT_PROVIDERS.items():
            print(f"  {name}:")
            print(f"    Base URL: {config.base_url}")
            print(f"    Default Model: {config.default_model}")
            print(f"    API Key Env: {config.api_key_env}")
        return

    # Load configuration
    if args.config:
        agent_config = load_config(args.config)
    else:
        agent_config = get_default_config()

    # Run agent
    if args.interactive:
        asyncio.run(interactive_mode(agent_config, args.provider))
    elif args.task:
        result = asyncio.run(
            run_agent(args.task, agent_config, args.provider, args.verbose)
        )
        print(result)
    else:
        parser.print_help()
        print("\nError: Either --task or --interactive is required")
        sys.exit(1)


if __name__ == "__main__":
    main()
