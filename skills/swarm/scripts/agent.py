#!/usr/bin/env python3
"""
Swarm Agent - Interactive AI agent session with tool access.

Usage:
    python agent.py                           # Start interactive session
    python agent.py --provider anthropic      # Use specific provider
    python agent.py --tools search,research   # Limit available tools
    python agent.py --stream                  # Enable streaming output
    python agent.py "Your query"              # One-shot query
"""

import argparse
import os
import sys
import json

PROVIDERS = ["xai", "anthropic", "openai", "mistral", "gemini", "perplexity", "cohere", "groq"]

def create_agent(provider: str, model: str = None, tools: list = None):
    """Create a swarm agent instance."""
    agent_config = {
        "provider": provider,
        "model": model or get_default_model(provider),
        "tools": tools or ["all"],
        "conversation_memory": True,
        "streaming": False
    }
    return agent_config

def get_default_model(provider: str) -> str:
    """Get default model for provider."""
    defaults = {
        "xai": "grok-3",
        "anthropic": "claude-3-5-sonnet-20241022",
        "openai": "gpt-4-turbo",
        "mistral": "mistral-large-latest",
        "gemini": "gemini-2.0-flash",
        "perplexity": "sonar-pro",
        "cohere": "command-r-plus",
        "groq": "llama-3.3-70b-versatile"
    }
    return defaults.get(provider, "grok-3")

def run_interactive(config: dict, stream: bool = False):
    """Run interactive agent session."""
    print(f"Swarm Agent - Provider: {config['provider']}, Model: {config['model']}")
    print(f"Tools: {', '.join(config['tools'])}")
    print("Type 'exit' or 'quit' to end session, 'tools' to list available tools")
    print("-" * 50)

    conversation = []

    while True:
        try:
            user_input = input("\n> ").strip()
        except (EOFError, KeyboardInterrupt):
            print("\nEnding session.")
            break

        if not user_input:
            continue

        if user_input.lower() in ["exit", "quit", "q"]:
            print("Ending session.")
            break

        if user_input.lower() == "tools":
            print_available_tools(config["tools"])
            continue

        if user_input.lower() == "clear":
            conversation = []
            print("Conversation cleared.")
            continue

        # Add to conversation
        conversation.append({"role": "user", "content": user_input})

        # Process query (placeholder for actual implementation)
        response = process_query(config, conversation, stream)

        if response:
            conversation.append({"role": "assistant", "content": response})
            print(f"\n{response}")

def process_query(config: dict, conversation: list, stream: bool) -> str:
    """Process user query with agent."""
    # This would connect to actual swarm agent
    # For now, return placeholder
    query = conversation[-1]["content"]

    print(f"\n[Agent processing with {config['provider']}...]")

    # Check for tool-requiring queries
    tool_hints = {
        "search": ["search", "find", "look up", "google"],
        "research": ["paper", "arxiv", "pubmed", "academic", "research"],
        "generate": ["generate image", "create image", "draw", "illustrate"],
        "weather": ["weather", "temperature", "forecast"],
        "finance": ["stock", "market", "price", "trading"]
    }

    for tool, keywords in tool_hints.items():
        if any(kw in query.lower() for kw in keywords):
            print(f"[Would invoke {tool} tool]")

    return f"[Response to: {query}]\n\nTo use this agent with full functionality, ensure the swarm system is installed and configured with API keys."

def print_available_tools(enabled_tools: list):
    """Print available tools."""
    all_tools = {
        "search": ["web_search", "image_search", "map_search"],
        "research": ["arxiv_search", "pubmed_search", "scholar_search"],
        "gen": ["generate_image", "edit_image"],
        "finance": ["stock_quote", "market_data"],
        "data": ["fetch_json", "parse_csv"],
        "news": ["headlines", "article_search"],
        "chat": ["llm_query", "summarize"],
        "executor": ["run_code", "shell_command"]
    }

    print("\nAvailable Tools:")
    for module, tools in all_tools.items():
        if enabled_tools == ["all"] or module in enabled_tools:
            print(f"\n  {module}:")
            for tool in tools:
                print(f"    - {tool}")

def run_oneshot(config: dict, query: str, stream: bool = False) -> str:
    """Run single query and exit."""
    conversation = [{"role": "user", "content": query}]
    return process_query(config, conversation, stream)

def main():
    parser = argparse.ArgumentParser(
        description="Swarm Agent - Interactive AI agent with tool access",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python agent.py                           Start interactive session
  python agent.py --provider anthropic      Use Claude
  python agent.py --tools search,research   Limit to specific tools
  python agent.py "What is quantum computing?"  One-shot query
        """
    )

    parser.add_argument("query", nargs="?", help="One-shot query (optional)")
    parser.add_argument("--provider", "-p", choices=PROVIDERS, default="xai",
                       help="LLM provider (default: xai)")
    parser.add_argument("--model", "-m", help="Specific model override")
    parser.add_argument("--tools", "-t", help="Comma-separated list of tool modules")
    parser.add_argument("--stream", action="store_true", help="Enable streaming output")
    parser.add_argument("--new-session", action="store_true", help="Start fresh session")
    parser.add_argument("--max-cycles", "-c", type=int, default=10,
                       help="Maximum tool execution cycles (default: 10)")
    parser.add_argument("--verbose", "-v", action="store_true", help="Verbose output")

    args = parser.parse_args()

    # Parse tools
    tools = args.tools.split(",") if args.tools else ["all"]

    # Create agent config
    config = create_agent(args.provider, args.model, tools)
    config["max_cycles"] = args.max_cycles
    config["verbose"] = args.verbose

    if args.query:
        # One-shot mode
        response = run_oneshot(config, args.query, args.stream)
        print(response)
    else:
        # Interactive mode
        run_interactive(config, args.stream)

if __name__ == "__main__":
    main()
