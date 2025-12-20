#!/usr/bin/env python3
"""
Swarm Task Runner - Execute predefined tasks with streaming output.

Usage:
    python task.py --list                           # List available tasks
    python task.py research_deep "AI safety"        # Run research task
    python task.py business_planner "Startup idea"  # Run planning task
    python task.py research_deep "Topic" -o out.md  # Save to file
"""

import argparse
import os
import sys
import json
from datetime import datetime

# Predefined task configurations
TASKS = {
    "research_deep": {
        "description": "Deep research with academic sources and synthesis",
        "tools": ["search", "research", "chat"],
        "max_cycles": 15,
        "system_prompt": "You are a thorough researcher. Search multiple sources, synthesize findings, and provide comprehensive analysis with citations."
    },
    "research_quick": {
        "description": "Quick web research for timely information",
        "tools": ["search", "news"],
        "max_cycles": 5,
        "system_prompt": "You are a quick researcher. Find relevant current information and summarize key points."
    },
    "business_planner": {
        "description": "Business plan generation with market analysis",
        "tools": ["search", "finance", "chat"],
        "max_cycles": 10,
        "system_prompt": "You are a business strategist. Analyze markets, competitors, and create comprehensive business plans."
    },
    "code_assistant": {
        "description": "Programming help with code generation",
        "tools": ["search", "executor", "chat"],
        "max_cycles": 10,
        "system_prompt": "You are a senior developer. Help with code, explain concepts, and suggest best practices."
    },
    "creative_writer": {
        "description": "Creative content generation",
        "tools": ["search", "gen", "chat"],
        "max_cycles": 8,
        "system_prompt": "You are a creative writer. Generate engaging content with vivid descriptions."
    },
    "data_analyst": {
        "description": "Data analysis and visualization recommendations",
        "tools": ["search", "data", "finance", "chat"],
        "max_cycles": 12,
        "system_prompt": "You are a data analyst. Analyze data, identify patterns, and provide insights."
    }
}

def list_tasks():
    """List all available tasks."""
    print("Available Tasks:\n")
    for name, config in TASKS.items():
        print(f"  {name}")
        print(f"    {config['description']}")
        print(f"    Tools: {', '.join(config['tools'])}")
        print(f"    Max cycles: {config['max_cycles']}")
        print()

def run_task(task_name: str, prompt: str, output: str = None, verbose: bool = False):
    """Run a predefined task."""
    if task_name not in TASKS:
        print(f"Error: Unknown task '{task_name}'")
        print(f"Available tasks: {', '.join(TASKS.keys())}")
        sys.exit(1)

    task = TASKS[task_name]

    print(f"Running task: {task_name}")
    print(f"Prompt: {prompt}")
    print(f"Tools: {', '.join(task['tools'])}")
    print("-" * 50)

    # Task execution (placeholder)
    result = execute_task(task, prompt, verbose)

    # Output handling
    if output:
        save_result(result, output)
        print(f"\nResult saved to: {output}")
    else:
        print("\nResult:")
        print(result["content"])

    return result

def execute_task(task: dict, prompt: str, verbose: bool = False) -> dict:
    """Execute task with swarm agent."""
    # This would connect to actual swarm system
    # Placeholder implementation

    if verbose:
        print(f"\n[System: {task['system_prompt'][:50]}...]")
        print(f"[Max cycles: {task['max_cycles']}]")

    # Simulate task stages
    stages = [
        ("Planning", "Analyzing task requirements..."),
        ("Research", "Gathering information from sources..."),
        ("Analysis", "Processing and synthesizing data..."),
        ("Generation", "Creating final output...")
    ]

    for stage, description in stages:
        if verbose:
            print(f"[{stage}] {description}")

    return {
        "task": task,
        "prompt": prompt,
        "content": f"[Task result for: {prompt}]\n\nTo use this task runner with full functionality, ensure the swarm system is installed and configured.",
        "metadata": {
            "timestamp": datetime.now().isoformat(),
            "cycles_used": 1,
            "tools_invoked": []
        }
    }

def save_result(result: dict, output_path: str):
    """Save result to file."""
    ext = os.path.splitext(output_path)[1].lower()

    with open(output_path, "w") as f:
        if ext == ".json":
            json.dump(result, f, indent=2)
        elif ext in [".md", ".markdown"]:
            f.write(f"# Task Result\n\n")
            f.write(f"**Task:** {result['task'].get('description', 'N/A')}\n\n")
            f.write(f"**Prompt:** {result['prompt']}\n\n")
            f.write(f"---\n\n")
            f.write(result["content"])
        else:
            f.write(result["content"])

def main():
    parser = argparse.ArgumentParser(
        description="Swarm Task Runner - Execute predefined AI tasks",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python task.py --list                           List all tasks
  python task.py research_deep "AI developments"  Run deep research
  python task.py business_planner "SaaS startup"  Generate business plan
  python task.py research_quick "Topic" -o out.md Save to file
        """
    )

    parser.add_argument("task", nargs="?", help="Task name to run")
    parser.add_argument("prompt", nargs="?", help="Task prompt")
    parser.add_argument("--list", "-l", action="store_true", help="List available tasks")
    parser.add_argument("--output", "-o", help="Output file path")
    parser.add_argument("--provider", "-p", default="xai", help="LLM provider")
    parser.add_argument("--verbose", "-v", action="store_true", help="Verbose output")
    parser.add_argument("--artifact-dir", help="Directory for generated artifacts")

    args = parser.parse_args()

    if args.list:
        list_tasks()
        return

    if not args.task:
        parser.print_help()
        print("\nUse --list to see available tasks")
        return

    if not args.prompt:
        print(f"Error: Task '{args.task}' requires a prompt")
        sys.exit(1)

    run_task(args.task, args.prompt, args.output, args.verbose)

if __name__ == "__main__":
    main()
