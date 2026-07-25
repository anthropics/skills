#!/usr/bin/env python3
"""Initialize an AgentHub collaboration session.

Creates the .agenthub/ directory structure, generates a session ID,
and writes config.yaml and state.json for the session.

Usage:
    python hub_init.py --task "Optimize API response time" --agents 3 \\
        --eval "pytest bench.py --json" --metric p50_ms --direction lower

    python hub_init.py --task "Refactor auth module" --agents 2

    python hub_init.py --demo
"""

import argparse
import json
import os
import sys
from datetime import datetime, timezone


def generate_session_id():
    """Generate a timestamp-based session ID."""
    return datetime.now().strftime("%Y%m%d-%H%M%S")


def create_directory_structure(base_path):
    """Create the .agenthub/ directory tree."""
    dirs = [
        os.path.join(base_path, "sessions"),
        os.path.join(base_path, "board", "dispatch"),
        os.path.join(base_path, "board", "progress"),
        os.path.join(base_path, "board", "results"),
    ]
    for d in dirs:
        os.makedirs(d, exist_ok=True)


def write_gitignore(base_path):
    """Write .agenthub/.gitignore to exclude worktree artifacts."""
    gitignore_path = os.path.join(base_path, ".gitignore")
    if not os.path.exists(gitignore_path):
        with open(gitignore_path, "w") as f:
            f.write("# AgentHub gitignore\n")
            f.write("# Keep board and sessions, ignore worktree artifacts\n")
            f.write("*.tmp\n")
            f.write("*.lock\n")


def write_board_index(base_path):
    """Initialize the board index file."""
    index_path = os.path.join(base_path, "board", "_index.json")
    if not os.path.exists(index_path):
        index = {
            "channels": ["dispatch", "progress", "results"],
            "counters": {"dispatch": 0, "progress": 0, "results": 0},
        }
        with open(index_path, "w") as f:
            json.dump(index, f, indent=2)
            f.write("\n")


def create_session(base_path, session_id, task, agents, eval_cmd, metric,
                   direction, base_branch):
    """Create a new session with config and state files."""
    session_dir = os.path.join(base_path, "sessions", session_id)
    os.makedirs(session_dir, exist_ok=True)

    # Write config.yaml (manual YAML to avoid dependency)
    config_path = os.path.join(session_dir, "config.yaml")
    config_lines = [
        f"session_id: {session_id}",
        f"task: \"{task}\"",
        f"agent_count: {agents}",
        f"base_branch: {base_branch}",
        f"created: {datetime.now(timezone.utc).isoformat()}",
    ]
    if eval_cmd:
        config_lines.append(f"eval_cmd: \"{eval_cmd}\"")
    if metric:
        config_lines.append(f"metric: {metric}")
    if direction:
        config_lines.append(f"direction: {direction}")

    with open(config_path, "w") as f:
        f.write("\n".join(config_lines))
        f.write("\n")

    # Write state.json
    state_path = os.path.join(session_dir, "state.json")
    state = {
        "session_id": session_id,
        "state": "init",
        "created": datetime.now(timezone.utc).isoformat(),
        "updated": datetime.now(timezone.utc).isoformat(),
        "agents": {},
    }
    with open(state_path, "w") as f:
        json.dump(state, f, indent=2)
        f.write("\n")

    return session_dir


def validate_git_repo():
    """Check if current directory is a git repository."""
    if not os.path.isdir(".git"):
        # Check parent dirs
        path = os.path.abspath(".")
        while path != "/":
            if os.path.isdir(os.path.join(path, ".git")):
                return True
            path = os.path.dirname(path)
        return False
    return True


def get_current_branch():
    """Get the current git branch name."""
    head_file = os.path.join(".git", "HEAD")
    if os.path.exists(head_file):
        with open(head_file) as f:
            ref = f.read().strip()
            if ref.startswith("ref: refs/heads/"):
                return ref[len("ref: refs/heads/"):]
    return "main"


def run_demo():
    """Show a demo of what hub_init creates."""
    print("=" * 60)
    print("AgentHub Init — Demo Mode")
    print("=" * 60)
    print()
    print("Session ID: 20260317-143022")
    print("Task: Optimize API response time below 100ms")
    print("Agents: 3")
    print("Eval: pytest bench.py --json")
    print("Metric: p50_ms (lower is better)")
    print("Base branch: dev")
    print()
    print("Directory structure created:")
    print("  .agenthub/")
    print("  ├── .gitignore")
    print("  ├── sessions/")
    print("  │   └── 20260317-143022/")
    print("  │       ├── config.yaml")
    print("  │       └── state.json")
    print("  └── board/")
    print("      ├── _index.json")
    print("      ├── dispatch/")
    print("      ├── progress/")
    print("      └── results/")
    print()
    print("config.yaml:")
    print('  session_id: 20260317-143022')
    print('  task: "Optimize API response time below 100ms"')
    print("  agent_count: 3")
    print("  base_branch: dev")
    print('  eval_cmd: "pytest bench.py --json"')
    print("  metric: p50_ms")
    print("  direction: lower")
    print()
    print("state.json:")
    print('  { "state": "init", "agents": {} }')
    print()
    print("Next step: Run /hub:spawn to launch agents")


def main():
    parser = argparse.ArgumentParser(
        description="Initialize an AgentHub collaboration session"
    )
    parser.add_argument("--task", type=str, help="Task description for agents")
    parser.add_argument("--agents", type=int, default=3,
                        help="Number of parallel agents (default: 3)")
    parser.add_argument("--eval", type=str, dest="eval_cmd",
                        help="Evaluation command to run in each worktree")
    parser.add_argument("--metric", type=str,
                        help="Metric name to extract from eval output")
    parser.add_argument("--direction", choices=["lower", "higher"],
                        help="Whether lower or higher metric is better")
    parser.add_argument("--base-branch", type=str,
                        help="Base branch (default: current branch)")
    parser.add_argument("--format", choices=["text", "json"], default="text",
                        help="Output format (default: text)")
    parser.add_argument("--demo", action="store_true",
                        help="Show demo output without creating files")
    args = parser.parse_args()

    if args.demo:
        run_demo()
        return

    if not args.task:
        print("Error: --task is required", file=sys.stderr)
        print("Usage: hub_init.py --task 'description' [--agents N] "
              "[--eval 'cmd'] [--metric name] [--direction lower|higher]",
              file=sys.stderr)
        sys.exit(1)

    if not validate_git_repo():
        print("Error: Not a git repository. AgentHub requires git.",
              file=sys.stderr)
        sys.exit(1)

    base_branch = args.base_branch or get_current_branch()
    base_path = ".agenthub"
    session_id = generate_session_id()

    # Create structure
    create_directory_structure(base_path)
    write_gitignore(base_path)
    write_board_index(base_path)

    # Create session
    session_dir = create_session(
        base_path, session_id, args.task, args.agents,
        args.eval_cmd, args.metric, args.direction, base_branch
    )

    if args.format == "json":
        output = {
            "session_id": session_id,
            "session_dir": session_dir,
            "task": args.task,
            "agent_count": args.agents,
            "eval_cmd": args.eval_cmd,
            "metric": args.metric,
            "direction": args.direction,
            "base_branch": base_branch,
            "state": "init",
        }
        print(json.dumps(output, indent=2))
    else:
        print(f"AgentHub session initialized")
        print(f"  Session ID: {session_id}")
        print(f"  Task: {args.task}")
        print(f"  Agents: {args.agents}")
        if args.eval_cmd:
            print(f"  Eval: {args.eval_cmd}")
        if args.metric:
            direction_str = "lower is better" if args.direction == "lower" else "higher is better"
            print(f"  Metric: {args.metric} ({direction_str})")
        print(f"  Base branch: {base_branch}")
        print(f"  State: init")
        print()
        print(f"Next step: Run /hub:spawn to launch {args.agents} agents")


if __name__ == "__main__":
    main()
