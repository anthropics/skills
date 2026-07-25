#!/usr/bin/env python3
"""AgentHub session state machine and lifecycle manager.

Manages session states (init → running → evaluating → merged/archived),
lists sessions, and handles cleanup of worktrees and branches.

Usage:
    python session_manager.py --list
    python session_manager.py --status 20260317-143022
    python session_manager.py --update 20260317-143022 --state running
    python session_manager.py --cleanup 20260317-143022
    python session_manager.py --demo
"""

import argparse
import json
import os
import subprocess
import sys
from datetime import datetime, timezone


SESSIONS_PATH = ".agenthub/sessions"

VALID_STATES = ["init", "running", "evaluating", "merged", "archived"]

VALID_TRANSITIONS = {
    "init": ["running"],
    "running": ["evaluating"],
    "evaluating": ["merged", "archived"],
    "merged": [],
    "archived": [],
}


def load_state(session_id):
    """Load session state.json."""
    state_path = os.path.join(SESSIONS_PATH, session_id, "state.json")
    if not os.path.exists(state_path):
        return None
    with open(state_path) as f:
        return json.load(f)


def save_state(session_id, state):
    """Save session state.json."""
    state_path = os.path.join(SESSIONS_PATH, session_id, "state.json")
    state["updated"] = datetime.now(timezone.utc).isoformat()
    with open(state_path, "w") as f:
        json.dump(state, f, indent=2)
        f.write("\n")


def load_config(session_id):
    """Load session config.yaml (simple key: value parsing)."""
    config_path = os.path.join(SESSIONS_PATH, session_id, "config.yaml")
    if not os.path.exists(config_path):
        return None
    config = {}
    with open(config_path) as f:
        for line in f:
            line = line.strip()
            if ":" in line and not line.startswith("#"):
                key, val = line.split(":", 1)
                config[key.strip()] = val.strip().strip('"')
    return config


def run_git(*args):
    """Run a git command and return stdout."""
    try:
        result = subprocess.run(
            ["git"] + list(args),
            capture_output=True, text=True, check=True
        )
        return result.stdout.strip()
    except subprocess.CalledProcessError:
        return ""


def list_sessions(output_format="text"):
    """List all sessions with their states."""
    if not os.path.isdir(SESSIONS_PATH):
        print("No sessions found. Run hub_init.py first.")
        return

    sessions = []
    for sid in sorted(os.listdir(SESSIONS_PATH)):
        session_dir = os.path.join(SESSIONS_PATH, sid)
        if not os.path.isdir(session_dir):
            continue
        state = load_state(sid)
        config = load_config(sid)
        if state and config:
            sessions.append({
                "session_id": sid,
                "state": state.get("state", "unknown"),
                "task": config.get("task", ""),
                "agents": config.get("agent_count", "?"),
                "created": state.get("created", ""),
            })

    if output_format == "json":
        print(json.dumps({"sessions": sessions}, indent=2))
        return

    if not sessions:
        print("No sessions found.")
        return

    print("AgentHub Sessions")
    print()
    header = f"{'SESSION ID':<20} {'STATE':<12} {'AGENTS':<8} {'TASK'}"
    print(header)
    print("-" * 70)
    for s in sessions:
        task = s["task"][:40] + "..." if len(s["task"]) > 40 else s["task"]
        print(f"{s['session_id']:<20} {s['state']:<12} {s['agents']:<8} {task}")


def show_status(session_id, output_format="text"):
    """Show detailed status for a session."""
    state = load_state(session_id)
    config = load_config(session_id)

    if not state or not config:
        print(f"Error: Session {session_id} not found", file=sys.stderr)
        sys.exit(1)

    if output_format == "json":
        print(json.dumps({"config": config, "state": state}, indent=2))
        return

    print(f"Session: {session_id}")
    print(f"  State: {state.get('state', 'unknown')}")
    print(f"  Task: {config.get('task', '')}")
    print(f"  Agents: {config.get('agent_count', '?')}")
    print(f"  Base branch: {config.get('base_branch', '?')}")
    if config.get("eval_cmd"):
        print(f"  Eval: {config['eval_cmd']}")
    if config.get("metric"):
        print(f"  Metric: {config['metric']} ({config.get('direction', '?')})")
    print(f"  Created: {state.get('created', '?')}")
    print(f"  Updated: {state.get('updated', '?')}")

    # Show agent branches
    branches = run_git("branch", "--list", f"hub/{session_id}/*",
                       "--format=%(refname:short)")
    if branches:
        print()
        print("  Branches:")
        for b in branches.split("\n"):
            if b.strip():
                print(f"    {b.strip()}")


def update_state(session_id, new_state):
    """Transition session to a new state."""
    state = load_state(session_id)
    if not state:
        print(f"Error: Session {session_id} not found", file=sys.stderr)
        sys.exit(1)

    current = state.get("state", "unknown")

    if new_state not in VALID_STATES:
        print(f"Error: Invalid state '{new_state}'. "
              f"Valid: {', '.join(VALID_STATES)}", file=sys.stderr)
        sys.exit(1)

    valid_next = VALID_TRANSITIONS.get(current, [])
    if new_state not in valid_next:
        print(f"Error: Cannot transition from '{current}' to '{new_state}'. "
              f"Valid transitions: {', '.join(valid_next) or 'none (terminal)'}",
              file=sys.stderr)
        sys.exit(1)

    state["state"] = new_state
    save_state(session_id, state)
    print(f"Session {session_id}: {current} → {new_state}")


def cleanup_session(session_id):
    """Clean up worktrees and optionally archive branches."""
    config = load_config(session_id)
    if not config:
        print(f"Error: Session {session_id} not found", file=sys.stderr)
        sys.exit(1)

    # Find and remove worktrees for this session
    worktree_output = run_git("worktree", "list", "--porcelain")
    removed = 0
    if worktree_output:
        current_path = None
        for line in worktree_output.split("\n"):
            if line.startswith("worktree "):
                current_path = line[len("worktree "):]
            elif line.startswith("branch ") and current_path:
                ref = line[len("branch "):]
                if f"hub/{session_id}/" in ref:
                    result = subprocess.run(
                        ["git", "worktree", "remove", "--force", current_path],
                        capture_output=True, text=True
                    )
                    if result.returncode == 0:
                        removed += 1
                        print(f"  Removed worktree: {current_path}")
                current_path = None

    print(f"Cleaned up {removed} worktrees for session {session_id}")


def run_demo():
    """Show demo output."""
    print("=" * 60)
    print("AgentHub Session Manager — Demo Mode")
    print("=" * 60)
    print()

    print("--- Session List ---")
    print("AgentHub Sessions")
    print()
    header = f"{'SESSION ID':<20} {'STATE':<12} {'AGENTS':<8} {'TASK'}"
    print(header)
    print("-" * 70)
    print(f"{'20260317-143022':<20} {'merged':<12} {'3':<8} Optimize API response time below 100ms")
    print(f"{'20260317-151500':<20} {'running':<12} {'2':<8} Refactor auth module for JWT support")
    print(f"{'20260317-160000':<20} {'init':<12} {'4':<8} Implement caching strategy")
    print()

    print("--- Session Detail ---")
    print("Session: 20260317-143022")
    print("  State: merged")
    print("  Task: Optimize API response time below 100ms")
    print("  Agents: 3")
    print("  Base branch: dev")
    print("  Eval: pytest bench.py --json")
    print("  Metric: p50_ms (lower)")
    print("  Created: 2026-03-17T14:30:22Z")
    print("  Updated: 2026-03-17T14:45:00Z")
    print()
    print("  Branches:")
    print("    hub/20260317-143022/agent-1/attempt-1  (archived)")
    print("    hub/20260317-143022/agent-2/attempt-1  (merged)")
    print("    hub/20260317-143022/agent-3/attempt-1  (archived)")
    print()

    print("--- State Transitions ---")
    print("Valid transitions:")
    for state, transitions in VALID_TRANSITIONS.items():
        arrow = " → ".join(transitions) if transitions else "(terminal)"
        print(f"  {state}: {arrow}")


def main():
    parser = argparse.ArgumentParser(
        description="AgentHub session state machine and lifecycle manager"
    )
    parser.add_argument("--list", action="store_true",
                        help="List all sessions with state")
    parser.add_argument("--status", type=str, metavar="SESSION_ID",
                        help="Show detailed session status")
    parser.add_argument("--update", type=str, metavar="SESSION_ID",
                        help="Update session state")
    parser.add_argument("--state", type=str,
                        help="New state for --update")
    parser.add_argument("--cleanup", type=str, metavar="SESSION_ID",
                        help="Remove worktrees and clean up session")
    parser.add_argument("--format", choices=["text", "json"], default="text",
                        help="Output format (default: text)")
    parser.add_argument("--demo", action="store_true",
                        help="Show demo output")
    args = parser.parse_args()

    if args.demo:
        run_demo()
        return

    if args.list:
        list_sessions(args.format)
        return

    if args.status:
        show_status(args.status, args.format)
        return

    if args.update:
        if not args.state:
            print("Error: --update requires --state", file=sys.stderr)
            sys.exit(1)
        update_state(args.update, args.state)
        return

    if args.cleanup:
        cleanup_session(args.cleanup)
        return

    parser.print_help()


if __name__ == "__main__":
    main()
