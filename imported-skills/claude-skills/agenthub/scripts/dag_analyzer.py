#!/usr/bin/env python3
"""Analyze the AgentHub git DAG.

Detects frontier branches (leaves with no children), displays DAG graphs,
and shows per-agent branch status for a session.

Usage:
    python dag_analyzer.py --frontier --session 20260317-143022
    python dag_analyzer.py --graph
    python dag_analyzer.py --status --session 20260317-143022
    python dag_analyzer.py --demo
"""

import argparse
import json
import os
import re
import subprocess
import sys
from datetime import datetime


def run_git(*args):
    """Run a git command and return stdout."""
    try:
        result = subprocess.run(
            ["git"] + list(args),
            capture_output=True, text=True, check=True
        )
        return result.stdout.strip()
    except subprocess.CalledProcessError as e:
        print(f"Git error: {e.stderr.strip()}", file=sys.stderr)
        return ""


def get_hub_branches(session_id=None):
    """Get all hub/* branches, optionally filtered by session."""
    output = run_git("branch", "--list", "hub/*", "--format=%(refname:short)")
    if not output:
        return []
    branches = output.strip().split("\n")
    if session_id:
        prefix = f"hub/{session_id}/"
        branches = [b for b in branches if b.startswith(prefix)]
    return branches


def get_branch_commit(branch):
    """Get the commit hash for a branch."""
    return run_git("rev-parse", "--short", branch)


def get_branch_commit_count(branch, base_branch="main"):
    """Count commits ahead of base branch."""
    output = run_git("rev-list", "--count", f"{base_branch}..{branch}")
    try:
        return int(output)
    except ValueError:
        return 0


def get_branch_last_commit_date(branch):
    """Get the last commit date for a branch."""
    output = run_git("log", "-1", "--format=%ci", branch)
    if output:
        return output[:19]
    return "unknown"


def get_branch_last_commit_msg(branch):
    """Get the last commit message for a branch."""
    return run_git("log", "-1", "--format=%s", branch)


def detect_frontier(session_id=None):
    """Find frontier branches (tips with no child branches).

    A branch is on the frontier if no other hub branch contains its tip commit
    as an ancestor (i.e., it has no children in the DAG).
    """
    branches = get_hub_branches(session_id)
    if not branches:
        return []

    # Get commit hashes for all branches
    branch_commits = {}
    for b in branches:
        commit = run_git("rev-parse", b)
        if commit:
            branch_commits[b] = commit

    # A branch is frontier if its commit is not an ancestor of any other branch
    frontier = []
    for branch, commit in branch_commits.items():
        is_ancestor = False
        for other_branch, other_commit in branch_commits.items():
            if other_branch == branch:
                continue
            # Check if commit is ancestor of other_commit
            result = subprocess.run(
                ["git", "merge-base", "--is-ancestor", commit, other_commit],
                capture_output=True
            )
            if result.returncode == 0:
                is_ancestor = True
                break
        if not is_ancestor:
            frontier.append(branch)

    return frontier


def show_graph():
    """Display the git DAG graph for hub branches."""
    branches = get_hub_branches()
    if not branches:
        print("No hub/* branches found.")
        return

    # Use git log with graph for hub branches
    branch_args = [b for b in branches]
    output = run_git(
        "log", "--all", "--oneline", "--graph", "--decorate",
        "--simplify-by-decoration",
        *[f"--branches=hub/*"]
    )
    if output:
        print(output)
    else:
        print("No hub commits found.")


def show_status(session_id, output_format="table"):
    """Show per-agent branch status for a session."""
    branches = get_hub_branches(session_id)
    if not branches:
        print(f"No branches found for session {session_id}")
        return

    frontier = detect_frontier(session_id)

    # Parse agent info from branch names
    agents = []
    for branch in sorted(branches):
        # Pattern: hub/{session}/agent-{N}/attempt-{M}
        match = re.match(r"hub/[^/]+/agent-(\d+)/attempt-(\d+)", branch)
        if match:
            agent_num = int(match.group(1))
            attempt = int(match.group(2))
        else:
            agent_num = 0
            attempt = 1

        commit = get_branch_commit(branch)
        commits = get_branch_commit_count(branch)
        last_date = get_branch_last_commit_date(branch)
        last_msg = get_branch_last_commit_msg(branch)
        is_frontier = branch in frontier

        agents.append({
            "agent": agent_num,
            "attempt": attempt,
            "branch": branch,
            "commit": commit,
            "commits_ahead": commits,
            "last_update": last_date,
            "last_message": last_msg,
            "frontier": is_frontier,
        })

    if output_format == "json":
        print(json.dumps({"session": session_id, "agents": agents}, indent=2))
        return

    # Table output
    print(f"Session: {session_id}")
    print(f"Branches: {len(branches)} | Frontier: {len(frontier)}")
    print()
    header = f"{'AGENT':<8} {'BRANCH':<45} {'COMMITS':<8} {'STATUS':<10} {'LAST UPDATE':<20}"
    print(header)
    print("-" * len(header))
    for a in agents:
        status = "frontier" if a["frontier"] else "merged"
        print(f"agent-{a['agent']:<4} {a['branch']:<45} {a['commits_ahead']:<8} {status:<10} {a['last_update']:<20}")


def run_demo():
    """Show demo output."""
    print("=" * 60)
    print("AgentHub DAG Analyzer — Demo Mode")
    print("=" * 60)
    print()

    print("--- Frontier Detection ---")
    print("Frontier branches (leaves with no children):")
    print("  hub/20260317-143022/agent-1/attempt-1  (3 commits ahead)")
    print("  hub/20260317-143022/agent-2/attempt-1  (5 commits ahead)")
    print("  hub/20260317-143022/agent-3/attempt-1  (2 commits ahead)")
    print()

    print("--- Session Status ---")
    print("Session: 20260317-143022")
    print("Branches: 3 | Frontier: 3")
    print()
    header = f"{'AGENT':<8} {'BRANCH':<45} {'COMMITS':<8} {'STATUS':<10} {'LAST UPDATE':<20}"
    print(header)
    print("-" * len(header))
    print(f"{'agent-1':<8} {'hub/20260317-143022/agent-1/attempt-1':<45} {'3':<8} {'frontier':<10} {'2026-03-17 14:35:10':<20}")
    print(f"{'agent-2':<8} {'hub/20260317-143022/agent-2/attempt-1':<45} {'5':<8} {'frontier':<10} {'2026-03-17 14:36:45':<20}")
    print(f"{'agent-3':<8} {'hub/20260317-143022/agent-3/attempt-1':<45} {'2':<8} {'frontier':<10} {'2026-03-17 14:34:22':<20}")
    print()

    print("--- DAG Graph ---")
    print("* abc1234 (hub/20260317-143022/agent-2/attempt-1) Replaced O(n²) with hash map")
    print("* def5678 Added benchmark tests")
    print("| * ghi9012 (hub/20260317-143022/agent-1/attempt-1) Added caching layer")
    print("| * jkl3456 Refactored data access")
    print("|/")
    print("| * mno7890 (hub/20260317-143022/agent-3/attempt-1) Minor optimizations")
    print("|/")
    print("* pqr1234 (dev) Base commit")


def main():
    parser = argparse.ArgumentParser(
        description="Analyze the AgentHub git DAG"
    )
    parser.add_argument("--frontier", action="store_true",
                        help="List frontier branches (leaves with no children)")
    parser.add_argument("--graph", action="store_true",
                        help="Show ASCII DAG graph for hub branches")
    parser.add_argument("--status", action="store_true",
                        help="Show per-agent branch status")
    parser.add_argument("--session", type=str,
                        help="Filter by session ID")
    parser.add_argument("--format", choices=["table", "json"], default="table",
                        help="Output format (default: table)")
    parser.add_argument("--demo", action="store_true",
                        help="Show demo output")
    args = parser.parse_args()

    if args.demo:
        run_demo()
        return

    if not any([args.frontier, args.graph, args.status]):
        parser.print_help()
        return

    if args.frontier:
        frontier = detect_frontier(args.session)
        if args.format == "json":
            print(json.dumps({"frontier": frontier}, indent=2))
        else:
            if frontier:
                print("Frontier branches:")
                for b in frontier:
                    print(f"  {b}")
            else:
                print("No frontier branches found.")
        print()

    if args.graph:
        show_graph()
        print()

    if args.status:
        if not args.session:
            print("Error: --session required with --status", file=sys.stderr)
            sys.exit(1)
        show_status(args.session, args.format)


if __name__ == "__main__":
    main()
