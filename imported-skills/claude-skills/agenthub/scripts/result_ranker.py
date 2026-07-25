#!/usr/bin/env python3
"""Rank AgentHub agent results by metric or diff quality.

Runs an evaluation command in each agent's worktree, parses a metric,
and produces a ranked table.

Usage:
    python result_ranker.py --session 20260317-143022 \\
        --eval-cmd "pytest bench.py --json" --metric p50_ms --direction lower

    python result_ranker.py --session 20260317-143022 --diff-summary

    python result_ranker.py --demo
"""

import argparse
import json
import os
import re
import subprocess
import sys


def run_git(*args):
    """Run a git command and return stdout."""
    try:
        result = subprocess.run(
            ["git"] + list(args),
            capture_output=True, text=True, check=True
        )
        return result.stdout.strip()
    except subprocess.CalledProcessError as e:
        return ""


def get_session_config(session_id):
    """Load session config."""
    config_path = os.path.join(".agenthub", "sessions", session_id, "config.yaml")
    if not os.path.exists(config_path):
        print(f"Error: Session {session_id} not found", file=sys.stderr)
        sys.exit(1)

    config = {}
    with open(config_path) as f:
        for line in f:
            line = line.strip()
            if ":" in line and not line.startswith("#"):
                key, val = line.split(":", 1)
                val = val.strip().strip('"')
                config[key.strip()] = val
    return config


def get_hub_branches(session_id):
    """Get all hub branches for a session."""
    output = run_git("branch", "--list", f"hub/{session_id}/*",
                     "--format=%(refname:short)")
    if not output:
        return []
    return [b.strip() for b in output.split("\n") if b.strip()]


def get_worktree_path(branch):
    """Get the worktree path for a branch, if it exists."""
    output = run_git("worktree", "list", "--porcelain")
    if not output:
        return None
    current_path = None
    for line in output.split("\n"):
        if line.startswith("worktree "):
            current_path = line[len("worktree "):]
        elif line.startswith("branch ") and current_path:
            ref = line[len("branch "):]
            short = ref.replace("refs/heads/", "")
            if short == branch:
                return current_path
            current_path = None
    return None


def run_eval_in_worktree(worktree_path, eval_cmd):
    """Run evaluation command in a worktree and return stdout."""
    try:
        result = subprocess.run(
            eval_cmd, shell=True, capture_output=True, text=True,
            cwd=worktree_path, timeout=120
        )
        return result.stdout.strip(), result.returncode
    except subprocess.TimeoutExpired:
        return "TIMEOUT", 1
    except Exception as e:
        return str(e), 1


def extract_metric(output, metric_name):
    """Extract a numeric metric from command output.

    Looks for patterns like:
    - metric_name: 42.5
    - metric_name=42.5
    - "metric_name": 42.5
    """
    patterns = [
        rf'{metric_name}\s*[:=]\s*([\d.]+)',
        rf'"{metric_name}"\s*[:=]\s*([\d.]+)',
        rf"'{metric_name}'\s*[:=]\s*([\d.]+)",
    ]
    for pattern in patterns:
        match = re.search(pattern, output, re.IGNORECASE)
        if match:
            try:
                return float(match.group(1))
            except ValueError:
                continue
    return None


def get_diff_stats(branch, base_branch="main"):
    """Get diff statistics for a branch vs base."""
    output = run_git("diff", "--stat", f"{base_branch}...{branch}")
    lines_output = run_git("diff", "--shortstat", f"{base_branch}...{branch}")

    files_changed = 0
    insertions = 0
    deletions = 0

    if lines_output:
        files_match = re.search(r"(\d+) files? changed", lines_output)
        ins_match = re.search(r"(\d+) insertions?", lines_output)
        del_match = re.search(r"(\d+) deletions?", lines_output)
        if files_match:
            files_changed = int(files_match.group(1))
        if ins_match:
            insertions = int(ins_match.group(1))
        if del_match:
            deletions = int(del_match.group(1))

    return {
        "files_changed": files_changed,
        "insertions": insertions,
        "deletions": deletions,
        "net_lines": insertions - deletions,
    }


def rank_by_metric(results, direction="lower"):
    """Sort results by metric value."""
    valid = [r for r in results if r.get("metric_value") is not None]
    invalid = [r for r in results if r.get("metric_value") is None]

    reverse = direction == "higher"
    valid.sort(key=lambda r: r["metric_value"], reverse=reverse)

    for i, r in enumerate(valid):
        r["rank"] = i + 1

    for r in invalid:
        r["rank"] = len(valid) + 1

    return valid + invalid


def run_demo():
    """Show demo ranking output."""
    print("=" * 60)
    print("AgentHub Result Ranker — Demo Mode")
    print("=" * 60)
    print()
    print("Session: 20260317-143022")
    print("Eval: pytest bench.py --json")
    print("Metric: p50_ms (lower is better)")
    print("Baseline: 180ms")
    print()

    header = f"{'RANK':<6} {'AGENT':<10} {'METRIC':<10} {'DELTA':<10} {'FILES':<7} {'SUMMARY'}"
    print(header)
    print("-" * 75)
    print(f"{'1':<6} {'agent-2':<10} {'142ms':<10} {'-38ms':<10} {'2':<7} Replaced O(n²) with hash map lookup")
    print(f"{'2':<6} {'agent-1':<10} {'165ms':<10} {'-15ms':<10} {'3':<7} Added caching layer")
    print(f"{'3':<6} {'agent-3':<10} {'190ms':<10} {'+10ms':<10} {'1':<7} Minor loop optimizations")
    print()
    print("Winner: agent-2 (142ms, -21% from baseline)")
    print()
    print("Next step: Run /hub:merge to merge agent-2's branch")


def main():
    parser = argparse.ArgumentParser(
        description="Rank AgentHub agent results"
    )
    parser.add_argument("--session", type=str,
                        help="Session ID to evaluate")
    parser.add_argument("--eval-cmd", type=str,
                        help="Evaluation command to run in each worktree")
    parser.add_argument("--metric", type=str,
                        help="Metric name to extract from eval output")
    parser.add_argument("--direction", choices=["lower", "higher"],
                        default="lower",
                        help="Whether lower or higher metric is better")
    parser.add_argument("--baseline", type=float,
                        help="Baseline metric value for delta calculation")
    parser.add_argument("--diff-summary", action="store_true",
                        help="Show diff statistics per agent (no eval cmd needed)")
    parser.add_argument("--format", choices=["table", "json"], default="table",
                        help="Output format (default: table)")
    parser.add_argument("--demo", action="store_true",
                        help="Show demo output")
    args = parser.parse_args()

    if args.demo:
        run_demo()
        return

    if not args.session:
        print("Error: --session is required", file=sys.stderr)
        sys.exit(1)

    config = get_session_config(args.session)
    branches = get_hub_branches(args.session)

    if not branches:
        print(f"No branches found for session {args.session}")
        return

    eval_cmd = args.eval_cmd or config.get("eval_cmd")
    metric = args.metric or config.get("metric")
    direction = args.direction or config.get("direction", "lower")
    base_branch = config.get("base_branch", "main")

    results = []
    for branch in branches:
        # Extract agent number
        match = re.match(r"hub/[^/]+/agent-(\d+)/", branch)
        agent_id = f"agent-{match.group(1)}" if match else branch.split("/")[-2]

        result = {
            "agent": agent_id,
            "branch": branch,
            "metric_value": None,
            "metric_raw": None,
            "diff": get_diff_stats(branch, base_branch),
        }

        if eval_cmd and metric:
            worktree = get_worktree_path(branch)
            if worktree:
                output, returncode = run_eval_in_worktree(worktree, eval_cmd)
                result["metric_raw"] = output
                result["eval_returncode"] = returncode
                if returncode == 0:
                    result["metric_value"] = extract_metric(output, metric)

        results.append(result)

    # Rank
    ranked = rank_by_metric(results, direction)

    # Calculate deltas
    baseline = args.baseline
    if baseline is None and ranked and ranked[0].get("metric_value") is not None:
        # Use worst as baseline if not specified
        values = [r["metric_value"] for r in ranked if r["metric_value"] is not None]
        if values:
            baseline = max(values) if direction == "lower" else min(values)

    for r in ranked:
        if r.get("metric_value") is not None and baseline is not None:
            r["delta"] = r["metric_value"] - baseline
        else:
            r["delta"] = None

    if args.format == "json":
        print(json.dumps({"session": args.session, "results": ranked}, indent=2))
        return

    # Table output
    print(f"Session: {args.session}")
    if eval_cmd:
        print(f"Eval: {eval_cmd}")
    if metric:
        dir_str = "lower is better" if direction == "lower" else "higher is better"
        print(f"Metric: {metric} ({dir_str})")
    if baseline:
        print(f"Baseline: {baseline}")
    print()

    if args.diff_summary or not eval_cmd:
        header = f"{'RANK':<6} {'AGENT':<12} {'FILES':<7} {'ADDED':<8} {'REMOVED':<8} {'NET':<6}"
        print(header)
        print("-" * 50)
        for i, r in enumerate(ranked):
            d = r["diff"]
            print(f"{i+1:<6} {r['agent']:<12} {d['files_changed']:<7} "
                  f"+{d['insertions']:<7} -{d['deletions']:<7} {d['net_lines']:<6}")
    else:
        header = f"{'RANK':<6} {'AGENT':<12} {'METRIC':<12} {'DELTA':<10} {'FILES':<7}"
        print(header)
        print("-" * 50)
        for r in ranked:
            mv = str(r["metric_value"]) if r["metric_value"] is not None else "N/A"
            delta = ""
            if r["delta"] is not None:
                sign = "+" if r["delta"] >= 0 else ""
                delta = f"{sign}{r['delta']:.1f}"
            print(f"{r['rank']:<6} {r['agent']:<12} {mv:<12} {delta:<10} {r['diff']['files_changed']:<7}")

    # Winner
    if ranked and ranked[0].get("metric_value") is not None:
        winner = ranked[0]
        print()
        print(f"Winner: {winner['agent']} ({winner['metric_value']})")


if __name__ == "__main__":
    main()
