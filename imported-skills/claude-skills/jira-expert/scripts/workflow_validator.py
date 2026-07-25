#!/usr/bin/env python3
"""
Workflow Validator

Validates Jira workflow definitions (JSON input) for anti-patterns and common
issues. Checks for dead-end states, orphan states, missing transitions, circular
paths, and produces a health score with severity-rated findings.

Usage:
    python workflow_validator.py workflow.json
    python workflow_validator.py workflow.json --format json
"""

import argparse
import json
import sys
from typing import Any, Dict, List, Optional, Set, Tuple


# ---------------------------------------------------------------------------
# Validation Configuration
# ---------------------------------------------------------------------------

MAX_RECOMMENDED_STATES = 10
REQUIRED_TERMINAL_STATES = {"done", "closed", "resolved", "completed"}

SEVERITY_WEIGHTS = {
    "error": 20,
    "warning": 10,
    "info": 3,
}


# ---------------------------------------------------------------------------
# Validation Rules
# ---------------------------------------------------------------------------

def check_state_count(states: List[str]) -> List[Dict[str, str]]:
    """Check if the workflow has too many states."""
    findings = []
    count = len(states)

    if count > MAX_RECOMMENDED_STATES:
        findings.append({
            "rule": "state_count",
            "severity": "warning",
            "message": f"Workflow has {count} states (recommended max: {MAX_RECOMMENDED_STATES}). "
                       f"Complex workflows slow teams down and increase error rates.",
        })
    elif count < 2:
        findings.append({
            "rule": "state_count",
            "severity": "error",
            "message": f"Workflow has only {count} state(s). A minimum of 2 states is required.",
        })

    if count > 15:
        findings[-1]["severity"] = "error"

    return findings


def check_dead_end_states(
    states: List[str],
    transitions: List[Dict[str, str]],
    terminal_states: Set[str],
) -> List[Dict[str, str]]:
    """Find states with no outgoing transitions that are not terminal."""
    findings = []
    outgoing = set()
    for t in transitions:
        outgoing.add(t.get("from", "").lower())

    for state in states:
        state_lower = state.lower()
        if state_lower not in outgoing and state_lower not in terminal_states:
            findings.append({
                "rule": "dead_end_state",
                "severity": "error",
                "message": f"State '{state}' has no outgoing transitions and is not a terminal state. "
                           f"Issues will get stuck here.",
            })

    return findings


def check_orphan_states(
    states: List[str],
    transitions: List[Dict[str, str]],
    initial_state: Optional[str],
) -> List[Dict[str, str]]:
    """Find states with no incoming transitions (except the initial state)."""
    findings = []
    incoming = set()
    for t in transitions:
        incoming.add(t.get("to", "").lower())

    initial_lower = (initial_state or "").lower()

    for state in states:
        state_lower = state.lower()
        if state_lower not in incoming and state_lower != initial_lower:
            findings.append({
                "rule": "orphan_state",
                "severity": "warning",
                "message": f"State '{state}' has no incoming transitions and is not the initial state. "
                           f"This state may be unreachable.",
            })

    return findings


def check_missing_terminal_state(states: List[str]) -> List[Dict[str, str]]:
    """Check that at least one terminal/done state exists."""
    findings = []
    states_lower = {s.lower() for s in states}

    has_terminal = bool(states_lower & REQUIRED_TERMINAL_STATES)
    if not has_terminal:
        findings.append({
            "rule": "missing_terminal_state",
            "severity": "error",
            "message": f"No terminal state found. Expected one of: {', '.join(sorted(REQUIRED_TERMINAL_STATES))}. "
                       f"Issues cannot be marked as complete.",
        })

    return findings


def check_duplicate_transition_names(
    transitions: List[Dict[str, str]],
) -> List[Dict[str, str]]:
    """Check for duplicate transition names from the same state."""
    findings = []
    seen = {}

    for t in transitions:
        name = t.get("name", "").lower()
        from_state = t.get("from", "").lower()
        key = (from_state, name)

        if key in seen:
            findings.append({
                "rule": "duplicate_transition",
                "severity": "warning",
                "message": f"Duplicate transition name '{t.get('name', '')}' from state '{t.get('from', '')}'. "
                           f"This can confuse users selecting transitions.",
            })
        else:
            seen[key] = True

    return findings


def check_missing_transitions(
    states: List[str],
    transitions: List[Dict[str, str]],
) -> List[Dict[str, str]]:
    """Check for states referenced in transitions but not defined."""
    findings = []
    defined_states = {s.lower() for s in states}

    for t in transitions:
        from_state = t.get("from", "").lower()
        to_state = t.get("to", "").lower()

        if from_state and from_state not in defined_states:
            findings.append({
                "rule": "undefined_state_reference",
                "severity": "error",
                "message": f"Transition references undefined source state '{t.get('from', '')}'.",
            })

        if to_state and to_state not in defined_states:
            findings.append({
                "rule": "undefined_state_reference",
                "severity": "error",
                "message": f"Transition references undefined target state '{t.get('to', '')}'.",
            })

    return findings


def check_circular_paths(
    states: List[str],
    transitions: List[Dict[str, str]],
    terminal_states: Set[str],
) -> List[Dict[str, str]]:
    """Detect circular paths that have no exit to a terminal state."""
    findings = []

    # Build adjacency list
    adjacency = {}
    for state in states:
        adjacency[state.lower()] = set()
    for t in transitions:
        from_state = t.get("from", "").lower()
        to_state = t.get("to", "").lower()
        if from_state in adjacency:
            adjacency[from_state].add(to_state)

    # Find strongly connected components using iterative DFS
    def can_reach_terminal(start: str) -> bool:
        visited = set()
        stack = [start]
        while stack:
            node = stack.pop()
            if node in terminal_states:
                return True
            if node in visited:
                continue
            visited.add(node)
            for neighbor in adjacency.get(node, set()):
                stack.append(neighbor)
        return False

    # Check each non-terminal state
    for state in states:
        state_lower = state.lower()
        if state_lower not in terminal_states:
            if not can_reach_terminal(state_lower):
                findings.append({
                    "rule": "circular_no_exit",
                    "severity": "error",
                    "message": f"State '{state}' cannot reach any terminal state. "
                               f"Issues entering this state will never be resolved.",
                })

    return findings


def check_self_transitions(transitions: List[Dict[str, str]]) -> List[Dict[str, str]]:
    """Check for transitions that go from a state to itself."""
    findings = []
    for t in transitions:
        if t.get("from", "").lower() == t.get("to", "").lower():
            findings.append({
                "rule": "self_transition",
                "severity": "info",
                "message": f"State '{t.get('from', '')}' has a self-transition '{t.get('name', '')}'. "
                           f"Ensure this is intentional (e.g., for triggering automation).",
            })
    return findings


# ---------------------------------------------------------------------------
# Main Validation
# ---------------------------------------------------------------------------

def validate_workflow(data: Dict[str, Any]) -> Dict[str, Any]:
    """Run all validations on a workflow definition."""
    states = data.get("states", [])
    transitions = data.get("transitions", [])
    initial_state = data.get("initial_state", states[0] if states else None)

    if not states:
        return {
            "health_score": 0,
            "grade": "invalid",
            "findings": [{"rule": "no_states", "severity": "error", "message": "No states defined in workflow"}],
            "summary": {"errors": 1, "warnings": 0, "info": 0},
        }

    # Determine terminal states
    states_lower = {s.lower() for s in states}
    terminal_states = states_lower & REQUIRED_TERMINAL_STATES

    # Custom terminal states from input
    custom_terminals = data.get("terminal_states", [])
    for ct in custom_terminals:
        terminal_states.add(ct.lower())

    # Run all checks
    all_findings = []
    all_findings.extend(check_state_count(states))
    all_findings.extend(check_dead_end_states(states, transitions, terminal_states))
    all_findings.extend(check_orphan_states(states, transitions, initial_state))
    all_findings.extend(check_missing_terminal_state(states))
    all_findings.extend(check_duplicate_transition_names(transitions))
    all_findings.extend(check_missing_transitions(states, transitions))
    all_findings.extend(check_circular_paths(states, transitions, terminal_states))
    all_findings.extend(check_self_transitions(transitions))

    # Calculate health score
    summary = {"errors": 0, "warnings": 0, "info": 0}
    penalty = 0
    for finding in all_findings:
        severity = finding["severity"]
        summary[severity] = summary.get(severity, 0) + 1
        penalty += SEVERITY_WEIGHTS.get(severity, 0)

    health_score = max(0, 100 - penalty)

    if health_score >= 90:
        grade = "excellent"
    elif health_score >= 75:
        grade = "good"
    elif health_score >= 55:
        grade = "fair"
    else:
        grade = "poor"

    return {
        "health_score": health_score,
        "grade": grade,
        "findings": all_findings,
        "summary": summary,
        "workflow_info": {
            "state_count": len(states),
            "transition_count": len(transitions),
            "initial_state": initial_state,
            "terminal_states": sorted(terminal_states),
        },
    }


# ---------------------------------------------------------------------------
# Output Formatting
# ---------------------------------------------------------------------------

def format_text_output(result: Dict[str, Any]) -> str:
    """Format results as readable text report."""
    lines = []
    lines.append("=" * 60)
    lines.append("WORKFLOW VALIDATION REPORT")
    lines.append("=" * 60)
    lines.append("")

    # Health summary
    lines.append("HEALTH SUMMARY")
    lines.append("-" * 30)
    lines.append(f"Health Score: {result['health_score']}/100")
    lines.append(f"Grade: {result['grade'].title()}")
    lines.append("")

    # Workflow info
    info = result.get("workflow_info", {})
    if info:
        lines.append("WORKFLOW INFO")
        lines.append("-" * 30)
        lines.append(f"States: {info.get('state_count', 0)}")
        lines.append(f"Transitions: {info.get('transition_count', 0)}")
        lines.append(f"Initial State: {info.get('initial_state', 'N/A')}")
        lines.append(f"Terminal States: {', '.join(info.get('terminal_states', []))}")
        lines.append("")

    # Summary
    summary = result.get("summary", {})
    lines.append("FINDINGS SUMMARY")
    lines.append("-" * 30)
    lines.append(f"Errors: {summary.get('errors', 0)}")
    lines.append(f"Warnings: {summary.get('warnings', 0)}")
    lines.append(f"Info: {summary.get('info', 0)}")
    lines.append("")

    # Detailed findings
    findings = result.get("findings", [])
    if findings:
        lines.append("DETAILED FINDINGS")
        lines.append("-" * 30)
        for i, finding in enumerate(findings, 1):
            severity = finding["severity"].upper()
            lines.append(f"{i}. [{severity}] {finding['message']}")
            lines.append(f"   Rule: {finding['rule']}")
            lines.append("")
    else:
        lines.append("No issues found. Workflow looks healthy!")

    return "\n".join(lines)


def format_json_output(result: Dict[str, Any]) -> Dict[str, Any]:
    """Format results as JSON."""
    return result


# ---------------------------------------------------------------------------
# CLI Interface
# ---------------------------------------------------------------------------

def main() -> int:
    """Main CLI entry point."""
    parser = argparse.ArgumentParser(
        description="Validate Jira workflow definitions for anti-patterns"
    )
    parser.add_argument(
        "workflow_file",
        help="JSON file containing workflow definition (states, transitions)",
    )
    parser.add_argument(
        "--format",
        choices=["text", "json"],
        default="text",
        help="Output format (default: text)",
    )

    args = parser.parse_args()

    try:
        with open(args.workflow_file, "r") as f:
            data = json.load(f)

        result = validate_workflow(data)

        if args.format == "json":
            print(json.dumps(format_json_output(result), indent=2))
        else:
            print(format_text_output(result))

        return 0

    except FileNotFoundError:
        print(f"Error: File '{args.workflow_file}' not found", file=sys.stderr)
        return 1
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON in '{args.workflow_file}': {e}", file=sys.stderr)
        return 1
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
