#!/usr/bin/env python3
"""
Pipeline validation for multi-agent swarms.
Checks agent definitions for schema correctness, dependency cycles,
missing connections, and cost budget violations.

Part of swarm-orchestrator skill by Swarm Labs USA
https://github.com/michaelwinczuk/swarm-orchestrator
"""

import json
import sys
from collections import defaultdict

VALID_ARCHETYPES = {
    "Perceiver", "Classifier", "Analyzer", "Synthesizer",
    "Validator", "Resolver", "Planner", "Executor"
}

REQUIRED_AGENT_FIELDS = {"name", "archetype", "input_schema", "output_schema"}


def load_pipeline(path: str) -> dict:
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def validate_agents(pipeline: dict) -> list[dict]:
    """Validate individual agent definitions."""
    errors = []
    agents = pipeline.get("agents", [])

    if not agents:
        errors.append({"severity": "critical", "agent": "pipeline", "error": "No agents defined"})
        return errors

    names = set()
    for i, agent in enumerate(agents):
        agent_name = agent.get("name", f"agent_{i}")

        # Check required fields
        missing = REQUIRED_AGENT_FIELDS - set(agent.keys())
        if missing:
            errors.append({
                "severity": "critical",
                "agent": agent_name,
                "error": f"Missing required fields: {', '.join(missing)}"
            })

        # Check duplicate names
        if agent_name in names:
            errors.append({
                "severity": "critical",
                "agent": agent_name,
                "error": "Duplicate agent name"
            })
        names.add(agent_name)

        # Check archetype validity
        archetype = agent.get("archetype", "")
        if archetype and archetype not in VALID_ARCHETYPES:
            errors.append({
                "severity": "warning",
                "agent": agent_name,
                "error": f"Unknown archetype '{archetype}'. Valid: {', '.join(sorted(VALID_ARCHETYPES))}"
            })

        # Check deterministic + API consistency
        deterministic = agent.get("deterministic", False)
        api_calls = agent.get("api_calls", 0)
        if deterministic and api_calls > 0:
            errors.append({
                "severity": "critical",
                "agent": agent_name,
                "error": f"Marked deterministic=true but api_calls={api_calls}. Contradictory."
            })

        # Warn on Validator/Gate agents that aren't deterministic
        if archetype == "Validator" and not deterministic:
            errors.append({
                "severity": "warning",
                "agent": agent_name,
                "error": "Validators should be deterministic. Using LLM for validation is expensive and non-reproducible."
            })

    return errors


def validate_connections(pipeline: dict) -> list[dict]:
    """Check that the pipeline forms a valid DAG with no orphans."""
    errors = []
    agents = pipeline.get("agents", [])
    connections = pipeline.get("connections", [])

    agent_names = {a.get("name") for a in agents}

    # Check for agents with no connections
    connected = set()
    for conn in connections:
        src = conn.get("from", "")
        tgt = conn.get("to", "")

        if src != "input" and src not in agent_names:
            errors.append({
                "severity": "critical",
                "agent": src,
                "error": f"Connection references unknown agent '{src}'"
            })

        if tgt != "output" and tgt not in agent_names:
            errors.append({
                "severity": "critical",
                "agent": tgt,
                "error": f"Connection references unknown agent '{tgt}'"
            })

        connected.add(src)
        connected.add(tgt)

    orphans = agent_names - connected
    for orphan in orphans:
        errors.append({
            "severity": "warning",
            "agent": orphan,
            "error": "Agent is not connected to any other agent in the pipeline"
        })

    return errors


def validate_cost_budget(pipeline: dict) -> list[dict]:
    """Check that agent API budgets don't exceed pipeline budget."""
    errors = []
    budget = pipeline.get("pipeline_budget", {})
    max_cost = budget.get("max_cost_per_run", float("inf"))
    max_api = budget.get("max_api_calls", float("inf"))

    total_api = 0
    total_max_cost = 0.0

    for agent in pipeline.get("agents", []):
        agent_name = agent.get("name", "unknown")
        api_calls = agent.get("api_calls", 0)
        agent_cost = agent.get("max_cost", 0.0)

        total_api += api_calls
        total_max_cost += agent_cost

    if total_api > max_api:
        errors.append({
            "severity": "critical",
            "agent": "pipeline",
            "error": f"Total agent API calls ({total_api}) exceeds pipeline budget ({max_api})"
        })

    if total_max_cost > max_cost:
        errors.append({
            "severity": "warning",
            "agent": "pipeline",
            "error": f"Total max agent cost (${total_max_cost:.2f}) exceeds pipeline budget (${max_cost:.2f})"
        })

    # Check deterministic ratio
    agents = pipeline.get("agents", [])
    if agents:
        det_count = sum(1 for a in agents if a.get("deterministic", False))
        det_ratio = det_count / len(agents)
        if det_ratio < 0.5:
            errors.append({
                "severity": "warning",
                "agent": "pipeline",
                "error": f"Only {det_ratio*100:.0f}% of agents are deterministic. Target >= 50% for cost efficiency."
            })

    return errors


def detect_cycles(pipeline: dict) -> list[dict]:
    """Detect circular dependencies in the pipeline."""
    errors = []
    connections = pipeline.get("connections", [])

    # Build adjacency list
    graph = defaultdict(list)
    for conn in connections:
        graph[conn.get("from", "")].append(conn.get("to", ""))

    # DFS cycle detection
    visited = set()
    rec_stack = set()
    cycle_path = []

    def dfs(node: str) -> bool:
        visited.add(node)
        rec_stack.add(node)
        cycle_path.append(node)

        for neighbor in graph.get(node, []):
            if neighbor not in visited:
                if dfs(neighbor):
                    return True
            elif neighbor in rec_stack:
                cycle_start = cycle_path.index(neighbor)
                cycle = cycle_path[cycle_start:] + [neighbor]
                errors.append({
                    "severity": "critical",
                    "agent": "pipeline",
                    "error": f"Circular dependency detected: {' → '.join(cycle)}"
                })
                return True

        cycle_path.pop()
        rec_stack.remove(node)
        return False

    for node in list(graph.keys()):
        if node not in visited:
            dfs(node)

    return errors


def validate_pipeline(path: str) -> dict:
    """Run all validations on a pipeline definition."""
    pipeline = load_pipeline(path)

    all_errors = []
    all_errors.extend(validate_agents(pipeline))
    all_errors.extend(validate_connections(pipeline))
    all_errors.extend(validate_cost_budget(pipeline))
    all_errors.extend(detect_cycles(pipeline))

    critical = [e for e in all_errors if e["severity"] == "critical"]
    warnings = [e for e in all_errors if e["severity"] == "warning"]

    agents = pipeline.get("agents", [])
    det_count = sum(1 for a in agents if a.get("deterministic", False))

    return {
        "valid": len(critical) == 0,
        "critical_errors": len(critical),
        "warnings": len(warnings),
        "errors": all_errors,
        "summary": {
            "agent_count": len(agents),
            "deterministic_count": det_count,
            "api_enabled_count": len(agents) - det_count,
            "total_api_calls": sum(a.get("api_calls", 0) for a in agents),
            "deterministic_ratio": f"{(det_count/len(agents)*100) if agents else 0:.0f}%"
        }
    }


def main():
    if len(sys.argv) < 2:
        print("Usage: python validate_pipeline.py <pipeline.json>")
        print()
        print("Pipeline JSON format:")
        print(json.dumps({
            "name": "my-swarm",
            "mission": "What this swarm does",
            "pipeline_budget": {"max_api_calls": 2, "max_cost_per_run": 0.20},
            "agents": [
                {
                    "name": "AgentName",
                    "archetype": "Perceiver",
                    "deterministic": True,
                    "api_calls": 0,
                    "max_cost": 0,
                    "input_schema": {"field": "type"},
                    "output_schema": {"field": "type"}
                }
            ],
            "connections": [
                {"from": "input", "to": "AgentName"},
                {"from": "AgentName", "to": "output"}
            ]
        }, indent=2))
        sys.exit(1)

    result = validate_pipeline(sys.argv[1])
    print(json.dumps(result, indent=2))

    sys.exit(0 if result["valid"] else 1)


if __name__ == "__main__":
    main()
