#!/usr/bin/env python3
"""
Chalkboard simulation for multi-agent pipelines.
Runs a dry simulation of a pipeline to verify data flow,
estimate costs, and check for schema mismatches.

Part of swarm-orchestrator skill by Swarm Labs USA
https://github.com/michaelwinczuk/swarm-orchestrator
"""

import json
import sys
import time
from typing import Any


def load_pipeline(path: str) -> dict:
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def build_execution_order(pipeline: dict) -> list[str]:
    """Determine agent execution order from connections."""
    connections = pipeline.get("connections", [])
    agents = {a["name"]: a for a in pipeline.get("agents", [])}

    # Build dependency graph
    deps = {name: set() for name in agents}
    for conn in connections:
        src = conn.get("from", "")
        tgt = conn.get("to", "")
        if tgt in deps and src != "input":
            deps[tgt].add(src)

    # Topological sort
    order = []
    resolved = set()

    while len(order) < len(agents):
        progress = False
        for name, dependencies in deps.items():
            if name not in resolved and dependencies.issubset(resolved):
                order.append(name)
                resolved.add(name)
                progress = True

        if not progress:
            remaining = set(agents.keys()) - resolved
            # Fallback: add by position_in_pipeline
            for name in sorted(remaining, key=lambda n: agents[n].get("position_in_pipeline", 99)):
                order.append(name)
                resolved.add(name)
            break

    return order


def simulate_agent(agent: dict, chalkboard: dict) -> dict:
    """Simulate an agent's execution, producing mock output based on its schema."""
    output_schema = agent.get("output_schema", {})
    mock_output = {}

    for field, field_type in output_schema.items():
        if isinstance(field_type, str):
            if "array" in field_type.lower() or "list" in field_type.lower():
                mock_output[field] = ["<simulated_item_1>", "<simulated_item_2>"]
            elif "bool" in field_type.lower():
                mock_output[field] = True
            elif "int" in field_type.lower() or "float" in field_type.lower() or "number" in field_type.lower():
                mock_output[field] = 0.85
            else:
                mock_output[field] = f"<simulated_{field}>"
        else:
            mock_output[field] = f"<simulated_{field}>"

    return mock_output


def check_schema_compatibility(producer: dict, consumer: dict) -> list[str]:
    """Check if producer's output schema has fields that consumer's input expects."""
    producer_output = set(producer.get("output_schema", {}).keys())
    consumer_input = set(consumer.get("input_schema", {}).keys())

    # Check if consumer expects fields from producer
    # This is a heuristic — field names should overlap
    warnings = []
    if not producer_output and not consumer_input:
        return warnings

    common = producer_output & consumer_input
    if not common and producer_output and consumer_input:
        warnings.append(
            f"No matching fields between {producer['name']} output and {consumer['name']} input. "
            f"Producer outputs: {', '.join(producer_output)}. Consumer expects: {', '.join(consumer_input)}."
        )

    return warnings


def simulate_pipeline(path: str) -> dict:
    """Run a full dry simulation of the pipeline."""
    pipeline = load_pipeline(path)
    agents = {a["name"]: a for a in pipeline.get("agents", [])}
    connections = pipeline.get("connections", [])
    execution_order = build_execution_order(pipeline)

    chalkboard = {
        "input": {"data": "<simulated_input>"},
        "metadata": {
            "start_time": time.strftime("%Y-%m-%dT%H:%M:%SZ"),
            "agents_executed": 0,
            "total_cost": 0.0,
            "api_calls": 0,
            "deterministic_solves": 0
        }
    }

    trace = []
    schema_warnings = []

    # Check schema compatibility along connections
    conn_map = {}
    for conn in connections:
        src = conn.get("from", "")
        tgt = conn.get("to", "")
        if src != "input" and tgt != "output" and src in agents and tgt in agents:
            warnings = check_schema_compatibility(agents[src], agents[tgt])
            schema_warnings.extend(warnings)
            conn_map.setdefault(tgt, []).append(src)

    # Simulate execution
    for agent_name in execution_order:
        agent = agents[agent_name]

        step = {
            "agent": agent_name,
            "archetype": agent.get("archetype", "unknown"),
            "deterministic": agent.get("deterministic", False),
            "api_calls": agent.get("api_calls", 0),
            "est_cost": agent.get("max_cost", 0.0),
            "status": "simulated",
            "reads_from": conn_map.get(agent_name, ["input"]),
        }

        # Simulate the agent
        mock_output = simulate_agent(agent, chalkboard)
        chalkboard[agent_name] = mock_output
        step["output_fields"] = list(mock_output.keys())

        # Update metadata
        chalkboard["metadata"]["agents_executed"] += 1
        chalkboard["metadata"]["total_cost"] += agent.get("max_cost", 0.0)
        chalkboard["metadata"]["api_calls"] += agent.get("api_calls", 0)
        if agent.get("deterministic", False):
            chalkboard["metadata"]["deterministic_solves"] += 1

        trace.append(step)

    chalkboard["metadata"]["end_time"] = time.strftime("%Y-%m-%dT%H:%M:%SZ")

    # Summary
    total_agents = len(execution_order)
    det_agents = sum(1 for a in execution_order if agents[a].get("deterministic", False))

    return {
        "simulation": "complete",
        "execution_order": execution_order,
        "trace": trace,
        "schema_warnings": schema_warnings,
        "chalkboard_keys": list(chalkboard.keys()),
        "summary": {
            "agents_executed": total_agents,
            "deterministic_agents": det_agents,
            "api_agents": total_agents - det_agents,
            "deterministic_ratio": f"{(det_agents/total_agents*100) if total_agents else 0:.0f}%",
            "total_api_calls": chalkboard["metadata"]["api_calls"],
            "estimated_max_cost": f"${chalkboard['metadata']['total_cost']:.2f}",
        }
    }


def main():
    if len(sys.argv) < 2:
        print("Usage: python simulate.py <pipeline.json>")
        print("  Runs a dry simulation of the pipeline and reports execution order,")
        print("  schema compatibility, cost estimates, and chalkboard state.")
        sys.exit(1)

    result = simulate_pipeline(sys.argv[1])
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
