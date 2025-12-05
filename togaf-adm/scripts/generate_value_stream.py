#!/usr/bin/env python3
"""
Generate Value Stream Mermaid Diagram

This script generates a Mermaid diagram representing a Value Stream
with stages, activities, stakeholders, and systems.

Usage:
    python generate_value_stream.py <input_json>

Input JSON structure:
{
    "name": "Value Stream Name",
    "trigger": "Event that starts the value stream",
    "value_delivered": "Final value delivered",
    "stages": [
        {
            "name": "Stage 1",
            "activities": ["Activity 1", "Activity 2"],
            "stakeholders": ["Stakeholder 1"],
            "systems": ["System 1", "System 2"],
            "metrics": {
                "time": "5 min",
                "automation": "90%"
            }
        }
    ],
    "overall_metrics": {
        "lead_time": "15 min",
        "cycle_time": "10 min",
        "automation_rate": "92%"
    }
}
"""

import json
import sys


def sanitize_id(text):
    """Sanitize text for use as Mermaid node ID"""
    return text.replace(" ", "_").replace("-", "_").replace("&", "and")[:20]


def generate_value_stream_mermaid(data):
    """Generate Mermaid diagram for Value Stream"""

    name = data.get("name", "Value Stream")
    trigger = data.get("trigger", "Trigger Event")
    value_delivered = data.get("value_delivered", "Value Delivered")
    stages = data.get("stages", [])
    overall_metrics = data.get("overall_metrics", {})

    # Build Mermaid diagram
    mermaid = []
    mermaid.append("```mermaid")
    mermaid.append("graph LR")
    mermaid.append("")
    mermaid.append(f"    %% Value Stream: {name}")
    mermaid.append("")

    # Trigger node
    mermaid.append("    %% Trigger")
    mermaid.append(f"    TRIGGER([\"⚡ {trigger}\"])")
    mermaid.append("")

    # Stages
    stage_ids = []
    for i, stage in enumerate(stages):
        stage_name = stage.get("name", f"Stage {i+1}")
        stage_id = f"STAGE{i+1}"
        stage_ids.append(stage_id)

        activities = stage.get("activities", [])
        stakeholders = stage.get("stakeholders", [])
        systems = stage.get("systems", [])
        metrics = stage.get("metrics", {})

        # Stage subgraph
        mermaid.append(f"    %% {stage_name}")
        mermaid.append(f"    subgraph {stage_id} [\"{stage_name}\"]")
        mermaid.append(f"        direction TB")

        # Activities
        if activities:
            act_id = f"ACT{i+1}"
            act_list = "<br/>".join([f"• {a}" for a in activities])
            mermaid.append(f"        {act_id}[\"📋 Activities:<br/>{act_list}\"]")

        # Stakeholders
        if stakeholders:
            stake_id = f"STAKE{i+1}"
            stake_list = "<br/>".join([f"👤 {s}" for s in stakeholders])
            mermaid.append(f"        {stake_id}[\"{stake_list}\"]")

        # Systems
        if systems:
            sys_id = f"SYS{i+1}"
            sys_list = "<br/>".join([f"💻 {s}" for s in systems])
            mermaid.append(f"        {sys_id}[\"{sys_list}\"]")

        # Metrics
        if metrics:
            met_id = f"MET{i+1}"
            met_list = "<br/>".join([f"{k}: {v}" for k, v in metrics.items()])
            mermaid.append(f"        {met_id}[\"📊 {met_list}\"]")

        mermaid.append(f"    end")
        mermaid.append("")

    # Value Delivered node
    mermaid.append("    %% Value Delivered")
    mermaid.append(f"    VALUE([\"✅ {value_delivered}\"])")
    mermaid.append("")

    # Overall Metrics
    if overall_metrics:
        mermaid.append("    %% Overall Metrics")
        mermaid.append(f"    subgraph METRICS [\"📈 Overall Metrics\"]")
        for key, value in overall_metrics.items():
            label = key.replace("_", " ").title()
            met_id = f"METRIC_{sanitize_id(key)}"
            mermaid.append(f"        {met_id}[\"{label}: {value}\"]")
        mermaid.append(f"    end")
        mermaid.append("")

    # Flow connections
    mermaid.append("    %% Flow")
    mermaid.append(f"    TRIGGER --> STAGE1")
    for i in range(len(stage_ids) - 1):
        mermaid.append(f"    {stage_ids[i]} --> {stage_ids[i+1]}")
    if stage_ids:
        mermaid.append(f"    {stage_ids[-1]} --> VALUE")
    mermaid.append("")

    # Styling
    mermaid.append("    %% Styling")
    mermaid.append("    classDef triggerClass fill:#ffebee,stroke:#c62828,stroke-width:3px")
    mermaid.append("    classDef stageClass fill:#e3f2fd,stroke:#1976d2,stroke-width:2px")
    mermaid.append("    classDef valueClass fill:#e8f5e9,stroke:#388e3c,stroke-width:3px")
    mermaid.append("    classDef metricsClass fill:#fff9c4,stroke:#f57f17,stroke-width:2px")
    mermaid.append("")
    mermaid.append("    class TRIGGER triggerClass")
    mermaid.append("    class VALUE valueClass")

    for i in range(len(stages)):
        mermaid.append(f"    class ACT{i+1},STAKE{i+1},SYS{i+1},MET{i+1} stageClass")

    if overall_metrics:
        for key in overall_metrics.keys():
            met_id = f"METRIC_{sanitize_id(key)}"
            mermaid.append(f"    class {met_id} metricsClass")

    mermaid.append("```")

    return "\n".join(mermaid)


def generate_interactive_prompt():
    """Generate interactive prompts to gather data"""
    print("🌊 Value Stream Generator")
    print("=" * 50)

    name = input("Value Stream name: ").strip()
    trigger = input("Trigger event: ").strip()
    value_delivered = input("Value delivered: ").strip()

    print("\n📌 Stages (press Enter with empty name to finish)")
    stages = []
    i = 1
    while True:
        stage_name = input(f"\n  Stage {i} name (or Enter to finish): ").strip()
        if not stage_name:
            break

        print(f"  Activities for '{stage_name}' (comma-separated): ")
        activities_input = input("    ").strip()
        activities = [a.strip() for a in activities_input.split(",")] if activities_input else []

        print(f"  Stakeholders (comma-separated): ")
        stakeholders_input = input("    ").strip()
        stakeholders = [s.strip() for s in stakeholders_input.split(",")] if stakeholders_input else []

        print(f"  Systems (comma-separated): ")
        systems_input = input("    ").strip()
        systems = [s.strip() for s in systems_input.split(",")] if systems_input else []

        print(f"  Metrics (key=value, comma-separated, e.g., time=5min,automation=90%): ")
        metrics_input = input("    ").strip()
        metrics = {}
        if metrics_input:
            for pair in metrics_input.split(","):
                if "=" in pair:
                    k, v = pair.split("=", 1)
                    metrics[k.strip()] = v.strip()

        stages.append({
            "name": stage_name,
            "activities": activities,
            "stakeholders": stakeholders,
            "systems": systems,
            "metrics": metrics
        })
        i += 1

    print("\n📈 Overall Metrics (key=value, comma-separated): ")
    overall_input = input("  ").strip()
    overall_metrics = {}
    if overall_input:
        for pair in overall_input.split(","):
            if "=" in pair:
                k, v = pair.split("=", 1)
                overall_metrics[k.strip()] = v.strip()

    return {
        "name": name,
        "trigger": trigger,
        "value_delivered": value_delivered,
        "stages": stages,
        "overall_metrics": overall_metrics
    }


def main():
    if len(sys.argv) > 1:
        # Load from JSON file
        json_file = sys.argv[1]
        try:
            with open(json_file, 'r', encoding='utf-8') as f:
                data = json.load(f)
        except FileNotFoundError:
            print(f"❌ Error: File '{json_file}' not found")
            sys.exit(1)
        except json.JSONDecodeError as e:
            print(f"❌ Error: Invalid JSON - {e}")
            sys.exit(1)
    else:
        # Interactive mode
        data = generate_interactive_prompt()

    # Generate Mermaid diagram
    mermaid_output = generate_value_stream_mermaid(data)

    print("\n" + "=" * 50)
    print("📊 Value Stream Mermaid Diagram")
    print("=" * 50)
    print(mermaid_output)

    # Save to file
    output_file = "value_stream_diagram.md"
    with open(output_file, 'w', encoding='utf-8') as f:
        f.write(f"# Value Stream - {data.get('name', 'Value Stream')}\n\n")
        f.write(mermaid_output)

    print(f"\n✅ Diagram saved to: {output_file}")


if __name__ == "__main__":
    main()
