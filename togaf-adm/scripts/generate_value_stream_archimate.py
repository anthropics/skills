#!/usr/bin/env python3
"""
Generate Value Stream ArchiMate Diagram (PlantUML)

This script generates a PlantUML ArchiMate diagram representing a Value Stream
with stages, business processes, actors, and application components.

Usage:
    python generate_value_stream_archimate.py <input_json>

Input JSON structure:
{
    "name": "Value Stream Name",
    "trigger": "Event that starts the value stream",
    "value_delivered": "Final value delivered",
    "stages": [
        {
            "name": "Stage 1",
            "process": "Business process name",
            "actors": ["Actor 1", "Actor 2"],
            "applications": ["App 1", "App 2"],
            "metrics": {"time": "5 min", "automation": "90%"}
        }
    ]
}
"""

import json
import sys


def sanitize_id(text):
    """Sanitize text for use as PlantUML identifier"""
    return text.replace(" ", "_").replace("-", "_").replace("&", "and").replace("/", "_").replace("(", "").replace(")", "").replace(":", "")[:30]


def generate_value_stream_archimate(data):
    """Generate PlantUML ArchiMate diagram for Value Stream"""

    name = data.get("name", "Value Stream")
    trigger = data.get("trigger", "Trigger Event")
    value_delivered = data.get("value_delivered", "Value Delivered")
    stages = data.get("stages", [])

    # Build PlantUML diagram
    puml = []
    puml.append("@startuml")
    puml.append("!include <archimate/Archimate>")
    puml.append("")
    puml.append(f"title Value Stream: {name}")
    puml.append("")
    puml.append("' ========================================")
    puml.append("' Value Stream and Trigger")
    puml.append("' ========================================")
    puml.append("")

    # Trigger event
    trigger_id = f"trigger_{sanitize_id(trigger[:20])}"
    puml.append(f"Business_Event({trigger_id}, \"{trigger}\")")
    puml.append("")

    # Main value stream
    vs_id = f"vs_{sanitize_id(name)}"
    puml.append(f"Value_Stream({vs_id}, \"{name}\")")
    puml.append("")

    # Value delivered
    value_id = "value_delivered"
    puml.append(f"Value({value_id}, \"{value_delivered}\")")
    puml.append("")

    # Process stages, actors, and applications
    puml.append("' ========================================")
    puml.append("' Stages: Business Processes, Actors, Applications")
    puml.append("' ========================================")
    puml.append("")

    process_ids = []
    for i, stage in enumerate(stages):
        stage_name = stage.get("name", f"Stage {i+1}")
        process_name = stage.get("process", stage_name)
        actors = stage.get("actors", [])
        applications = stage.get("applications", [])
        metrics = stage.get("metrics", {})

        # Business Process for this stage
        process_id = f"proc_{sanitize_id(stage_name)}_{i+1}"
        process_ids.append(process_id)

        # Add metrics to label
        metrics_str = ""
        if metrics:
            metrics_list = [f"{k}: {v}" for k, v in metrics.items()]
            metrics_str = f"\\n<size:9>{', '.join(metrics_list)}</size>"

        puml.append(f"' --- Stage {i+1}: {stage_name} ---")
        puml.append(f"Business_Process({process_id}, \"{process_name}{metrics_str}\")")

        # Actors that perform this process
        for j, actor_name in enumerate(actors):
            actor_id = f"actor_{sanitize_id(actor_name)}_{i+1}_{j+1}"
            puml.append(f"Business_Actor({actor_id}, \"{actor_name}\")")
            puml.append(f"Rel_Assignment({actor_id}, {process_id}, \"performs\")")

        # Applications that serve this process
        for j, app_name in enumerate(applications):
            app_id = f"app_{sanitize_id(app_name)}_{i+1}_{j+1}"
            puml.append(f"Application_Component({app_id}, \"{app_name}\")")
            puml.append(f"Rel_Serving({app_id}, {process_id}, \"supports\")")

        puml.append("")

    # Relationships
    puml.append("' ========================================")
    puml.append("' Value Stream Relationships")
    puml.append("' ========================================")
    puml.append("")

    # Trigger triggers the value stream
    puml.append(f"Rel_Triggering({trigger_id}, {vs_id})")
    puml.append("")

    # Value stream aggregates all processes
    puml.append("' Value Stream aggregates business processes")
    for pid in process_ids:
        puml.append(f"Rel_Aggregation({vs_id}, {pid})")
    puml.append("")

    # Flow through processes
    puml.append("' Flow through business processes")
    for i in range(len(process_ids) - 1):
        puml.append(f"Rel_Flow({process_ids[i]}, {process_ids[i+1]})")
    puml.append("")

    # Last process realizes the value
    if process_ids:
        puml.append(f"Rel_Realization({process_ids[-1]}, {value_id})")
    puml.append("")

    # Value stream realizes the value
    puml.append(f"Rel_Realization({vs_id}, {value_id})")
    puml.append("")

    # Layout hints
    puml.append("' ========================================")
    puml.append("' Layout Hints")
    puml.append("' ========================================")
    puml.append("")
    puml.append("left to right direction")
    puml.append("")

    # Arrange processes horizontally
    if len(process_ids) > 1:
        for i in range(len(process_ids) - 1):
            puml.append(f"{process_ids[i]} -[hidden]r- {process_ids[i+1]}")

    puml.append("")
    puml.append("@enduml")

    return "\n".join(puml)


def generate_interactive_prompt():
    """Generate interactive prompts to gather data"""
    print("🌊 ArchiMate Value Stream Generator")
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

        process_name = input(f"  Business process name (default: {stage_name}): ").strip() or stage_name

        print(f"  Actors for '{stage_name}' (comma-separated): ")
        actors_input = input("    ").strip()
        actors = [a.strip() for a in actors_input.split(",")] if actors_input else []

        print(f"  Applications (comma-separated): ")
        apps_input = input("    ").strip()
        applications = [s.strip() for s in apps_input.split(",")] if apps_input else []

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
            "process": process_name,
            "actors": actors,
            "applications": applications,
            "metrics": metrics
        })
        i += 1

    return {
        "name": name,
        "trigger": trigger,
        "value_delivered": value_delivered,
        "stages": stages
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

    # Generate PlantUML ArchiMate diagram
    puml_output = generate_value_stream_archimate(data)

    print("\n" + "=" * 50)
    print("📊 ArchiMate Value Stream Diagram (PlantUML)")
    print("=" * 50)
    print(puml_output)

    # Save to file
    output_file = "value_stream_archimate.puml"
    with open(output_file, 'w', encoding='utf-8') as f:
        f.write(puml_output)

    print(f"\n✅ Diagram saved to: {output_file}")
    print(f"\n💡 Render with: plantuml {output_file}")
    print(f"   Or use online: https://www.plantuml.com/plantuml/uml/")


if __name__ == "__main__":
    main()
