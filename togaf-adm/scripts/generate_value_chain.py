#!/usr/bin/env python3
"""
Generate Value Chain Mermaid Diagram

This script generates a Mermaid diagram representing Porter's Value Chain
with primary and support activities.

Usage:
    python generate_value_chain.py <input_json>

Input JSON structure:
{
    "organization": "Organization Name",
    "support_activities": [
        {"name": "Infrastructure", "description": "Brief description"},
        {"name": "HR Management", "description": "Brief description"},
        {"name": "Technology", "description": "Brief description"},
        {"name": "Procurement", "description": "Brief description"}
    ],
    "primary_activities": [
        {"name": "Inbound Logistics", "description": "Brief description"},
        {"name": "Operations", "description": "Brief description"},
        {"name": "Outbound Logistics", "description": "Brief description"},
        {"name": "Marketing & Sales", "description": "Brief description"},
        {"name": "Service", "description": "Brief description"}
    ]
}
"""

import json
import sys


def generate_value_chain_mermaid(data):
    """Generate Mermaid diagram for Value Chain"""

    org = data.get("organization", "Organization")
    support = data.get("support_activities", [])
    primary = data.get("primary_activities", [])

    # Build Mermaid diagram
    mermaid = []
    mermaid.append("```mermaid")
    mermaid.append("graph TB")
    mermaid.append("")
    mermaid.append(f"    %% Value Chain for {org}")
    mermaid.append("")

    # Support Activities (top layer)
    mermaid.append("    %% Support Activities")
    mermaid.append("    subgraph Support [\"Support Activities (Margin)\"]")
    for i, activity in enumerate(support):
        node_id = f"SUP{i+1}"
        name = activity.get("name", f"Support {i+1}")
        desc = activity.get("description", "")
        label = f"{name}"
        if desc:
            label += f"<br/><small>{desc}</small>"
        mermaid.append(f"        {node_id}[\"{label}\"]")
    mermaid.append("    end")
    mermaid.append("")

    # Primary Activities (bottom layer)
    mermaid.append("    %% Primary Activities")
    mermaid.append("    subgraph Primary [\"Primary Activities\"]")
    for i, activity in enumerate(primary):
        node_id = f"PRI{i+1}"
        name = activity.get("name", f"Primary {i+1}")
        desc = activity.get("description", "")
        label = f"{name}"
        if desc:
            label += f"<br/><small>{desc}</small>"
        mermaid.append(f"        {node_id}[\"{label}\"]")
    mermaid.append("    end")
    mermaid.append("")

    # Margin node
    mermaid.append("    %% Margin")
    mermaid.append("    MARGIN([\"💰 MARGIN\"])")
    mermaid.append("")

    # Connections - Support to Primary (enabling relationship)
    mermaid.append("    %% Support enables Primary")
    for i in range(len(support)):
        mermaid.append(f"    SUP{i+1} -.->|enables| Primary")
    mermaid.append("")

    # Flow through Primary Activities
    mermaid.append("    %% Flow through Primary Activities")
    for i in range(len(primary) - 1):
        mermaid.append(f"    PRI{i+1} --> PRI{i+2}")

    # Last primary activity to Margin
    if primary:
        mermaid.append(f"    PRI{len(primary)} --> MARGIN")
    mermaid.append("")

    # Styling
    mermaid.append("    %% Styling")
    mermaid.append("    classDef supportClass fill:#e1f5ff,stroke:#0288d1,stroke-width:2px")
    mermaid.append("    classDef primaryClass fill:#fff3e0,stroke:#f57c00,stroke-width:2px")
    mermaid.append("    classDef marginClass fill:#c8e6c9,stroke:#388e3c,stroke-width:3px")
    mermaid.append("")

    for i in range(len(support)):
        mermaid.append(f"    class SUP{i+1} supportClass")
    for i in range(len(primary)):
        mermaid.append(f"    class PRI{i+1} primaryClass")
    mermaid.append("    class MARGIN marginClass")

    mermaid.append("```")

    return "\n".join(mermaid)


def generate_interactive_prompt():
    """Generate interactive prompts to gather data"""
    print("🔗 Value Chain Generator")
    print("=" * 50)

    org = input("Organization name: ").strip()

    print("\n📌 Support Activities (press Enter with empty name to finish)")
    support_activities = []
    i = 1
    while True:
        name = input(f"  Support Activity {i} name (or Enter to finish): ").strip()
        if not name:
            break
        desc = input(f"  Description (optional): ").strip()
        support_activities.append({"name": name, "description": desc})
        i += 1

    print("\n📌 Primary Activities (press Enter with empty name to finish)")
    primary_activities = []
    i = 1
    while True:
        name = input(f"  Primary Activity {i} name (or Enter to finish): ").strip()
        if not name:
            break
        desc = input(f"  Description (optional): ").strip()
        primary_activities.append({"name": name, "description": desc})
        i += 1

    return {
        "organization": org,
        "support_activities": support_activities,
        "primary_activities": primary_activities
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
    mermaid_output = generate_value_chain_mermaid(data)

    print("\n" + "=" * 50)
    print("📊 Value Chain Mermaid Diagram")
    print("=" * 50)
    print(mermaid_output)

    # Save to file
    output_file = "value_chain_diagram.md"
    with open(output_file, 'w', encoding='utf-8') as f:
        f.write(f"# Value Chain - {data.get('organization', 'Organization')}\n\n")
        f.write(mermaid_output)

    print(f"\n✅ Diagram saved to: {output_file}")


if __name__ == "__main__":
    main()
