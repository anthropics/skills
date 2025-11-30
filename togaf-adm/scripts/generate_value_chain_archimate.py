#!/usr/bin/env python3
"""
Generate Value Chain ArchiMate Diagram (PlantUML)

This script generates a PlantUML ArchiMate diagram representing Porter's Value Chain
using Business Functions and aggregation relationships.

Usage:
    python generate_value_chain_archimate.py <input_json>

Input JSON structure:
{
    "organization": "Organization Name",
    "support_activities": [
        {"name": "Infrastructure", "description": "Brief description"}
    ],
    "primary_activities": [
        {"name": "Inbound Logistics", "description": "Brief description"}
    ]
}
"""

import json
import sys


def sanitize_id(text):
    """Sanitize text for use as PlantUML identifier"""
    return text.replace(" ", "_").replace("-", "_").replace("&", "and").replace("/", "_").replace("(", "").replace(")", "")[:30]


def generate_value_chain_archimate(data):
    """Generate PlantUML ArchiMate diagram for Value Chain"""

    org = data.get("organization", "Organization")
    support = data.get("support_activities", [])
    primary = data.get("primary_activities", [])

    # Build PlantUML diagram
    puml = []
    puml.append("@startuml")
    puml.append("!include <archimate/Archimate>")
    puml.append("")
    puml.append(f"title Value Chain - {org}")
    puml.append("")
    puml.append("' ========================================")
    puml.append("' Strategy: Value Stream representing the value chain")
    puml.append("' ========================================")
    puml.append("")

    # Main value stream
    puml.append(f"Value_Stream(valueChain, \"{org} Value Chain\")")
    puml.append("")

    # Support Activities (as Business Functions that support)
    puml.append("' ========================================")
    puml.append("' Support Activities (Business Functions)")
    puml.append("' ========================================")
    puml.append("")

    support_ids = []
    for i, activity in enumerate(support):
        activity_id = f"sup_{sanitize_id(activity.get('name', f'Support{i+1}'))}"
        support_ids.append(activity_id)
        name = activity.get("name", f"Support {i+1}")
        desc = activity.get("description", "")
        label = f"{name}\\n<size:10>{desc}</size>" if desc else name
        puml.append(f"Business_Function({activity_id}, \"{label}\")")

    puml.append("")

    # Primary Activities (as Business Functions in the value chain)
    puml.append("' ========================================")
    puml.append("' Primary Activities (Business Functions)")
    puml.append("' ========================================")
    puml.append("")

    primary_ids = []
    for i, activity in enumerate(primary):
        activity_id = f"pri_{sanitize_id(activity.get('name', f'Primary{i+1}'))}"
        primary_ids.append(activity_id)
        name = activity.get("name", f"Primary {i+1}")
        desc = activity.get("description", "")
        label = f"{name}\\n<size:10>{desc}</size>" if desc else name
        puml.append(f"Business_Function({activity_id}, \"{label}\")")

    puml.append("")

    # Margin/Value outcome
    puml.append("' ========================================")
    puml.append("' Value / Margin")
    puml.append("' ========================================")
    puml.append("")
    puml.append("Value(margin, \"Customer Value / Margin\")")
    puml.append("")

    # Relationships
    puml.append("' ========================================")
    puml.append("' Relationships")
    puml.append("' ========================================")
    puml.append("")

    # Value chain aggregates all primary activities
    puml.append("' Value Stream aggregates primary activities")
    for pid in primary_ids:
        puml.append(f"Rel_Aggregation(valueChain, {pid})")
    puml.append("")

    # Support activities serve/influence primary activities
    puml.append("' Support activities serve primary activities")
    for sid in support_ids:
        # Support serves all primary activities (simplified)
        puml.append(f"Rel_Influence({sid}, valueChain, \"enables\")")
    puml.append("")

    # Flow through primary activities
    puml.append("' Flow through primary activities")
    for i in range(len(primary_ids) - 1):
        puml.append(f"Rel_Flow({primary_ids[i]}, {primary_ids[i+1]})")

    # Last primary activity realizes value/margin
    if primary_ids:
        puml.append(f"Rel_Realization({primary_ids[-1]}, margin)")
    puml.append("")

    # Layout hints
    puml.append("' ========================================")
    puml.append("' Layout")
    puml.append("' ========================================")
    puml.append("")

    # Support activities on top
    if len(support_ids) > 1:
        for i in range(len(support_ids) - 1):
            puml.append(f"{support_ids[i]} -[hidden]r- {support_ids[i+1]}")

    # Primary activities in a row
    if len(primary_ids) > 1:
        for i in range(len(primary_ids) - 1):
            puml.append(f"{primary_ids[i]} -[hidden]r- {primary_ids[i+1]}")

    puml.append("")
    puml.append("@enduml")

    return "\n".join(puml)


def generate_interactive_prompt():
    """Generate interactive prompts to gather data"""
    print("🔗 ArchiMate Value Chain Generator")
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

    # Generate PlantUML ArchiMate diagram
    puml_output = generate_value_chain_archimate(data)

    print("\n" + "=" * 50)
    print("📊 ArchiMate Value Chain Diagram (PlantUML)")
    print("=" * 50)
    print(puml_output)

    # Save to file
    output_file = "value_chain_archimate.puml"
    with open(output_file, 'w', encoding='utf-8') as f:
        f.write(puml_output)

    print(f"\n✅ Diagram saved to: {output_file}")
    print(f"\n💡 Render with: plantuml {output_file}")
    print(f"   Or use online: https://www.plantuml.com/plantuml/uml/")


if __name__ == "__main__":
    main()
