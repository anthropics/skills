#!/usr/bin/env python3
"""
Generate Capability Map Mermaid Diagram

This script generates a Mermaid diagram representing a Business Capability Map
with hierarchical levels and maturity heat map.

Usage:
    python generate_capability_map.py <input_json>

Input JSON structure:
{
    "organization": "Organization Name",
    "domains": [
        {
            "name": "Domain 1",
            "capabilities": [
                {
                    "name": "Capability 1.1",
                    "maturity_current": 2,
                    "maturity_target": 4,
                    "criticality": "HIGH",
                    "sub_capabilities": [
                        {
                            "name": "Sub-capability 1.1.1",
                            "maturity_current": 1,
                            "maturity_target": 3
                        }
                    ]
                }
            ]
        }
    ]
}

Maturity levels: 0-5 (0=doesn't exist, 5=optimized)
Criticality: LOW, MEDIUM, HIGH, CRITICAL
"""

import json
import sys


def sanitize_id(text):
    """Sanitize text for use as Mermaid node ID"""
    return text.replace(" ", "_").replace("-", "_").replace("&", "and").replace("/", "_")[:30]


def get_maturity_color(current, target, criticality):
    """Determine color based on maturity gap and criticality"""
    gap = target - current

    if gap == 0:
        return "#c8e6c9"  # Green - no gap
    elif gap <= 1 and criticality in ["LOW", "MEDIUM"]:
        return "#fff9c4"  # Yellow - small gap
    elif gap <= 2 and criticality in ["MEDIUM"]:
        return "#ffe0b2"  # Light orange
    else:
        return "#ffcdd2"  # Red - critical gap


def get_maturity_icon(current, target):
    """Get icon based on maturity status"""
    gap = target - current
    if gap == 0:
        return "✅"
    elif gap > 0 and gap <= 1:
        return "🟡"
    elif gap > 1 and gap <= 2:
        return "🟠"
    else:
        return "🔴"


def generate_capability_map_mermaid(data):
    """Generate Mermaid diagram for Capability Map"""

    org = data.get("organization", "Organization")
    domains = data.get("domains", [])

    # Build Mermaid diagram
    mermaid = []
    mermaid.append("```mermaid")
    mermaid.append("graph TB")
    mermaid.append("")
    mermaid.append(f"    %% Capability Map for {org}")
    mermaid.append("")

    # Root node
    mermaid.append("    %% Organization")
    mermaid.append(f"    ORG[\"{org}<br/>Capability Map\"]")
    mermaid.append("    style ORG fill:#e1f5fe,stroke:#01579b,stroke-width:3px")
    mermaid.append("")

    # Track all nodes for styling
    all_nodes = []

    # Domains (Level 1)
    for d_idx, domain in enumerate(domains):
        domain_name = domain.get("name", f"Domain {d_idx+1}")
        domain_id = f"DOM{d_idx+1}"

        mermaid.append(f"    %% Domain: {domain_name}")
        mermaid.append(f"    {domain_id}[\"{domain_name}\"]")
        mermaid.append(f"    ORG --> {domain_id}")
        mermaid.append("")

        # Capabilities (Level 2)
        capabilities = domain.get("capabilities", [])
        for c_idx, capability in enumerate(capabilities):
            cap_name = capability.get("name", f"Capability {c_idx+1}")
            cap_id = f"CAP{d_idx+1}_{c_idx+1}"
            current = capability.get("maturity_current", 0)
            target = capability.get("maturity_target", 0)
            criticality = capability.get("criticality", "MEDIUM")

            icon = get_maturity_icon(current, target)
            gap = target - current
            color = get_maturity_color(current, target, criticality)

            label = f"{icon} {cap_name}<br/><small>Current: L{current} → Target: L{target}</small>"
            if gap > 0:
                label += f"<br/><small>Gap: +{gap}</small>"

            mermaid.append(f"    {cap_id}[\"{label}\"]")
            mermaid.append(f"    {domain_id} --> {cap_id}")

            # Store for styling
            all_nodes.append({
                "id": cap_id,
                "color": color,
                "current": current,
                "target": target,
                "criticality": criticality
            })

            # Sub-capabilities (Level 3)
            sub_capabilities = capability.get("sub_capabilities", [])
            for s_idx, sub_cap in enumerate(sub_capabilities):
                sub_name = sub_cap.get("name", f"Sub-capability {s_idx+1}")
                sub_id = f"SUB{d_idx+1}_{c_idx+1}_{s_idx+1}"
                sub_current = sub_cap.get("maturity_current", 0)
                sub_target = sub_cap.get("maturity_target", 0)
                sub_criticality = sub_cap.get("criticality", criticality)  # Inherit from parent

                sub_icon = get_maturity_icon(sub_current, sub_target)
                sub_gap = sub_target - sub_current
                sub_color = get_maturity_color(sub_current, sub_target, sub_criticality)

                sub_label = f"{sub_icon} {sub_name}<br/><small>L{sub_current} → L{sub_target}</small>"

                mermaid.append(f"    {sub_id}[\"{sub_label}\"]")
                mermaid.append(f"    {cap_id} --> {sub_id}")

                # Store for styling
                all_nodes.append({
                    "id": sub_id,
                    "color": sub_color,
                    "current": sub_current,
                    "target": sub_target,
                    "criticality": sub_criticality
                })

        mermaid.append("")

    # Apply custom styling for each node
    mermaid.append("    %% Heat Map Styling (based on maturity gap)")
    for node in all_nodes:
        mermaid.append(f"    style {node['id']} fill:{node['color']},stroke:#333,stroke-width:2px")

    mermaid.append("")

    # Legend
    mermaid.append("    %% Legend")
    mermaid.append("    subgraph LEGEND [\"📊 Legend\"]")
    mermaid.append("        L1[\"✅ No Gap (On Target)\"]")
    mermaid.append("        L2[\"🟡 Small Gap (1 level)\"]")
    mermaid.append("        L3[\"🟠 Medium Gap (2 levels)\"]")
    mermaid.append("        L4[\"🔴 Critical Gap (3+ levels)\"]")
    mermaid.append("    end")
    mermaid.append("")
    mermaid.append("    style L1 fill:#c8e6c9,stroke:#388e3c")
    mermaid.append("    style L2 fill:#fff9c4,stroke:#f57f17")
    mermaid.append("    style L3 fill:#ffe0b2,stroke:#e64a19")
    mermaid.append("    style L4 fill:#ffcdd2,stroke:#c62828")

    mermaid.append("```")

    return "\n".join(mermaid)


def generate_interactive_prompt():
    """Generate interactive prompts to gather data"""
    print("🗺️  Capability Map Generator")
    print("=" * 50)

    org = input("Organization name: ").strip()

    print("\n📌 Domains (press Enter with empty name to finish)")
    domains = []
    d_idx = 1
    while True:
        domain_name = input(f"\n  Domain {d_idx} name (or Enter to finish): ").strip()
        if not domain_name:
            break

        print(f"\n  Capabilities for '{domain_name}' (press Enter with empty name to finish):")
        capabilities = []
        c_idx = 1
        while True:
            cap_name = input(f"    Capability {c_idx} name (or Enter to finish): ").strip()
            if not cap_name:
                break

            current = int(input(f"    Current maturity (0-5): ").strip() or "0")
            target = int(input(f"    Target maturity (0-5): ").strip() or "0")
            criticality = input(f"    Criticality (LOW/MEDIUM/HIGH/CRITICAL): ").strip().upper() or "MEDIUM"

            # Sub-capabilities (optional)
            print(f"    Sub-capabilities for '{cap_name}' (optional, Enter to skip):")
            sub_capabilities = []
            s_idx = 1
            while True:
                sub_name = input(f"      Sub-capability {s_idx} name (or Enter to skip): ").strip()
                if not sub_name:
                    break

                sub_current = int(input(f"      Current maturity (0-5): ").strip() or "0")
                sub_target = int(input(f"      Target maturity (0-5): ").strip() or "0")

                sub_capabilities.append({
                    "name": sub_name,
                    "maturity_current": sub_current,
                    "maturity_target": sub_target
                })
                s_idx += 1

            capabilities.append({
                "name": cap_name,
                "maturity_current": current,
                "maturity_target": target,
                "criticality": criticality,
                "sub_capabilities": sub_capabilities
            })
            c_idx += 1

        domains.append({
            "name": domain_name,
            "capabilities": capabilities
        })
        d_idx += 1

    return {
        "organization": org,
        "domains": domains
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
    mermaid_output = generate_capability_map_mermaid(data)

    print("\n" + "=" * 50)
    print("📊 Capability Map Mermaid Diagram")
    print("=" * 50)
    print(mermaid_output)

    # Save to file
    output_file = "capability_map_diagram.md"
    with open(output_file, 'w', encoding='utf-8') as f:
        f.write(f"# Capability Map - {data.get('organization', 'Organization')}\n\n")
        f.write(mermaid_output)

        # Add summary table
        f.write("\n\n## Capability Summary\n\n")
        f.write("| Domain | Capability | Current | Target | Gap | Criticality | Status |\n")
        f.write("|--------|------------|---------|--------|-----|-------------|--------|\n")

        for domain in data.get("domains", []):
            domain_name = domain.get("name", "")
            for cap in domain.get("capabilities", []):
                cap_name = cap.get("name", "")
                current = cap.get("maturity_current", 0)
                target = cap.get("maturity_target", 0)
                gap = target - current
                criticality = cap.get("criticality", "MEDIUM")
                icon = get_maturity_icon(current, target)

                f.write(f"| {domain_name} | {cap_name} | {current} | {target} | +{gap} | {criticality} | {icon} |\n")

    print(f"\n✅ Diagram saved to: {output_file}")


if __name__ == "__main__":
    main()
