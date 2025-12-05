#!/usr/bin/env python3
"""
Generate Capability Map ArchiMate Diagram (PlantUML)

This script generates a PlantUML ArchiMate diagram representing a hierarchical
Business Capability Map with maturity levels.

Usage:
    python generate_capability_map_archimate.py <input_json>

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
"""

import json
import sys


def sanitize_id(text):
    """Sanitize text for use as PlantUML identifier"""
    return text.replace(" ", "_").replace("-", "_").replace("&", "and").replace("/", "_").replace("(", "").replace(")", "")[:40]


def get_maturity_color(current, target, criticality):
    """Determine color based on maturity gap and criticality"""
    gap = target - current

    if gap == 0:
        return "#C8E6C9"  # Green - no gap
    elif gap == 1:
        return "#FFF9C4"  # Yellow - small gap
    elif gap == 2:
        return "#FFE0B2"  # Orange - medium gap
    else:
        return "#FFCDD2"  # Red - critical gap


def get_maturity_icon(current, target):
    """Get icon based on maturity status"""
    gap = target - current
    if gap == 0:
        return "✅"
    elif gap == 1:
        return "🟡"
    elif gap == 2:
        return "🟠"
    else:
        return "🔴"


def generate_capability_map_archimate(data):
    """Generate PlantUML ArchiMate diagram for Capability Map"""

    org = data.get("organization", "Organization")
    domains = data.get("domains", [])

    # Build PlantUML diagram
    puml = []
    puml.append("@startuml")
    puml.append("!include <archimate/Archimate>")
    puml.append("")
    puml.append(f"title Capability Map - {org}")
    puml.append("")
    puml.append("' ========================================")
    puml.append("' Organization")
    puml.append("' ========================================")
    puml.append("")

    # We won't create a root node, just group by domains

    # Track all capability IDs for coloring
    all_caps = []

    # Domains and Capabilities
    for d_idx, domain in enumerate(domains):
        domain_name = domain.get("name", f"Domain {d_idx+1}")
        domain_id = f"dom_{sanitize_id(domain_name)}"

        puml.append(f"' ========================================")
        puml.append(f"' Domain: {domain_name}")
        puml.append(f"' ========================================")
        puml.append("")

        # Domain as a grouping (we can use a high-level capability or just a note)
        puml.append(f"package \"{domain_name}\" {{")
        puml.append("")

        capabilities = domain.get("capabilities", [])
        for c_idx, capability in enumerate(capabilities):
            cap_name = capability.get("name", f"Capability {c_idx+1}")
            cap_id = f"cap_{d_idx+1}_{sanitize_id(cap_name)}"
            current = capability.get("maturity_current", 0)
            target = capability.get("maturity_target", 0)
            criticality = capability.get("criticality", "MEDIUM")

            icon = get_maturity_icon(current, target)
            gap = target - current
            color = get_maturity_color(current, target, criticality)

            # Label with maturity info
            label = f"{icon} {cap_name}\\nL{current} → L{target}"
            if gap > 0:
                label += f" (Gap: +{gap})"

            puml.append(f"  Capability({cap_id}, \"{label}\")")

            # Store for coloring
            all_caps.append({
                "id": cap_id,
                "color": color,
                "current": current,
                "target": target,
                "criticality": criticality
            })

            # Sub-capabilities
            sub_capabilities = capability.get("sub_capabilities", [])
            for s_idx, sub_cap in enumerate(sub_capabilities):
                sub_name = sub_cap.get("name", f"Sub-cap {s_idx+1}")
                sub_id = f"sub_{d_idx+1}_{c_idx+1}_{sanitize_id(sub_name)}"
                sub_current = sub_cap.get("maturity_current", 0)
                sub_target = sub_cap.get("maturity_target", 0)
                sub_criticality = sub_cap.get("criticality", criticality)

                sub_icon = get_maturity_icon(sub_current, sub_target)
                sub_gap = sub_target - sub_current
                sub_color = get_maturity_color(sub_current, sub_target, sub_criticality)

                sub_label = f"{sub_icon} {sub_name}\\nL{sub_current} → L{sub_target}"

                puml.append(f"  Capability({sub_id}, \"{sub_label}\")")

                # Aggregation relationship
                puml.append(f"  Rel_Aggregation({cap_id}, {sub_id})")

                # Store for coloring
                all_caps.append({
                    "id": sub_id,
                    "color": sub_color,
                    "current": sub_current,
                    "target": sub_target,
                    "criticality": sub_criticality
                })

            puml.append("")

        puml.append("}")
        puml.append("")

    # Legend
    puml.append("' ========================================")
    puml.append("' Legend")
    puml.append("' ========================================")
    puml.append("")
    puml.append("legend right")
    puml.append("  |<back:#C8E6C9>    </back>| ✅ No Gap (On Target) |")
    puml.append("  |<back:#FFF9C4>    </back>| 🟡 Small Gap (1 level) |")
    puml.append("  |<back:#FFE0B2>    </back>| 🟠 Medium Gap (2 levels) |")
    puml.append("  |<back:#FFCDD2>    </back>| 🔴 Critical Gap (3+ levels) |")
    puml.append("endlegend")
    puml.append("")

    # Styling
    puml.append("' ========================================")
    puml.append("' Styling (Color by Maturity Gap)")
    puml.append("' ========================================")
    puml.append("")

    for cap_info in all_caps:
        puml.append(f"{cap_info['id']} #back:{cap_info['color']}")

    puml.append("")
    puml.append("@enduml")

    return "\n".join(puml)


def generate_summary_table(data):
    """Generate markdown summary table"""
    lines = []
    lines.append("\n## Capability Summary\n")
    lines.append("| Domain | Capability | Current | Target | Gap | Criticality | Status |")
    lines.append("|--------|------------|---------|--------|-----|-------------|--------|")

    for domain in data.get("domains", []):
        domain_name = domain.get("name", "")
        for cap in domain.get("capabilities", []):
            cap_name = cap.get("name", "")
            current = cap.get("maturity_current", 0)
            target = cap.get("maturity_target", 0)
            gap = target - current
            criticality = cap.get("criticality", "MEDIUM")
            icon = get_maturity_icon(current, target)

            lines.append(f"| {domain_name} | {cap_name} | {current} | {target} | +{gap} | {criticality} | {icon} |")

    return "\n".join(lines)


def generate_interactive_prompt():
    """Generate interactive prompts to gather data"""
    print("🗺️  ArchiMate Capability Map Generator")
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

    # Generate PlantUML ArchiMate diagram
    puml_output = generate_capability_map_archimate(data)

    print("\n" + "=" * 50)
    print("📊 ArchiMate Capability Map Diagram (PlantUML)")
    print("=" * 50)
    print(puml_output)

    # Save to file
    output_file = "capability_map_archimate.puml"
    with open(output_file, 'w', encoding='utf-8') as f:
        f.write(puml_output)

    # Save summary table
    summary_file = "capability_map_summary.md"
    with open(summary_file, 'w', encoding='utf-8') as f:
        f.write(f"# Capability Map - {data.get('organization', 'Organization')}\n\n")
        f.write("See `capability_map_archimate.puml` for the ArchiMate diagram.\n")
        f.write(generate_summary_table(data))

    print(f"\n✅ Diagram saved to: {output_file}")
    print(f"✅ Summary saved to: {summary_file}")
    print(f"\n💡 Render with: plantuml {output_file}")
    print(f"   Or use online: https://www.plantuml.com/plantuml/uml/")


if __name__ == "__main__":
    main()
