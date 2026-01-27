import os
import sys
import json
import re

def stitch_skill(skill_dir):
    """
    Reads evolution.json and stitches it into SKILL.md under a dedicated section.
    """
    skill_md_path = os.path.join(skill_dir, "SKILL.md")
    evolution_json_path = os.path.join(skill_dir, "evolution.json")

    if not os.path.exists(skill_md_path):
        print(f"Error: SKILL.md not found in {skill_dir}", file=sys.stderr)
        return False
        
    if not os.path.exists(evolution_json_path):
        print(f"Info: No evolution.json found in {skill_dir}. Nothing to stitch.", file=sys.stderr)
        return True

    try:
        with open(evolution_json_path, 'r', encoding='utf-8') as f:
            data = json.load(f)
    except Exception as e:
        print(f"Error parsing evolution.json: {e}", file=sys.stderr)
        return False

    # Prepare the Markdown content block
    evolution_section = []
    evolution_section.append("\n\n## User-Learned Best Practices & Constraints")
    evolution_section.append("\n> **Auto-Generated Section**: This section is maintained by `skill-evolution-manager`. Do not edit manually.")
    
    if data.get("preferences"):
        evolution_section.append("\n### User Preferences")
        for item in data["preferences"]:
            evolution_section.append(f"- {item}")
            
    if data.get("fixes"):
        evolution_section.append("\n### Known Fixes & Workarounds")
        for item in data["fixes"]:
            evolution_section.append(f"- {item}")
            
    if data.get("custom_prompts"):
        evolution_section.append("\n### Custom Instruction Injection")
        evolution_section.append(f"\n{data['custom_prompts']}")
        
    evolution_block = "\n".join(evolution_section)

    # Read original SKILL.md
    with open(skill_md_path, 'r', encoding='utf-8') as f:
        content = f.read()

    # Regex to find existing User-Learned section and replace it, or append if not found
    # Pattern looks for "## User-Learned Best Practices..." until end of file
    pattern = r"(\n+## User-Learned Best Practices & Constraints.*$)"
    
    match = re.search(pattern, content, re.DOTALL)
    
    new_content = ""
    if match:
        # Replace existing section
        print("Updating existing evolution section...", file=sys.stderr)
        new_content = content[:match.start()] + evolution_block
    else:
        # Append to end
        print("Appending new evolution section...", file=sys.stderr)
        new_content = content + evolution_block

    # Write back
    with open(skill_md_path, 'w', encoding='utf-8') as f:
        f.write(new_content)
        
    print(f"Successfully stitched evolution data into {skill_md_path}")
    return True

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python smart_stitch.py <skill_dir>")
        sys.exit(1)
        
    target_dir = sys.argv[1]
    stitch_skill(target_dir)
