#!/usr/bin/env python3
"""
Convert Agent Skills to Trae format

This script converts Agent Skills to Trae plugin format.
Trae plugins use a manifest.json file to define plugin metadata and skills.

Usage:
    python convert_to_trae.py <skill_path> [output_path]
    
Example:
    python convert_to_trae.py ../../skills/course-designer trae-plugins/
"""

import sys
import json
import re
from pathlib import Path

try:
    import yaml
    HAS_YAML = True
except ImportError:
    HAS_YAML = False


def parse_yaml_simple(text):
    """Simple YAML parser for frontmatter (handles basic key: value pairs)"""
    result = {}
    for line in text.split('\n'):
        line = line.strip()
        if ':' in line and not line.startswith('#'):
            key, value = line.split(':', 1)
            key = key.strip()
            value = value.strip().strip('"').strip("'")
            result[key] = value
    return result


def extract_frontmatter(content):
    """Extract YAML frontmatter from SKILL.md"""
    frontmatter_pattern = r'^---\n(.*?)\n---\n'
    match = re.match(frontmatter_pattern, content, re.DOTALL)
    
    if match:
        frontmatter_text = match.group(1)
        if HAS_YAML:
            frontmatter = yaml.safe_load(frontmatter_text)
        else:
            frontmatter = parse_yaml_simple(frontmatter_text)
        return frontmatter
    return {}


def convert_to_trae_plugin(skill_path, output_dir=None):
    """
    Convert Agent Skill to Trae plugin format
    
    Args:
        skill_path: Path to skill directory containing SKILL.md
        output_dir: Output directory for plugin (optional)
    """
    skill_path = Path(skill_path)
    skill_file = skill_path / "SKILL.md"
    
    if not skill_file.exists():
        print(f"Error: SKILL.md not found in {skill_path}")
        return None
    
    # Read skill file
    with open(skill_file, "r", encoding="utf-8") as f:
        content = f.read()
    
    # Extract frontmatter
    frontmatter = extract_frontmatter(content)
    
    if not frontmatter:
        print(f"Warning: No frontmatter found in {skill_file}")
        frontmatter = {"name": skill_path.name, "description": ""}
    
    # Create Trae plugin manifest
    plugin_manifest = {
        "name": frontmatter.get("name", skill_path.name),
        "version": "1.0.0",
        "description": frontmatter.get("description", ""),
        "author": "Teaching AI",
        "type": "skill",
        "skills": [
            {
                "name": frontmatter.get("name", skill_path.name),
                "description": frontmatter.get("description", ""),
                "instructions": "SKILL.md",
                "resources": []
            }
        ]
    }
    
    # Check for additional resources
    if (skill_path / "scripts").exists():
        plugin_manifest["skills"][0]["resources"].append("scripts/")
    if (skill_path / "references").exists():
        plugin_manifest["skills"][0]["resources"].append("references/")
    if (skill_path / "assets").exists():
        plugin_manifest["skills"][0]["resources"].append("assets/")
    
    # Write output
    if output_dir:
        output_dir = Path(output_dir)
        output_dir.mkdir(parents=True, exist_ok=True)
        
        # Create plugin directory
        plugin_dir = output_dir / frontmatter.get("name", skill_path.name)
        plugin_dir.mkdir(parents=True, exist_ok=True)
        
        # Write manifest
        manifest_file = plugin_dir / "trae-plugin.json"
        with open(manifest_file, "w", encoding="utf-8") as f:
            json.dump(plugin_manifest, f, indent=2, ensure_ascii=False)
        
        # Copy SKILL.md
        import shutil
        shutil.copy2(skill_file, plugin_dir / "SKILL.md")
        
        print(f"✅ Converted to Trae plugin: {plugin_dir}")
        return plugin_dir
    else:
        return plugin_manifest


def convert_all_skills(skills_dir, output_dir):
    """Convert all skills in a directory"""
    skills_dir = Path(skills_dir)
    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    
    converted = []
    for skill_dir in skills_dir.iterdir():
        if skill_dir.is_dir() and (skill_dir / "SKILL.md").exists():
            try:
                result = convert_to_trae_plugin(skill_dir, output_dir)
                if result:
                    converted.append(skill_dir.name)
            except Exception as e:
                print(f"Error converting {skill_dir.name}: {e}")
    
    print(f"\n✅ Converted {len(converted)} skills: {', '.join(converted)}")
    return converted


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python convert_to_trae.py <skill_path> [output_path]")
        print("   or: python convert_to_trae.py --all <skills_dir> <output_dir>")
        sys.exit(1)
    
    if sys.argv[1] == "--all":
        if len(sys.argv) < 4:
            print("Usage: python convert_to_trae.py --all <skills_dir> <output_dir>")
            sys.exit(1)
        convert_all_skills(sys.argv[2], sys.argv[3])
    else:
        skill_path = sys.argv[1]
        output_path = sys.argv[2] if len(sys.argv) > 2 else None
        convert_to_trae_plugin(skill_path, output_path)
