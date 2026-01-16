#!/usr/bin/env python3
"""
Convert Agent Skills to Windsurf format

This script converts Agent Skills to Windsurf Cascade Skills format.
Windsurf supports skills via .windsurf/skills/ directory.

Usage:
    python convert_to_windsurf.py <skill_path> [output_path]
    
Example:
    python convert_to_windsurf.py ../../skills/course-designer windsurf-skills/
"""

import sys
import re
import shutil
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
        body_start = match.end()
        body = content[body_start:].strip()
        return frontmatter, body
    else:
        return {}, content.strip()


def convert_to_windsurf_skill(skill_path, output_dir=None):
    """
    Convert Agent Skill to Windsurf format
    
    Args:
        skill_path: Path to skill directory containing SKILL.md
        output_dir: Output directory for Windsurf skills (optional)
    """
    skill_path = Path(skill_path)
    skill_file = skill_path / "SKILL.md"
    
    if not skill_file.exists():
        print(f"Error: SKILL.md not found in {skill_path}")
        return None
    
    # Read skill file
    with open(skill_file, "r", encoding="utf-8") as f:
        content = f.read()
    
    # Extract frontmatter and body
    frontmatter, body = extract_frontmatter(content)
    
    if not frontmatter:
        print(f"Warning: No frontmatter found in {skill_file}")
        frontmatter = {"name": skill_path.name, "description": ""}
    
    skill_name = frontmatter.get("name", skill_path.name)
    
    # Windsurf SKILL.md format (similar to Agent Skills, but may have slight differences)
    # Windsurf uses the same SKILL.md format with YAML frontmatter
    windsurf_skill_content = content  # Windsurf uses the same format, so we can use the original
    
    # Write output
    if output_dir:
        output_dir = Path(output_dir)
        output_dir.mkdir(parents=True, exist_ok=True)
        
        # Create skill directory
        skill_dir = output_dir / skill_name
        skill_dir.mkdir(parents=True, exist_ok=True)
        
        # Write SKILL.md
        skill_output_file = skill_dir / "SKILL.md"
        with open(skill_output_file, "w", encoding="utf-8") as f:
            f.write(windsurf_skill_content)
        
        # Copy additional resources if they exist
        resources_copied = []
        for resource_dir in ["scripts", "templates", "references", "assets", "examples"]:
            src_dir = skill_path / resource_dir
            if src_dir.exists() and src_dir.is_dir():
                dst_dir = skill_dir / resource_dir
                shutil.copytree(src_dir, dst_dir, dirs_exist_ok=True)
                resources_copied.append(resource_dir)
        
        # Copy other files (LICENSE, requirements.txt, etc.)
        for file in skill_path.iterdir():
            if file.is_file() and file.name not in ["SKILL.md", ".DS_Store"]:
                shutil.copy2(file, skill_dir / file.name)
                resources_copied.append(file.name)
        
        print(f"✅ Converted to Windsurf format: {skill_dir}")
        if resources_copied:
            print(f"   Copied resources: {', '.join(resources_copied)}")
        return skill_dir
    else:
        return windsurf_skill_content


def convert_all_skills(skills_dir, output_dir):
    """Convert all skills in a directory"""
    skills_dir = Path(skills_dir)
    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    
    converted = []
    for skill_dir in skills_dir.iterdir():
        if skill_dir.is_dir() and (skill_dir / "SKILL.md").exists():
            try:
                result = convert_to_windsurf_skill(skill_dir, output_dir)
                if result:
                    converted.append(skill_dir.name)
            except Exception as e:
                print(f"Error converting {skill_dir.name}: {e}")
    
    print(f"\n✅ Converted {len(converted)} skills: {', '.join(converted)}")
    return converted


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python convert_to_windsurf.py <skill_path> [output_path]")
        print("   or: python convert_to_windsurf.py --all <skills_dir> <output_dir>")
        sys.exit(1)
    
    if sys.argv[1] == "--all":
        if len(sys.argv) < 4:
            print("Usage: python convert_to_windsurf.py --all <skills_dir> <output_dir>")
            sys.exit(1)
        convert_all_skills(sys.argv[2], sys.argv[3])
    else:
        skill_path = sys.argv[1]
        output_path = sys.argv[2] if len(sys.argv) > 2 else None
        convert_to_windsurf_skill(skill_path, output_path)
