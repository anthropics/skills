#!/usr/bin/env python3
"""
Convert Agent Skills to Cursor format

This script converts Agent Skills to Cursor custom instruction format.
Cursor supports custom instructions via .cursorrules files or project context.

Usage:
    python convert_to_cursor.py <skill_path> [output_path]
    
Example:
    python convert_to_cursor.py ../../skills/course-designer .cursor/rules/
"""

import sys
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
        body_start = match.end()
        body = content[body_start:].strip()
        return frontmatter, body
    else:
        return {}, content.strip()


def convert_to_cursor_rule(skill_path, output_dir=None):
    """
    Convert Agent Skill to Cursor custom instruction format
    
    Args:
        skill_path: Path to skill directory containing SKILL.md
        output_dir: Output directory for .cursorrules file (optional)
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
    
    # Create Cursor rule format
    cursor_rule = f"""# {frontmatter.get('name', skill_path.name).replace('-', ' ').title()}

## Description
{frontmatter.get('description', 'No description available')}

## When to Use
Use this skill when the user asks about: {frontmatter.get('description', 'related tasks')}

## Instructions

{body}
"""
    
    # Write output
    if output_dir:
        output_dir = Path(output_dir)
        output_dir.mkdir(parents=True, exist_ok=True)
        output_file = output_dir / f"{frontmatter.get('name', skill_path.name)}.md"
        with open(output_file, "w", encoding="utf-8") as f:
            f.write(cursor_rule)
        print(f"✅ Converted to Cursor format: {output_file}")
        return output_file
    else:
        return cursor_rule


def convert_all_skills(skills_dir, output_dir):
    """Convert all skills in a directory"""
    skills_dir = Path(skills_dir)
    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    
    converted = []
    for skill_dir in skills_dir.iterdir():
        if skill_dir.is_dir() and (skill_dir / "SKILL.md").exists():
            try:
                result = convert_to_cursor_rule(skill_dir, output_dir)
                if result:
                    converted.append(skill_dir.name)
            except Exception as e:
                print(f"Error converting {skill_dir.name}: {e}")
    
    print(f"\n✅ Converted {len(converted)} skills: {', '.join(converted)}")
    return converted


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python convert_to_cursor.py <skill_path> [output_path]")
        print("   or: python convert_to_cursor.py --all <skills_dir> <output_dir>")
        sys.exit(1)
    
    if sys.argv[1] == "--all":
        if len(sys.argv) < 4:
            print("Usage: python convert_to_cursor.py --all <skills_dir> <output_dir>")
            sys.exit(1)
        convert_all_skills(sys.argv[2], sys.argv[3])
    else:
        skill_path = sys.argv[1]
        output_path = sys.argv[2] if len(sys.argv) > 2 else None
        convert_to_cursor_rule(skill_path, output_path)
