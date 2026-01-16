#!/usr/bin/env python3
"""
Convert Agent Skills to CodeBuddy Workflow format

This script converts Agent Skills to CodeBuddy workflow format.
CodeBuddy supports workflows and tips plugins.

Usage:
    python convert_to_codebuddy.py <skill_path> [output_path]
    
Example:
    python convert_to_codebuddy.py ../../skills/course-designer codebuddy-plugins/
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
        body_start = match.end()
        body = content[body_start:].strip()
        return frontmatter, body
    return {}, content.strip()


def extract_workflow_from_body(body):
    """Extract workflow steps from skill body"""
    workflow = {
        "name": "",
        "description": "",
        "steps": []
    }
    
    lines = body.split('\n')
    current_section = None
    
    for i, line in enumerate(lines):
        # Extract workflow name from title
        if line.startswith('# ') and not workflow["name"]:
            workflow["name"] = line.replace('#', '').strip()
        
        # Extract description
        elif line.startswith('## 概述') or line.startswith('## Overview'):
            if i + 1 < len(lines):
                workflow["description"] = lines[i + 1].strip()
        
        # Extract steps from numbered lists
        elif re.match(r'^\d+\.', line.strip()):
            step_text = re.sub(r'^\d+\.\s*', '', line.strip())
            workflow["steps"].append({
                "id": len(workflow["steps"]) + 1,
                "name": step_text.split(':')[0] if ':' in step_text else step_text,
                "description": step_text,
                "type": "instruction"
            })
    
    # If no steps found, create default workflow
    if not workflow["steps"]:
        workflow["steps"] = [
            {
                "id": 1,
                "name": "analyze",
                "description": "Analyze requirements",
                "type": "instruction"
            },
            {
                "id": 2,
                "name": "execute",
                "description": "Execute skill task",
                "type": "instruction"
            },
            {
                "id": 3,
                "name": "output",
                "description": "Generate output",
                "type": "instruction"
            }
        ]
    
    return workflow


def convert_to_codebuddy_workflow(skill_path, output_dir=None):
    """
    Convert Agent Skill to CodeBuddy workflow format
    
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
    
    # Extract frontmatter and body
    frontmatter, body = extract_frontmatter(content)
    
    if not frontmatter:
        print(f"Warning: No frontmatter found in {skill_file}")
        frontmatter = {"name": skill_path.name, "description": ""}
    
    # Extract workflow
    workflow = extract_workflow_from_body(body)
    workflow["name"] = workflow["name"] or frontmatter.get("name", skill_path.name)
    workflow["description"] = workflow["description"] or frontmatter.get("description", "")
    
    # Create CodeBuddy plugin manifest
    plugin_manifest = {
        "name": frontmatter.get("name", skill_path.name),
        "version": "1.0.0",
        "description": frontmatter.get("description", ""),
        "author": "Teaching AI",
        "type": "workflow-plugin",
        "workflows": [
            {
                "id": frontmatter.get("name", skill_path.name),
                "name": workflow["name"],
                "description": workflow["description"],
                "steps": workflow["steps"],
                "inputs": [],
                "outputs": []
            }
        ]
    }
    
    # Write output
    if output_dir:
        output_dir = Path(output_dir)
        output_dir.mkdir(parents=True, exist_ok=True)
        
        # Create plugin directory
        plugin_dir = output_dir / frontmatter.get("name", skill_path.name)
        plugin_dir.mkdir(parents=True, exist_ok=True)
        
        # Create workflows directory
        workflows_dir = plugin_dir / "workflows"
        workflows_dir.mkdir(parents=True, exist_ok=True)
        
        # Write manifest
        manifest_file = plugin_dir / "manifest.json"
        with open(manifest_file, "w", encoding="utf-8") as f:
            json.dump(plugin_manifest, f, indent=2, ensure_ascii=False)
        
        # Write workflow file
        workflow_file = workflows_dir / f"{frontmatter.get('name', skill_path.name)}.json"
        with open(workflow_file, "w", encoding="utf-8") as f:
            json.dump(plugin_manifest["workflows"][0], f, indent=2, ensure_ascii=False)
        
        # Copy SKILL.md to skills directory
        skills_dir = plugin_dir / "skills" / frontmatter.get("name", skill_path.name)
        skills_dir.mkdir(parents=True, exist_ok=True)
        import shutil
        shutil.copy2(skill_file, skills_dir / "SKILL.md")
        
        print(f"✅ Converted to CodeBuddy plugin: {plugin_dir}")
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
                result = convert_to_codebuddy_workflow(skill_dir, output_dir)
                if result:
                    converted.append(skill_dir.name)
            except Exception as e:
                print(f"Error converting {skill_dir.name}: {e}")
    
    print(f"\n✅ Converted {len(converted)} skills: {', '.join(converted)}")
    return converted


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python convert_to_codebuddy.py <skill_path> [output_path]")
        print("   or: python convert_to_codebuddy.py --all <skills_dir> <output_dir>")
        sys.exit(1)
    
    if sys.argv[1] == "--all":
        if len(sys.argv) < 4:
            print("Usage: python convert_to_codebuddy.py --all <skills_dir> <output_dir>")
            sys.exit(1)
        convert_all_skills(sys.argv[2], sys.argv[3])
    else:
        skill_path = sys.argv[1]
        output_path = sys.argv[2] if len(sys.argv) > 2 else None
        convert_to_codebuddy_workflow(skill_path, output_path)
