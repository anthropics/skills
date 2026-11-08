#!/usr/bin/env python3
"""
Scan local Claude Code skills and output their metadata as JSON.

Usage:
    python scan_skills.py [--path PATH] [--format FORMAT]

Options:
    --path PATH      Custom plugins path (default: ~/.claude/plugins)
    --format FORMAT  Output format: json, table, or brief (default: json)
"""

import os
import json
import re
import argparse
from pathlib import Path
from typing import Dict, List, Optional


def parse_skill_md(file_path: Path) -> Optional[Dict]:
    """Parse SKILL.md file and extract metadata."""
    try:
        content = file_path.read_text(encoding='utf-8')
    except Exception as e:
        return None

    # Extract YAML frontmatter
    frontmatter_match = re.match(r'^---\s*\n(.*?)\n---', content, re.DOTALL)
    if not frontmatter_match:
        return None

    frontmatter = frontmatter_match.group(1)

    # Parse name and description from frontmatter
    name_match = re.search(r'^name:\s*(.+)$', frontmatter, re.MULTILINE)
    desc_match = re.search(r'^description:\s*(.+?)(?=\n[a-z]+:|$)', frontmatter, re.MULTILINE | re.DOTALL)

    if not name_match:
        return None

    name = name_match.group(1).strip().strip('"\'')
    description = desc_match.group(1).strip().strip('"\'') if desc_match else ""

    # Clean up multiline descriptions
    description = ' '.join(description.split())

    return {
        'name': name,
        'description': description,
        'path': str(file_path.parent),
        'file': str(file_path)
    }


def scan_skills_directory(base_path: Path) -> List[Dict]:
    """Scan directory for SKILL.md files and collect metadata."""
    skills = []

    # Search patterns for skill locations
    search_patterns = [
        base_path / "**" / "SKILL.md",
    ]

    skill_files = set()
    for pattern in search_patterns:
        skill_files.update(base_path.glob("**/SKILL.md"))

    for skill_file in sorted(skill_files):
        metadata = parse_skill_md(skill_file)
        if metadata:
            skills.append(metadata)

    return skills


def get_default_plugins_path() -> Path:
    """Get default Claude plugins path."""
    home = Path.home()
    return home / ".claude" / "plugins"


def format_output(skills: List[Dict], format_type: str) -> str:
    """Format skills output based on requested format."""
    if format_type == "json":
        return json.dumps(skills, indent=2, ensure_ascii=False)

    elif format_type == "table":
        if not skills:
            return "No skills found."

        lines = []
        lines.append(f"{'Name':<25} {'Description':<60}")
        lines.append("-" * 85)

        for skill in skills:
            name = skill['name'][:24]
            desc = skill['description'][:59] if skill['description'] else "(no description)"
            lines.append(f"{name:<25} {desc:<60}")

        return "\n".join(lines)

    elif format_type == "brief":
        if not skills:
            return "No skills found."

        return "\n".join(f"- {s['name']}: {s['description'][:80]}..."
                        if len(s['description']) > 80
                        else f"- {s['name']}: {s['description']}"
                        for s in skills)

    return json.dumps(skills, indent=2, ensure_ascii=False)


def main():
    parser = argparse.ArgumentParser(description="Scan Claude Code skills")
    parser.add_argument("--path", type=str, help="Custom plugins path")
    parser.add_argument("--format", type=str, default="json",
                        choices=["json", "table", "brief"],
                        help="Output format")

    args = parser.parse_args()

    plugins_path = Path(args.path) if args.path else get_default_plugins_path()

    if not plugins_path.exists():
        print(json.dumps({"error": f"Path not found: {plugins_path}"}, indent=2))
        return 1

    skills = scan_skills_directory(plugins_path)

    # Sort by name
    skills.sort(key=lambda x: x['name'].lower())

    output = format_output(skills, args.format)
    print(output)

    return 0


if __name__ == "__main__":
    exit(main())
