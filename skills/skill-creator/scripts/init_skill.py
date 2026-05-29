#!/usr/bin/env python3
"""Initialize a new Anthropic skill from a template.

Usage:
    python init_skill.py <skill-name> [--description "Description of the skill"]
    python init_skill.py <skill-name> --interactive

Creates a new skill directory with the standard structure:
    <skill-name>/
    ├── SKILL.md
    ├── scripts/
    ├── references/
    ├── assets/
    └── evals/
"""

import argparse
import os
import re
import sys
from pathlib import Path

SKILL_MD_TEMPLATE = """\
---
name: {name}
description: {description}
---

# {title}

## Overview

{description}

## Instructions

TODO: Write instructions for Claude here. Start with the most common
workflow, then handle edge cases.

## Output Format

TODO: Describe the expected output format, if applicable.
"""

EVALS_JSON_TEMPLATE = """\
{{
  "skill_name": "{name}",
  "evals": []
}}
"""

EVAL_METADATA_TEMPLATE = """\
{{
  "eval_id": 0,
  "eval_name": "descriptive-name-here",
  "prompt": "TODO: The user's task prompt",
  "assertions": []
}}
"""


def sanitize_name(name: str) -> str:
    """Convert to kebab-case skill name."""
    name = name.strip().lower()
    name = re.sub(r"[^a-z0-9]+", "-", name)
    name = re.sub(r"-+", "-", name)
    name = name.strip("-")
    return name


def title_case(name: str) -> str:
    """Convert kebab-case to Title Case."""
    return " ".join(word.capitalize() for word in name.split("-"))


def init_skill(name: str, description: str) -> Path:
    """Create a new skill directory with standard structure."""
    skill_dir = Path(name)
    if skill_dir.exists():
        print(f"Error: {skill_dir} already exists", file=sys.stderr)
        sys.exit(1)

    skill_dir.mkdir()
    (skill_dir / "scripts").mkdir()
    (skill_dir / "references").mkdir()
    (skill_dir / "assets").mkdir()
    (skill_dir / "evals").mkdir()

    # Write SKILL.md
    skill_md = SKILL_MD_TEMPLATE.format(
        name=name,
        title=title_case(name),
        description=description,
    )
    (skill_dir / "SKILL.md").write_text(skill_md)

    # Write empty evals.json
    (skill_dir / "evals" / "evals.json").write_text(
        EVALS_JSON_TEMPLATE.format(name=name)
    )

    print(f"Created skill: {skill_dir}/")
    print(f"  SKILL.md       - Edit the description and instructions")
    print(f"  scripts/       - Add executable scripts here")
    print(f"  references/    - Add reference docs here")
    print(f"  assets/        - Add templates, icons, etc.")
    print(f"  evals/         - Add test cases to evals.json")
    return skill_dir


def main():
    parser = argparse.ArgumentParser(
        description="Initialize a new Anthropic skill from a template."
    )
    parser.add_argument("name", help="Skill name (kebab-case)")
    parser.add_argument(
        "-d", "--description",
        default="TODO: Describe what this skill does and when it should trigger.",
        help="Skill description (used in frontmatter and docs)",
    )
    parser.add_argument(
        "-i", "--interactive",
        action="store_true",
        help="Prompt for name and description interactively",
    )
    args = parser.parse_args()

    name = sanitize_name(args.name)
    if not name:
        print("Error: skill name cannot be empty", file=sys.stderr)
        sys.exit(1)

    description = args.description
    if args.interactive:
        print(f"Skill name: {name}")
        desc = input("Description: ").strip()
        if desc:
            description = desc

    init_skill(name, description)


if __name__ == "__main__":
    main()
