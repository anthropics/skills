"""Shared utilities for skill-creator scripts."""

from pathlib import Path

import yaml


def parse_skill_md(skill_path: Path) -> tuple[str, str, str]:
    """Parse a SKILL.md file, returning (name, description, full_content)."""
    content = (skill_path / "SKILL.md").read_text()
    lines = content.split("\n")

    if lines[0].strip() != "---":
        raise ValueError("SKILL.md missing frontmatter (no opening ---)")

    end_idx = None
    for i, line in enumerate(lines[1:], start=1):
        if line.strip() == "---":
            end_idx = i
            break

    if end_idx is None:
        raise ValueError("SKILL.md missing frontmatter (no closing ---)")

    try:
        frontmatter = yaml.safe_load("\n".join(lines[1:end_idx]) + "\n")
    except yaml.YAMLError as e:
        raise ValueError(f"Invalid YAML frontmatter in SKILL.md: {e}") from e

    if not isinstance(frontmatter, dict):
        raise ValueError("SKILL.md frontmatter must be a YAML mapping")

    name = frontmatter.get("name", "")
    description = frontmatter.get("description", "")
    if not isinstance(name, str) or not isinstance(description, str):
        raise ValueError("SKILL.md name and description must be strings")

    return name, description, content
