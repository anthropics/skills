#!/usr/bin/env python3
"""
Quick validation script for skills - minimal version
"""

import sys
import os
import re
import yaml
from pathlib import Path

# Known tools available across Claude platforms.
# When a skill declares `allowed-tools`, each referenced tool is checked
# against this set. If a tool is missing, the platform would silently fail
# at runtime — this validation surfaces the problem early.
KNOWN_TOOLS = frozenset({
    # Claude Code built-in tools
    'Bash', 'Read', 'Write', 'Edit', 'Glob', 'Grep',
    'WebFetch', 'WebSearch', 'Think', 'Task', 'Plan',
    # Cross-platform tools
    'Skill', 'subagent', 'present_files', 'GroupChat',
    'AddMemory', 'Notebook',
    # Platform-specific / MCP-style tools
    'TextEditor', 'Computer', 'View', 'Replace',
    'Create', 'Delete', 'Move', 'Copy', 'Rename',
    'Search', 'List',
})


def _validate_allowed_tools(allowed_tools_value):
    """
    Validate the allowed-tools field from skill frontmatter.

    Format per spec:
        Space-separated list of ToolName or ToolName(filter) entries.
        Example: allowed-tools: Bash(git:*) Read WebFetch

    Returns a list of error messages (empty list means valid).
    """
    errors = []

    if not isinstance(allowed_tools_value, str):
        errors.append("Field 'allowed-tools' must be a string")
        return errors

    value = allowed_tools_value.strip()
    if not value:
        errors.append("Field 'allowed-tools' must be a non-empty string if specified")
        return errors

    entries = value.split()
    for entry in entries:
        # Match ToolName or ToolName(filter) where filter is any non-paren chars
        match = re.match(r'^([A-Za-z_]\w*)(?:\([^)]*\))?$', entry)
        if not match:
            errors.append(
                f"Invalid entry '{entry}' in 'allowed-tools'. "
                f"Expected format: ToolName or ToolName(filter)"
            )
            continue

        tool_name = match.group(1)
        if tool_name not in KNOWN_TOOLS:
            errors.append(
                f"Unknown tool '{tool_name}' in 'allowed-tools'. "
                f"This tool is not recognized on Claude platforms. "
                f"If '{tool_name}' is a valid third-party / MCP tool, "
                f"the skill should declare it as a dependency in the "
                f"'compatibility' field instead."
            )

    return errors


def validate_skill(skill_path):
    """Basic validation of a skill"""
    skill_path = Path(skill_path)

    # Check SKILL.md exists
    skill_md = skill_path / 'SKILL.md'
    if not skill_md.exists():
        return False, "SKILL.md not found"

    # Read and validate frontmatter
    content = skill_md.read_text()
    if not content.startswith('---'):
        return False, "No YAML frontmatter found"

    # Extract frontmatter
    match = re.match(r'^---\n(.*?)\n---', content, re.DOTALL)
    if not match:
        return False, "Invalid frontmatter format"

    frontmatter_text = match.group(1)

    # Parse YAML frontmatter
    try:
        frontmatter = yaml.safe_load(frontmatter_text)
        if not isinstance(frontmatter, dict):
            return False, "Frontmatter must be a YAML dictionary"
    except yaml.YAMLError as e:
        return False, f"Invalid YAML in frontmatter: {e}"

    # Define allowed properties
    ALLOWED_PROPERTIES = {'name', 'description', 'license', 'allowed-tools', 'metadata', 'compatibility'}

    # Check for unexpected properties (excluding nested keys under metadata)
    unexpected_keys = set(frontmatter.keys()) - ALLOWED_PROPERTIES
    if unexpected_keys:
        return False, (
            f"Unexpected key(s) in SKILL.md frontmatter: {', '.join(sorted(unexpected_keys))}. "
            f"Allowed properties are: {', '.join(sorted(ALLOWED_PROPERTIES))}"
        )

    # Check required fields
    if 'name' not in frontmatter:
        return False, "Missing 'name' in frontmatter"
    if 'description' not in frontmatter:
        return False, "Missing 'description' in frontmatter"

    # Extract name for validation
    name = frontmatter.get('name', '')
    if not isinstance(name, str):
        return False, f"Name must be a string, got {type(name).__name__}"
    name = name.strip()
    if name:
        # Check naming convention (kebab-case: lowercase with hyphens)
        if not re.match(r'^[a-z0-9-]+$', name):
            return False, f"Name '{name}' should be kebab-case (lowercase letters, digits, and hyphens only)"
        if name.startswith('-') or name.endswith('-') or '--' in name:
            return False, f"Name '{name}' cannot start/end with hyphen or contain consecutive hyphens"
        # Check name length (max 64 characters per spec)
        if len(name) > 64:
            return False, f"Name is too long ({len(name)} characters). Maximum is 64 characters."

    # Extract and validate description
    description = frontmatter.get('description', '')
    if not isinstance(description, str):
        return False, f"Description must be a string, got {type(description).__name__}"
    description = description.strip()
    if description:
        # Check for angle brackets
        if '<' in description or '>' in description:
            return False, "Description cannot contain angle brackets (< or >)"
        # Check description length (max 1024 characters per spec)
        if len(description) > 1024:
            return False, f"Description is too long ({len(description)} characters). Maximum is 1024 characters."

    # Validate compatibility field if present (optional)
    compatibility = frontmatter.get('compatibility', '')
    if compatibility:
        if not isinstance(compatibility, str):
            return False, f"Compatibility must be a string, got {type(compatibility).__name__}"
        if len(compatibility) > 500:
            return False, f"Compatibility is too long ({len(compatibility)} characters). Maximum is 500 characters."

    # Validate allowed-tools field if present (optional, experimental)
    allowed_tools = frontmatter.get('allowed-tools', '')
    if allowed_tools:
        tool_errors = _validate_allowed_tools(allowed_tools)
        if tool_errors:
            return False, "allowed-tools validation failed:\n  " + "\n  ".join(tool_errors)

    return True, "Skill is valid!"

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python quick_validate.py <skill_directory>")
        sys.exit(1)
    
    valid, message = validate_skill(sys.argv[1])
    print(message)
    sys.exit(0 if valid else 1)