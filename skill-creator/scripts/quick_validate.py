#!/usr/bin/env python3
"""
Quick validation script for skills - minimal version
"""

import sys
import os
import re
from pathlib import Path

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

    frontmatter = match.group(1)

    # Define allowed frontmatter properties
    allowed_properties = {'name', 'description', 'license', 'allowed-tools', 'metadata'}

    # Extract all property keys from frontmatter (only top-level keys)
    property_keys = set()
    for line in frontmatter.split('\n'):
        # Skip comments
        if line.strip().startswith('#'):
            continue
        # Only consider lines that start at column 0 (top-level keys)
        # Indented lines are nested values (like metadata children)
        if ':' in line and not line.startswith(' ') and not line.startswith('\t'):
            # Extract key before the colon
            key = line.split(':')[0].strip()
            if key:  # Skip empty keys
                property_keys.add(key)

    # Check for unexpected properties
    unexpected_properties = property_keys - allowed_properties
    if unexpected_properties:
        unexpected_list = ', '.join(sorted(unexpected_properties))
        allowed_list = ', '.join(sorted(allowed_properties))
        return False, f"Unexpected key(s) in SKILL.md frontmatter: {unexpected_list}. Allowed properties: {allowed_list}"

    # Check required fields
    if 'name' not in property_keys:
        return False, "Missing 'name' in frontmatter"
    if 'description' not in property_keys:
        return False, "Missing 'description' in frontmatter"

    # Extract name for validation
    name_match = re.search(r'name:\s*(.+)', frontmatter)
    if name_match:
        name = name_match.group(1).strip()
        # Check naming convention (hyphen-case: lowercase with hyphens)
        if not re.match(r'^[a-z0-9-]+$', name):
            return False, f"Name '{name}' should be hyphen-case (lowercase letters, digits, and hyphens only)"
        if name.startswith('-') or name.endswith('-') or '--' in name:
            return False, f"Name '{name}' cannot start/end with hyphen or contain consecutive hyphens"

    # Extract and validate description
    desc_match = re.search(r'description:\s*(.+)', frontmatter)
    if desc_match:
        description = desc_match.group(1).strip()
        # Check for angle brackets
        if '<' in description or '>' in description:
            return False, "Description cannot contain angle brackets (< or >)"
        # Check description length (max 1024 characters)
        if len(description) > 1024:
            return False, f"Description too long ({len(description)} characters). Maximum 1024 characters allowed"

    return True, "Skill is valid!"

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python quick_validate.py <skill_directory>")
        sys.exit(1)
    
    valid, message = validate_skill(sys.argv[1])
    print(message)
    sys.exit(0 if valid else 1)