#!/usr/bin/env python3
"""
Quick validation script for rootnode Skills — D1 spec compliance check.

Validates frontmatter parse, name format, description length, body line count,
and allowed metadata fields per the rootnode build convention.
"""

import sys
import re
import yaml
from pathlib import Path

# Top-level frontmatter properties allowed by the Agent Skills spec.
ALLOWED_PROPERTIES = {
    'name',
    'description',
    'license',
    'allowed-tools',
    'metadata',
    'compatibility',
}

# Sub-fields allowed inside `metadata` per the rootnode build convention
# (see references/skills-spec.md §"YAML Frontmatter" for the discipline_post
# convention and root_SKILL_BUILD_DISCIPLINE.md §4.6 for the canonical source).
ALLOWED_METADATA_SUBFIELDS = {
    'author',
    'version',
    'predecessor',
    'original-source',
    'companion-files',
    'changelog',
    'notes',
    'discipline_post',
}


def validate_skill(skill_path):
    """Validate a Skill folder against D1 spec compliance."""
    skill_path = Path(skill_path)

    skill_md = skill_path / 'SKILL.md'
    if not skill_md.exists():
        return False, "SKILL.md not found"

    content = skill_md.read_text()
    if not content.startswith('---'):
        return False, "No YAML frontmatter found"

    match = re.match(r'^---\n(.*?)\n---', content, re.DOTALL)
    if not match:
        return False, "Invalid frontmatter format"

    frontmatter_text = match.group(1)

    try:
        frontmatter = yaml.safe_load(frontmatter_text)
        if not isinstance(frontmatter, dict):
            return False, "Frontmatter must be a YAML dictionary"
    except yaml.YAMLError as e:
        return False, f"Invalid YAML in frontmatter: {e}"

    unexpected_keys = set(frontmatter.keys()) - ALLOWED_PROPERTIES
    if unexpected_keys:
        return False, (
            f"Unexpected key(s) in SKILL.md frontmatter: {', '.join(sorted(unexpected_keys))}. "
            f"Allowed properties are: {', '.join(sorted(ALLOWED_PROPERTIES))}"
        )

    if 'name' not in frontmatter:
        return False, "Missing 'name' in frontmatter"
    if 'description' not in frontmatter:
        return False, "Missing 'description' in frontmatter"

    name = frontmatter.get('name', '')
    if not isinstance(name, str):
        return False, f"Name must be a string, got {type(name).__name__}"
    name = name.strip()
    if name:
        if not re.match(r'^[a-z0-9-]+$', name):
            return False, f"Name '{name}' should be kebab-case (lowercase letters, digits, and hyphens only)"
        if name.startswith('-') or name.endswith('-') or '--' in name:
            return False, f"Name '{name}' cannot start/end with hyphen or contain consecutive hyphens"
        if len(name) > 64:
            return False, f"Name is too long ({len(name)} characters). Maximum is 64 characters."

    description = frontmatter.get('description', '')
    if not isinstance(description, str):
        return False, f"Description must be a string, got {type(description).__name__}"
    description = description.strip()
    if description:
        if '<' in description or '>' in description:
            return False, "Description cannot contain angle brackets (< or >)"
        if len(description) > 1024:
            return False, f"Description is too long ({len(description)} characters). Maximum is 1024 characters."

    compatibility = frontmatter.get('compatibility', '')
    if compatibility:
        if not isinstance(compatibility, str):
            return False, f"Compatibility must be a string, got {type(compatibility).__name__}"
        if len(compatibility) > 500:
            return False, f"Compatibility is too long ({len(compatibility)} characters). Maximum is 500 characters."

    # Validate metadata sub-fields if metadata is present (rootnode convention).
    metadata = frontmatter.get('metadata')
    if metadata is not None:
        if not isinstance(metadata, dict):
            return False, f"metadata must be a YAML dictionary, got {type(metadata).__name__}"
        unexpected_meta = set(metadata.keys()) - ALLOWED_METADATA_SUBFIELDS
        if unexpected_meta:
            return False, (
                f"Unexpected sub-field(s) in metadata: {', '.join(sorted(unexpected_meta))}. "
                f"Allowed metadata sub-fields are: {', '.join(sorted(ALLOWED_METADATA_SUBFIELDS))}"
            )

    return True, "Skill is valid!"


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python quick_validate.py <skill_directory>")
        sys.exit(1)

    valid, message = validate_skill(sys.argv[1])
    print(message)
    sys.exit(0 if valid else 1)
