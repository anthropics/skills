#!/usr/bin/env python3
"""
Quick validation script for skills - minimal version
"""

import sys
import os
import re
import yaml
from pathlib import Path


def _utf8_byte_len(s):
    """Return the byte length of a string when encoded as UTF-8."""
    return len(s.encode('utf-8'))


def _truncate_utf8_safe(s, max_bytes):
    """Truncate a string to fit within max_bytes of UTF-8 without splitting multi-byte characters.

    Returns the truncated string by iterating over characters and accumulating
    their UTF-8 byte lengths, stopping before exceeding the limit.
    """
    byte_count = 0
    end_index = 0
    for i, ch in enumerate(s):
        char_bytes = len(ch.encode('utf-8'))
        if byte_count + char_bytes > max_bytes:
            break
        byte_count += char_bytes
        end_index = i + 1
    return s[:end_index]


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

    # Pre-parse check: detect unquoted values with special YAML characters
    # that would cause yaml.safe_load() to silently misparse them.
    YAML_SPECIAL_CHARS = {':', '#', '{', '}', '[', ']'}
    FIELDS_TO_CHECK = ['description', 'compatibility']
    for field in FIELDS_TO_CHECK:
        field_match = re.search(
            rf'^{re.escape(field)}:\s*(.+)$', frontmatter_text, re.MULTILINE
        )
        if field_match:
            raw_value = field_match.group(1).strip()
            # Skip values that are already properly quoted
            if (raw_value.startswith('"') and raw_value.endswith('"')) or \
               (raw_value.startswith("'") and raw_value.endswith("'")):
                continue
            # Check for special YAML characters in the unquoted value
            found_chars = [ch for ch in YAML_SPECIAL_CHARS if ch in raw_value]
            if found_chars:
                chars_display = ', '.join(repr(ch) for ch in sorted(found_chars))
                return False, (
                    f"The '{field}' value in SKILL.md frontmatter contains special "
                    f"YAML characters ({chars_display}) but is not quoted. "
                    f"This will cause the skill to silently fail to load. "
                    f"Wrap the value in quotes, e.g.:\n"
                    f"  {field}: \"your {field} text here\""
                )

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
        # Check name length (max 64 bytes in UTF-8 per spec)
        name_byte_len = _utf8_byte_len(name)
        if name_byte_len > 64:
            return False, f"Name is too long ({name_byte_len} bytes in UTF-8). Maximum is 64 bytes."

    # Extract and validate description
    description = frontmatter.get('description', '')
    if not isinstance(description, str):
        return False, f"Description must be a string, got {type(description).__name__}"
    description = description.strip()
    if description:
        # Check for angle brackets
        if '<' in description or '>' in description:
            return False, "Description cannot contain angle brackets (< or >)"
        # Check description length (max 1024 bytes in UTF-8 per spec)
        # Using byte length prevents downstream Rust panics from slicing
        # multi-byte UTF-8 characters (e.g., CJK characters, '。') at
        # invalid byte boundaries.
        desc_byte_len = _utf8_byte_len(description)
        if desc_byte_len > 1024:
            return False, f"Description is too long ({desc_byte_len} bytes in UTF-8). Maximum is 1024 bytes."

    # Validate compatibility field if present (optional)
    compatibility = frontmatter.get('compatibility', '')
    if compatibility:
        if not isinstance(compatibility, str):
            return False, f"Compatibility must be a string, got {type(compatibility).__name__}"
        compat_byte_len = _utf8_byte_len(compatibility)
        if compat_byte_len > 500:
            return False, f"Compatibility is too long ({compat_byte_len} bytes in UTF-8). Maximum is 500 bytes."

    return True, "Skill is valid!"

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python quick_validate.py <skill_directory>")
        sys.exit(1)
    
    valid, message = validate_skill(sys.argv[1])
    print(message)
    sys.exit(0 if valid else 1)