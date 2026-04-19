#!/usr/bin/env python3
"""
Validate the marketplace against the Agent Skills and Claude Code plugin schemas.

Checks:
  1. .claude-plugin/marketplace.json      — required fields, kebab-case names,
                                            reserved-name collisions, plugin entries
  2. plugins/*/.claude-plugin/plugin.json — required fields, version present
  3. plugins/*/skills/*/SKILL.md          — YAML frontmatter with name +
                                            description, description length,
                                            kebab-case name, no angle brackets

Exits 0 on success, 1 on the first error. Designed to run cleanly in CI and
locally via `python scripts/validate.py` from the repo root.

The authoritative validator is `claude plugin validate .` from the Claude Code
CLI. This script is a lightweight stand-in suitable for CI runners that do not
have Claude Code installed.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

import yaml

REPO_ROOT = Path(__file__).resolve().parent.parent

# Names reserved by Anthropic per the plugin marketplaces docs. Third-party
# marketplaces cannot use these, and names that impersonate official Anthropic
# marketplaces are also rejected.
RESERVED_MARKETPLACE_NAMES = {
    "claude-code-marketplace",
    "claude-code-plugins",
    "claude-plugins-official",
    "anthropic-marketplace",
    "anthropic-plugins",
    "agent-skills",
    "knowledge-work-plugins",
    "life-sciences",
}

KEBAB_CASE = re.compile(r"^[a-z0-9]+(-[a-z0-9]+)*$")

# Agent Skills spec: description up to 1024 chars; name up to 64.
MAX_DESCRIPTION_LEN = 1024
MAX_NAME_LEN = 64


class ValidationError(Exception):
    """Raised when a schema or convention check fails."""


def fail(message: str) -> None:
    print(f"❌ {message}", file=sys.stderr)
    raise ValidationError(message)


def ok(message: str) -> None:
    print(f"✅ {message}")


def check_kebab_case(value: str, label: str) -> None:
    if not KEBAB_CASE.match(value):
        fail(f"{label} '{value}' is not kebab-case (lowercase letters, digits, hyphens)")
    if len(value) > MAX_NAME_LEN:
        fail(f"{label} '{value}' is {len(value)} chars (max {MAX_NAME_LEN})")


def check_description(value: str, label: str) -> None:
    if not isinstance(value, str) or not value.strip():
        fail(f"{label} description must be a non-empty string")
    if "<" in value or ">" in value:
        fail(f"{label} description cannot contain angle brackets (< or >)")
    if len(value) > MAX_DESCRIPTION_LEN:
        fail(f"{label} description is {len(value)} chars (max {MAX_DESCRIPTION_LEN})")


def validate_marketplace(manifest_path: Path) -> list[dict]:
    """Validate marketplace.json and return its plugin entries."""
    try:
        data = json.loads(manifest_path.read_text())
    except json.JSONDecodeError as e:
        fail(f"{manifest_path} is not valid JSON: {e}")

    for field in ("name", "owner", "plugins"):
        if field not in data:
            fail(f"{manifest_path} missing required field '{field}'")

    name = data["name"]
    check_kebab_case(name, "marketplace.name")
    if name in RESERVED_MARKETPLACE_NAMES:
        fail(f"marketplace.name '{name}' is reserved for official Anthropic use")

    owner = data["owner"]
    if not isinstance(owner, dict) or "name" not in owner:
        fail("marketplace.owner must be an object with a 'name' field")

    plugins = data["plugins"]
    if not isinstance(plugins, list) or not plugins:
        fail("marketplace.plugins must be a non-empty array")

    seen_names: set[str] = set()
    for idx, plugin in enumerate(plugins):
        label = f"plugins[{idx}]"
        if "name" not in plugin or "source" not in plugin:
            fail(f"{label} missing required 'name' or 'source'")
        check_kebab_case(plugin["name"], f"{label}.name")
        if plugin["name"] in seen_names:
            fail(f"Duplicate plugin name '{plugin['name']}' in marketplace")
        seen_names.add(plugin["name"])
        if "description" in plugin:
            check_description(plugin["description"], f"{label}")

    ok(f"{manifest_path.relative_to(REPO_ROOT)} is valid")
    return plugins


def validate_plugin_manifest(plugin_json: Path) -> None:
    try:
        data = json.loads(plugin_json.read_text())
    except json.JSONDecodeError as e:
        fail(f"{plugin_json} is not valid JSON: {e}")

    for field in ("name", "description", "version"):
        if field not in data:
            fail(f"{plugin_json} missing required field '{field}'")

    check_kebab_case(data["name"], f"{plugin_json.relative_to(REPO_ROOT)}.name")
    check_description(data["description"], f"{plugin_json.relative_to(REPO_ROOT)}")

    ok(f"{plugin_json.relative_to(REPO_ROOT)} is valid")


def validate_skill_md(skill_md: Path) -> None:
    content = skill_md.read_text()
    if not content.startswith("---"):
        fail(f"{skill_md.relative_to(REPO_ROOT)} missing YAML frontmatter")

    match = re.match(r"^---\n(.*?)\n---", content, re.DOTALL)
    if not match:
        fail(f"{skill_md.relative_to(REPO_ROOT)} frontmatter is malformed")

    try:
        frontmatter = yaml.safe_load(match.group(1)) or {}
    except yaml.YAMLError as e:
        fail(f"{skill_md.relative_to(REPO_ROOT)} YAML is invalid: {e}")

    if "name" not in frontmatter:
        fail(f"{skill_md.relative_to(REPO_ROOT)} frontmatter missing 'name'")
    if "description" not in frontmatter:
        fail(f"{skill_md.relative_to(REPO_ROOT)} frontmatter missing 'description'")

    check_kebab_case(frontmatter["name"], f"{skill_md.relative_to(REPO_ROOT)}.name")
    check_description(
        frontmatter["description"], f"{skill_md.relative_to(REPO_ROOT)}"
    )

    # The folder name must match the frontmatter name (this is a convention
    # followed by every platform — Claude Code, Codex, Gemini CLI all expect it).
    folder_name = skill_md.parent.name
    if folder_name != frontmatter["name"]:
        fail(
            f"{skill_md.relative_to(REPO_ROOT)}: frontmatter name "
            f"'{frontmatter['name']}' does not match folder name '{folder_name}'"
        )

    ok(f"{skill_md.relative_to(REPO_ROOT)} is valid")


def main() -> int:
    print(f"Validating {REPO_ROOT}\n")
    try:
        # 1. Marketplace manifest
        marketplace_json = REPO_ROOT / ".claude-plugin" / "marketplace.json"
        if not marketplace_json.exists():
            fail(f"{marketplace_json.relative_to(REPO_ROOT)} not found")
        validate_marketplace(marketplace_json)

        # 2. Each plugin manifest
        plugin_manifests = sorted(
            REPO_ROOT.glob("plugins/*/.claude-plugin/plugin.json")
        )
        if not plugin_manifests:
            fail("No plugin.json files found under plugins/*/.claude-plugin/")
        for manifest in plugin_manifests:
            validate_plugin_manifest(manifest)

        # 3. Each SKILL.md
        skill_files = sorted(REPO_ROOT.glob("plugins/*/skills/*/SKILL.md"))
        if not skill_files:
            fail("No SKILL.md files found under plugins/*/skills/*/")
        for skill in skill_files:
            validate_skill_md(skill)

    except ValidationError:
        return 1

    print("\n🎉 All manifests and skills valid.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
