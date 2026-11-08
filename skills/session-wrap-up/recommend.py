#!/usr/bin/env python3
"""
Session wrap-up recommender — reads the Claude Code plugin registry,
installed list, install counts, and local skills directory, then outputs
recommendations based on session activity keywords.

Usage:
    python3 recommend.py <activity_keywords...>
    e.g. python3 recommend.py coding git debugging frontend

Output: JSON with recommended_new (uninstalled) and reminder_installed (already have).
"""

import json
import os
import sys
from pathlib import Path

PLUGINS_DIR = Path.home() / ".claude" / "plugins"
SKILLS_DIR = Path.home() / ".claude" / "skills"
MARKETPLACE = (
    PLUGINS_DIR
    / "marketplaces"
    / "claude-plugins-official"
    / ".claude-plugin"
    / "marketplace.json"
)
INSTALLED = PLUGINS_DIR / "installed_plugins.json"
COUNTS = PLUGINS_DIR / "install-counts-cache.json"

# Activity → candidate plugin/skill names
ACTIVITY_MAP = {
    "coding": ["code-review", "code-simplifier", "security-guidance", "superpowers"],
    "frontend": ["frontend-design", "playwright", "figma", "stagehand"],
    "debugging": ["explanatory-output-style", "sentry"],
    "git": ["commit-commands", "github", "pr-review-toolkit"],
    "api": ["postman", "context7", "firecrawl"],
    "data": ["firecrawl"],
    "deploy": ["vercel", "firebase"],
    "project": ["linear", "asana", "atlassian"],
    "docs": ["claude-md-management", "context7"],
    "skill_dev": ["skill-creator", "plugin-dev", "hookify"],
    "security": ["security-guidance", "semgrep"],
    "testing": ["playwright"],
    "python": ["pyright-lsp"],
    "typescript": ["typescript-lsp"],
}


def load_json(path: Path):
    """Load a JSON file, returning None on any error."""
    try:
        with open(path) as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError, PermissionError):
        return None


def get_installed_set(data):
    """Extract the set of installed plugin keys."""
    if not data or "plugins" not in data:
        return set()
    return set(data["plugins"].keys())


def get_install_counts(data):
    """Build a dict of plugin_key -> install count."""
    if not data or "counts" not in data:
        return {}
    return {item["plugin"]: item["unique_installs"] for item in data["counts"]}


def get_marketplace_descriptions(data):
    """Build a dict of plugin_name -> description."""
    if not data or "plugins" not in data:
        return {}
    return {p["name"]: p.get("description", "") for p in data["plugins"]}


def get_local_skills():
    """List local skill directory names that contain a SKILL.md."""
    skills = []
    if not SKILLS_DIR.exists():
        return skills
    for d in SKILLS_DIR.iterdir():
        if d.is_dir() and (d / "SKILL.md").exists():
            skills.append(d.name)
    return skills


def normalize_plugin_key(name: str) -> str:
    """Convert 'code-review' to 'code-review@claude-plugins-official'."""
    if "@" in name:
        return name
    return f"{name}@claude-plugins-official"


def recommend(activities: list[str]) -> dict:
    """Generate recommendations based on activity keywords."""
    installed_data = load_json(INSTALLED)
    counts_data = load_json(COUNTS)
    marketplace_data = load_json(MARKETPLACE)

    installed_set = get_installed_set(installed_data)
    install_counts = get_install_counts(counts_data)
    descriptions = get_marketplace_descriptions(marketplace_data)
    local_skills = get_local_skills()

    # Collect candidate names from activities
    candidates = set()
    for act in activities:
        act_lower = act.lower()
        for key, plugins in ACTIVITY_MAP.items():
            if act_lower in key or key in act_lower:
                candidates.update(plugins)

    # Classify: new vs already installed
    recommended_new = []
    reminder_installed = []

    for name in candidates:
        full_key = normalize_plugin_key(name)
        is_installed = full_key in installed_set or any(
            full_key.lower() == k.lower() for k in installed_set
        )
        is_local = name in local_skills
        count = install_counts.get(full_key, 0)
        desc = descriptions.get(name, "")

        entry = {
            "name": name,
            "description": desc,
            "installs": count,
            "source": "local_skill" if is_local else "official_plugin",
            "install_cmd": (
                f"claude plugin install {full_key}"
                if not is_local
                else f"/{name}"
            ),
        }

        if is_installed or is_local:
            reminder_installed.append(entry)
        else:
            recommended_new.append(entry)

    # Sort by install count descending
    recommended_new.sort(key=lambda x: -x["installs"])
    reminder_installed.sort(key=lambda x: -x["installs"])

    return {
        "recommended_new": recommended_new[:3],
        "reminder_installed": reminder_installed[:2],
    }


if __name__ == "__main__":
    activities = sys.argv[1:] if len(sys.argv) > 1 else ["coding"]
    result = recommend(activities)
    print(json.dumps(result, indent=2, ensure_ascii=False))
