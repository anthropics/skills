#!/usr/bin/env python3
"""
generate_wiki.py — Build GitHub Wiki pages from the upstream_skills repository.

Run locally:
    python scripts/generate_wiki.py

Environment variables:
    WIKI_OUTPUT_DIR   Directory where generated wiki files are written.
                      Defaults to <repo_root>/wiki_output.

The script:
  1. Scans skills/ for every subfolder that contains a SKILL.md.
  2. Parses each SKILL.md (YAML front-matter + markdown body).
  3. Generates dynamic pages:
       Home.md              — landing page with live skill statistics
       Skills-Overview.md   — table of all skills, auto-updated per run
       Skill-<name>.md      — one dedicated page per skill (new skills appear
                              automatically without any manual edits)
       _Sidebar.md          — GitHub wiki navigation sidebar
       _Footer.md           — GitHub wiki footer
  4. Copies static source pages from wiki/ into the output directory.

To add a new skill, drop a folder with a SKILL.md under skills/ and push.
The GitHub Actions workflow will pick it up on the next run.
"""

from __future__ import annotations

import os
import re
import shutil
from datetime import datetime, timezone
from pathlib import Path
from typing import NamedTuple

# ── Constants ─────────────────────────────────────────────────────────────────

REPO_ROOT = Path(__file__).parent.parent
SKILLS_DIR = REPO_ROOT / "skills"
STATIC_WIKI_DIR = REPO_ROOT / "wiki"
OUTPUT_DIR = Path(os.environ.get("WIKI_OUTPUT_DIR", str(REPO_ROOT / "wiki_output")))

REPO_URL = "https://github.com/d33disc/upstream_skills"
SKILLS_URL = f"{REPO_URL}/tree/main/skills"

# ── Skill categorisation ──────────────────────────────────────────────────────
# Map skill folder names → display category.
# Unknown / future skills fall into "Other" automatically.

SKILL_CATEGORIES: dict[str, str] = {
    "algorithmic-art": "Creative & Design",
    "brand-guidelines": "Creative & Design",
    "canvas-design": "Creative & Design",
    "frontend-design": "Creative & Design",
    "slack-gif-creator": "Creative & Design",
    "theme-factory": "Creative & Design",
    "claude-api": "Development & Technical",
    "mcp-builder": "Development & Technical",
    "web-artifacts-builder": "Development & Technical",
    "webapp-testing": "Development & Technical",
    "doc-coauthoring": "Enterprise & Communication",
    "internal-comms": "Enterprise & Communication",
    "skill-creator": "Enterprise & Communication",
    "docx": "Document Skills",
    "pdf": "Document Skills",
    "pptx": "Document Skills",
    "xlsx": "Document Skills",
}

CATEGORY_ICONS: dict[str, str] = {
    "Creative & Design": "🎨",
    "Development & Technical": "⚙️",
    "Enterprise & Communication": "🏢",
    "Document Skills": "📄",
    "Other": "🔧",
}

# Controls the order categories appear on every page.
CATEGORY_ORDER: list[str] = [
    "Creative & Design",
    "Development & Technical",
    "Enterprise & Communication",
    "Document Skills",
    "Other",
]


# ── Data model ────────────────────────────────────────────────────────────────

class Skill(NamedTuple):
    folder: str       # e.g. "algorithmic-art"
    name: str         # from frontmatter
    description: str  # from frontmatter
    license: str      # from frontmatter
    body: str         # full markdown body of SKILL.md
    files: list[str]  # relative paths of every file inside the skill folder
    category: str


# ── SKILL.md parsing ──────────────────────────────────────────────────────────

def _extract_yaml_field(fm_text: str, field: str) -> str:
    """Return the value of *field* from a block of YAML-like text."""
    # Double-quoted value — may span many characters on a single YAML line.
    m = re.search(
        rf'^{re.escape(field)}:\s*"((?:[^"\\]|\\.)*)"',
        fm_text,
        re.MULTILINE | re.DOTALL,
    )
    if m:
        return re.sub(r"\s+", " ", m.group(1)).strip()

    # Single-quoted value.
    m = re.search(
        rf"^{re.escape(field)}:\s*'((?:[^'\\]|\\.)*)'",
        fm_text,
        re.MULTILINE | re.DOTALL,
    )
    if m:
        return re.sub(r"\s+", " ", m.group(1)).strip()

    # Unquoted single-line value.
    m = re.search(rf"^{re.escape(field)}:\s*(.+)$", fm_text, re.MULTILINE)
    if m:
        return m.group(1).strip()

    return ""


def parse_frontmatter(content: str) -> tuple[dict[str, str], str]:
    """Return ``(frontmatter_dict, body_text)`` from the raw SKILL.md text."""
    if not content.startswith("---"):
        return {}, content

    rest = content[3:]
    close_idx = rest.find("\n---")
    if close_idx == -1:
        return {}, content

    fm_text = rest[:close_idx]
    body = rest[close_idx + 4:].lstrip("\n")

    return {
        "name": _extract_yaml_field(fm_text, "name"),
        "description": _extract_yaml_field(fm_text, "description"),
        "license": _extract_yaml_field(fm_text, "license"),
    }, body


# ── File discovery ────────────────────────────────────────────────────────────

def list_skill_files(skill_dir: Path) -> list[str]:
    """Return a sorted list of all file paths relative to *skill_dir*."""
    return sorted(
        str(p.relative_to(skill_dir))
        for p in skill_dir.rglob("*")
        if p.is_file()
    )


# ── File-description heuristics ───────────────────────────────────────────────

_EXACT_FILE_DESCRIPTIONS: dict[str, str] = {
    "SKILL.md": "Skill definition, YAML metadata, and Claude instructions",
    "LICENSE.txt": "License terms for this skill",
    "README.md": "Additional documentation",
}

_PATTERN_FILE_DESCRIPTIONS: list[tuple[str, str]] = [
    (r"scripts/office/", "Office document utility (LibreOffice integration)"),
    (r"scripts/.*\.py$", "Python utility script"),
    (r"scripts/.*\.sh$", "Shell script"),
    (r"reference/.*\.md$", "Reference documentation"),
    (r"examples/.*\.py$", "Example Python automation"),
    (r"examples/.*\.md$", "Example or template document"),
    (r"templates/.*\.html$", "HTML template"),
    (r"templates/.*\.js$", "JavaScript template"),
    (r"templates/.*\.md$", "Markdown template"),
    (r"themes/", "Pre-defined theme configuration"),
    (r"agents/", "Sub-agent definition"),
    (r"assets/", "Asset file"),
    (r"core/.*\.py$", "Core library module"),
    (r"eval-viewer/", "Evaluation viewer component"),
    (r"references/", "Reference material"),
    (r"\.ttf$", "TrueType font"),
    (r"\.otf$", "OpenType font"),
    (r"\.pdf$", "PDF document"),
    (r"\.xml$", "XML configuration or example"),
    (r"\.json$", "JSON configuration"),
    (r"-fonts/", "Font asset"),
]


def describe_file(rel_path: str) -> str:
    """Return a short human-readable description for a file inside a skill."""
    if rel_path in _EXACT_FILE_DESCRIPTIONS:
        return _EXACT_FILE_DESCRIPTIONS[rel_path]
    for pattern, desc in _PATTERN_FILE_DESCRIPTIONS:
        if re.search(pattern, rel_path, re.IGNORECASE):
            return desc
    return "Supporting file"


# ── Skill loading ─────────────────────────────────────────────────────────────

def load_skills() -> list[Skill]:
    """Discover, parse, and return all skills found under ``SKILLS_DIR``."""
    skills: list[Skill] = []
    for skill_dir in sorted(SKILLS_DIR.iterdir()):
        if not skill_dir.is_dir():
            continue
        skill_md = skill_dir / "SKILL.md"
        if not skill_md.exists():
            continue

        content = skill_md.read_text(encoding="utf-8")
        fm, body = parse_frontmatter(content)
        folder = skill_dir.name

        skills.append(
            Skill(
                folder=folder,
                name=fm.get("name") or folder,
                description=fm.get("description", ""),
                license=fm.get("license", ""),
                body=body,
                files=list_skill_files(skill_dir),
                category=SKILL_CATEGORIES.get(folder, "Other"),
            )
        )
    return skills


# ── Page generators ───────────────────────────────────────────────────────────

def _skill_wiki_link(skill: Skill) -> str:
    """Return a GitHub-wiki markdown link to a skill's dedicated page."""
    title = skill.folder.replace("-", " ").title()
    return f"[{title}](Skill-{skill.folder})"


def _by_category(skills: list[Skill]) -> dict[str, list[Skill]]:
    result: dict[str, list[Skill]] = {}
    for s in skills:
        result.setdefault(s.category, []).append(s)
    return result


def generate_home(skills: list[Skill], timestamp: str) -> str:
    """Generate ``Home.md`` — the wiki landing page."""
    by_cat = _by_category(skills)
    total = len(skills)

    lines: list[str] = [
        "# 🛠️ upstream_skills Wiki",
        "",
        "> **Anthropic's official reference implementation for Claude Agent Skills.**",
        "",
        f"**{total} skill{'s' if total != 1 else ''}** · "
        f"**Last updated: {timestamp}** · "
        f"[View on GitHub]({REPO_URL})",
        "",
        "---",
        "",
        "## What Is This Repository?",
        "",
        "This repository contains Anthropic's implementation of **Agent Skills** for Claude — "
        "a system that lets Claude dynamically load specialised instructions, scripts, and "
        "resources to improve performance on specific tasks.",
        "",
        "Skills teach Claude how to complete tasks in a repeatable, reliable way: "
        "creating Word documents with brand guidelines, generating generative art, "
        "building MCP servers, automating web testing, and much more.",
        "",
        "> **Disclaimer:** Skills are provided for demonstration and educational purposes. "
        "While some capabilities may be available in Claude, implementations may differ from "
        "these reference skills. Always test in your own environment before relying on them "
        "for critical tasks.",
        "",
        "---",
        "",
        "## 🗺️ Wiki Navigation",
        "",
        "| Page | Description |",
        "|------|-------------|",
        "| [Skills Overview](Skills-Overview) | Full table of every skill with descriptions and license info |",
        "| [Getting Started](Getting-Started) | How to install and activate skills in Claude Code, Claude.ai, and the API |",
        "| [Architecture](Architecture) | How skills work, `SKILL.md` format, script conventions, and plugin groups |",
        "| [Contributing](Contributing) | Step-by-step guide to authoring and submitting new skills |",
        "",
        "---",
        "",
        "## 🔍 Skills at a Glance",
        "",
    ]

    for cat in CATEGORY_ORDER:
        cat_skills = by_cat.get(cat, [])
        if not cat_skills:
            continue
        icon = CATEGORY_ICONS.get(cat, "🔧")
        plural = "s" if len(cat_skills) != 1 else ""
        lines += [
            f"### {icon} {cat} ({len(cat_skills)} skill{plural})",
            "",
            "| Skill | Summary |",
            "|-------|---------|",
        ]
        for s in cat_skills:
            summary = s.description.split(".")[0].rstrip() if s.description else "—"
            if len(summary) > 130:
                summary = summary[:127] + "…"
            lines.append(f"| {_skill_wiki_link(s)} | {summary} |")
        lines.append("")

    lines += [
        "---",
        "",
        "## ⚡ Quick Start",
        "",
        "### Claude Code",
        "",
        "```",
        "/plugin marketplace add anthropics/skills",
        "/plugin install document-skills@anthropic-agent-skills",
        "/plugin install example-skills@anthropic-agent-skills",
        "```",
        "",
        "Once installed, simply ask Claude to use a skill by mentioning it — e.g. "
        "*\"Use the PDF skill to extract the form fields from my-file.pdf\"*.",
        "",
        "### Claude.ai",
        "",
        "All skills in this repository are already available to paid Claude.ai plans. "
        "See [Using skills in Claude](https://support.claude.com/en/articles/12512180-using-skills-in-claude).",
        "",
        "### Claude API",
        "",
        "Use Anthropic's pre-built skills or upload custom ones via the API. "
        "See the [Skills API Quickstart](https://docs.claude.com/en/api/skills-guide#creating-a-skill).",
        "",
        "---",
        "",
        "## 📚 External Resources",
        "",
        "- [What are skills?](https://support.claude.com/en/articles/12512176-what-are-skills)",
        "- [Using skills in Claude](https://support.claude.com/en/articles/12512180-using-skills-in-claude)",
        "- [Creating custom skills](https://support.claude.com/en/articles/12512198-creating-custom-skills)",
        "- [Agent Skills specification](https://agentskills.io/specification)",
        "- [Engineering blog post](https://anthropic.com/engineering/equipping-agents-for-the-real-world-with-agent-skills)",
        "",
        "---",
        "",
        f"*This wiki is automatically generated from the repository source. "
        f"Last updated: {timestamp}.*",
    ]
    return "\n".join(lines)


def generate_skills_overview(skills: list[Skill], timestamp: str) -> str:
    """Generate ``Skills-Overview.md`` — sortable table of all skills."""
    by_cat = _by_category(skills)

    lines: list[str] = [
        "# 📚 Skills Overview",
        "",
        f"This page lists all **{len(skills)} skill{'s' if len(skills) != 1 else ''}** "
        "in the repository, organised by category. "
        "Click any skill name for its full documentation page.",
        "",
        f"*Auto-generated · Last updated: {timestamp}*",
        "",
        "---",
        "",
    ]

    for cat in CATEGORY_ORDER:
        cat_skills = by_cat.get(cat, [])
        if not cat_skills:
            continue
        icon = CATEGORY_ICONS.get(cat, "🔧")
        lines += [
            f"## {icon} {cat}",
            "",
            "| Skill | Description | License | Source |",
            "|-------|-------------|---------|--------|",
        ]
        for s in cat_skills:
            desc = s.description or "—"
            if len(desc) > 200:
                desc = desc[:197] + "…"
            lic = s.license or "Apache 2.0"
            source = f"[`skills/{s.folder}`]({SKILLS_URL}/{s.folder})"
            lines.append(f"| {_skill_wiki_link(s)} | {desc} | {lic} | {source} |")
        lines.append("")

    lines += [
        "---",
        "",
        "## Plugin Groups",
        "",
        "Skills can be installed as a group via Claude Code plugins:",
        "",
        "| Plugin name | Skills included |",
        "|-------------|-----------------|",
        "| `document-skills` | docx, pdf, pptx, xlsx |",
        "| `example-skills` | algorithmic-art, brand-guidelines, canvas-design, "
        "doc-coauthoring, frontend-design, internal-comms, mcp-builder, "
        "skill-creator, slack-gif-creator, theme-factory, web-artifacts-builder, webapp-testing |",
        "| `claude-api` | claude-api |",
        "",
        "```",
        "/plugin marketplace add anthropics/skills",
        "/plugin install document-skills@anthropic-agent-skills",
        "/plugin install example-skills@anthropic-agent-skills",
        "```",
    ]
    return "\n".join(lines)


def generate_skill_page(skill: Skill) -> str:
    """Generate ``Skill-<name>.md`` — the dedicated wiki page for one skill."""
    icon = CATEGORY_ICONS.get(skill.category, "🔧")
    title = skill.folder.replace("-", " ").title()

    lines: list[str] = [
        f"# {icon} {title}",
        "",
        f"> **Category:** {skill.category}",
        f"> **Folder:** [`skills/{skill.folder}`]({SKILLS_URL}/{skill.folder})",
    ]
    if skill.license:
        lines.append(f"> **License:** {skill.license}")
    lines += ["", "---", ""]

    # When to use
    lines += [
        "## When to Use This Skill",
        "",
        skill.description if skill.description else "*No trigger description provided.*",
        "",
        "---",
        "",
    ]

    # Files table
    lines += [
        "## Files in This Skill",
        "",
        "| File | Description |",
        "|------|-------------|",
    ]
    for f in skill.files:
        lines.append(f"| `{f}` | {describe_file(f)} |")
    lines += ["", "---", ""]

    # Full instructions from SKILL.md body
    if skill.body.strip():
        lines += [
            "## Instructions",
            "",
            skill.body.rstrip(),
            "",
            "---",
            "",
        ]

    # Related pages
    lines += [
        "## See Also",
        "",
        "- [Skills Overview](Skills-Overview) — full list of all skills",
        "- [Getting Started](Getting-Started) — how to install and use skills",
        "- [Architecture](Architecture) — how skills are structured",
        "- [Contributing](Contributing) — how to create your own skills",
    ]
    return "\n".join(lines)


def generate_sidebar(skills: list[Skill]) -> str:
    """Generate ``_Sidebar.md`` — GitHub wiki navigation sidebar."""
    by_cat = _by_category(skills)

    lines: list[str] = [
        "**🏠 [Home](Home)**",
        "",
        "**📚 [Skills Overview](Skills-Overview)**",
        "",
        "---",
        "",
        "**📖 Documentation**",
        "",
        "- [Getting Started](Getting-Started)",
        "- [Architecture](Architecture)",
        "- [Contributing](Contributing)",
        "",
        "---",
        "",
    ]

    for cat in CATEGORY_ORDER:
        cat_skills = by_cat.get(cat, [])
        if not cat_skills:
            continue
        icon = CATEGORY_ICONS.get(cat, "🔧")
        lines += [f"**{icon} {cat}**", ""]
        for s in cat_skills:
            title = s.folder.replace("-", " ").title()
            lines.append(f"- [{title}](Skill-{s.folder})")
        lines.append("")

    return "\n".join(lines)


def generate_footer(timestamp: str) -> str:
    """Generate ``_Footer.md`` — GitHub wiki footer."""
    return (
        f"---\n\n"
        f"*Wiki auto-generated from [{REPO_URL}]({REPO_URL}). "
        f"Last updated: {timestamp}.*"
    )


# ── Entry point ───────────────────────────────────────────────────────────────

def main() -> None:
    timestamp = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")

    print(f"Output directory : {OUTPUT_DIR}")
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    print("Scanning skills/ …")
    skills = load_skills()
    print(f"Found {len(skills)} skill(s): {', '.join(s.folder for s in skills)}")

    # Dynamic pages — regenerated on every run
    dynamic_pages: dict[str, str] = {
        "Home.md": generate_home(skills, timestamp),
        "Skills-Overview.md": generate_skills_overview(skills, timestamp),
        "_Sidebar.md": generate_sidebar(skills),
        "_Footer.md": generate_footer(timestamp),
    }
    for skill in skills:
        dynamic_pages[f"Skill-{skill.folder}.md"] = generate_skill_page(skill)

    for filename, content in sorted(dynamic_pages.items()):
        (OUTPUT_DIR / filename).write_text(content, encoding="utf-8")
        print(f"  generated : {filename}")

    # Static pages — authored in wiki/ and copied as-is
    if STATIC_WIKI_DIR.exists():
        for src in sorted(STATIC_WIKI_DIR.iterdir()):
            if src.is_file() and src.suffix == ".md":
                dest = OUTPUT_DIR / src.name
                shutil.copy2(src, dest)
                print(f"  copied    : {src.name}")

    total_pages = len(dynamic_pages) + sum(
        1 for f in STATIC_WIKI_DIR.iterdir()
        if STATIC_WIKI_DIR.exists() and f.is_file() and f.suffix == ".md"
    )
    print(f"\n✅  Done — {total_pages} wiki pages written to {OUTPUT_DIR}")


if __name__ == "__main__":
    main()
