#!/usr/bin/env python3
"""Regenerate skills index and master log.

Runs in-place without modifying skills beyond writing:
- skills_index.json
- skills_index.md
- MASTER_LOG.md (appended)

Detects missing SKILL.md, LICENSE, or instructions folder and reports in outputs.
"""
from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path
import re
import shutil
import os

ROOT = Path(__file__).resolve().parent.parent
INDEX_JSON = ROOT / "skills_index.json"
INDEX_MD = ROOT / "skills_index.md"
MASTER_LOG = ROOT / "MASTER_LOG.md"
INVENTORY_MD = ROOT / "SKILLS_INVENTORY.md"
OUTBOX = ROOT / "OUTBOX"
ARCHIVE = OUTBOX / "archive"
MARKETPLACE_JSON = ROOT / ".claude-plugin" / "marketplace.json"

SKIP_DIRS = {".git", ".claude-plugin", "Delete", "scripts", "_shared", ".INSTRUCTIONS-START-HERE", "OUTBOX"}

REQUIRED_SECTIONS = [
    "[Description]",
    "[requirements]",
    "[Cautions]",
    "[Definitions]",
    "[log]",
    "[model_readme]"
]

def load_marketplace_skills():
    if not MARKETPLACE_JSON.exists():
        return set()
    try:
        data = json.loads(MARKETPLACE_JSON.read_text(encoding="utf-8"))
        skills = set()
        for plugin in data.get("plugins", []):
            for skill_path in plugin.get("skills", []):
                # skill_path is like "./document-skills/xlsx" or "./skill-creator"
                parts = skill_path.strip("./").split("/")
                if len(parts) > 0:
                    # If it's nested like document-skills/xlsx, we might need to handle that.
                    # But based on the directory structure, 'document-skills' is a folder?
                    # Wait, looking at the file list, 'document-skills' is a folder.
                    # But 'skill-creator' is a root folder.
                    # Let's assume the first part of the path is the directory in skills/
                    skills.add(parts[0])
        return skills
    except Exception as e:
        print(f"Warning: Could not load marketplace.json: {e}")
        return set()

def archive_outbox():
    if not OUTBOX.exists():
        OUTBOX.mkdir(exist_ok=True)
    
    if not ARCHIVE.exists():
        ARCHIVE.mkdir(exist_ok=True)

    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    
    for item in OUTBOX.iterdir():
        if item.name == "archive" or item.name.startswith("."):
            continue
        
        if item.is_file():
            new_name = f"{item.stem}_{timestamp}{item.suffix}"
            dest = ARCHIVE / new_name
            try:
                shutil.move(str(item), str(dest))
                print(f"Archived {item.name} to {new_name}")
            except Exception as e:
                print(f"Failed to archive {item.name}: {e}")

def parse_frontmatter(skill_md: Path) -> tuple[str, str]:
    text = skill_md.read_text(encoding="utf-8", errors="replace")
    m = re.match(r"^---\n(.*?)\n---", text, re.DOTALL)
    if not m:
        return "", ""
    fm = m.group(1)
    name = ""
    desc = ""
    for line in fm.splitlines():
        if line.startswith("name:"):
            name = line.split(":", 1)[1].strip()
        if line.startswith("description:"):
            desc = line.split(":", 1)[1].strip()
    return name, desc


def parse_instruction_file(file_path: Path) -> dict:
    content = file_path.read_text(encoding="utf-8", errors="replace")
    sections = {}
    for section in REQUIRED_SECTIONS:
        # Simple check if section header exists
        if section.lower() in content.lower():
            sections[section] = True
            # We could extract content here if needed, but for now just validation
            # Regex to capture content between sections could be complex if order varies
            # Let's just extract the whole file content for the inventory for now
    
    return sections, content

def collect_skills():
    skills = []
    issues = []
    marketplace_skills = load_marketplace_skills()
    
    # Archive outbox first
    archive_outbox()

    for child in sorted(ROOT.iterdir(), key=lambda p: p.name.lower()):
        if not child.is_dir():
            continue
        if child.name in SKIP_DIRS or child.name.startswith("."):
            continue

        skill = {
            "dir": child.name,
            "name": "",
            "description": "",
            "has_skill_md": False,
            "has_license": False,
            "has_instructions": False,
            "instructions_files": [],
            "detailed_sections": {},
            "readme_content": ""
        }

        skill_md = child / "SKILL.md"
        if skill_md.exists():
            skill["has_skill_md"] = True
            n, d = parse_frontmatter(skill_md)
            skill["name"] = n or child.name
            skill["description"] = d
        else:
            issues.append(f"{child.name}: missing SKILL.md")

        lic = None
        for candidate in (child / "LICENSE.txt", child / "LICENSE"):
            if candidate.exists():
                lic = candidate
                break
        if lic:
            skill["has_license"] = True
        else:
            issues.append(f"{child.name}: missing LICENSE")

        instr_dir = child / f"{child.name}_instructions"
        if instr_dir.exists() and instr_dir.is_dir():
            skill["has_instructions"] = True
            numbered = sorted(instr_dir.glob("*"))
            skill["instructions_files"] = [p.name for p in numbered]
            if not numbered:
                issues.append(f"{child.name}: instructions folder present but empty")
            else:
                # Check the first file for required sections if not a marketplace skill
                first_file = numbered[0]
                sections, content = parse_instruction_file(first_file)
                skill["detailed_sections"] = sections
                skill["readme_content"] = content
                
                if child.name not in marketplace_skills:
                    missing_sections = []
                    for req in REQUIRED_SECTIONS:
                        if req not in sections:
                            missing_sections.append(req)
                    
                    if missing_sections:
                        issues.append(f"{child.name}: missing sections in {first_file.name}: {', '.join(missing_sections)}")

        else:
            issues.append(f"{child.name}: missing {child.name}_instructions folder")

        skills.append(skill)
    return skills, issues


def write_json(skills):
    payload = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "skills": skills,
    }
    INDEX_JSON.write_text(json.dumps(payload, indent=2), encoding="utf-8")


def write_md(skills, issues):
    lines = []
    lines.append("# Skills Index (auto-generated)")
    lines.append("")
    lines.append(f"Generated: {datetime.now(timezone.utc).isoformat()}")
    lines.append("")
    lines.append("Run order: 1) run this script before changes 2) make changes 3) run again and review issues.")
    lines.append("")
    lines.append("## Skills (alphabetical)")
    lines.append("")
    lines.append("| dir | name | license | instructions | notes |")
    lines.append("| --- | --- | --- | --- | --- |")
    for s in skills:
        notes = []
        if not s["has_skill_md"]:
            notes.append("missing SKILL.md")
        if not s["has_license"]:
            notes.append("missing LICENSE")
        if not s["has_instructions"]:
            notes.append("missing instructions")
        note_text = "; ".join(notes)
        lines.append(
            f"| {s['dir']} | {s['name'] or ''} | {'yes' if s['has_license'] else 'no'} | {'yes' if s['has_instructions'] else 'no'} | {note_text} |")
    if issues:
        lines.append("")
        lines.append("## Issues")
        lines.append("")
        for item in issues:
            lines.append(f"- {item}")
    INDEX_MD.write_text("\n".join(lines), encoding="utf-8")


def append_log(issues):
    timestamp = datetime.now(timezone.utc).isoformat()
    lines = [f"## Run {timestamp}", ""]
    if issues:
        lines.append("Issues detected:")
        lines.extend([f"- {i}" for i in issues])
    else:
        lines.append("No issues detected.")
    lines.append("")
    with MASTER_LOG.open("a", encoding="utf-8") as f:
        f.write("\n".join(lines))
        f.write("\n")


def write_inventory(skills):
    lines = []
    lines.append("# Skills Inventory")
    lines.append(f"Generated: {datetime.now(timezone.utc).isoformat()}")
    lines.append("")
    
    for s in skills:
        lines.append(f"## {s['name'] or s['dir']}")
        lines.append(f"**Directory**: `{s['dir']}`")
        lines.append(f"**Description**: {s['description']}")
        lines.append(f"**License**: {'Yes' if s['has_license'] else 'No'}")
        lines.append(f"**Instructions**: {len(s['instructions_files'])} files")
        
        if s['detailed_sections']:
            lines.append("\n### Metadata Sections Found")
            for sec, found in s['detailed_sections'].items():
                lines.append(f"- {sec}: {'✅' if found else '❌'}")
        
        if s['readme_content']:
            lines.append("\n### Model Readme Content")
            lines.append("```markdown")
            lines.append(s['readme_content'])
            lines.append("```")
        
        lines.append("\n---\n")

    INVENTORY_MD.write_text("\n".join(lines), encoding="utf-8")

def main():
    skills, issues = collect_skills()
    write_json(skills)
    write_md(skills, issues)
    write_inventory(skills)
    append_log(issues)
    print(f"Indexed {len(skills)} skills. Issues: {len(issues)}.")
    if issues:
        for i in issues:
            print(f"- {i}")


if __name__ == "__main__":
    main()
