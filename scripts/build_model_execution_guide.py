#!/usr/bin/env python3
"""
Extract model_readme sections from all skills and build execution guide JSON.

Reads section 6 [model_readme] from each skill's first instruction file
and creates a JSON file that models can use to understand how to execute each skill.

Outputs:
- Model_Execution_Guide.json (focused execution instructions for models)
"""

import json
import re
from datetime import datetime
from pathlib import Path
from typing import Dict, List

ROOT = Path(__file__).resolve().parent.parent
MODEL_GUIDE_JSON = ROOT / "Model_Execution_Guide.json"
SKILL_INDEX_JSON = ROOT / "Skill_Index.json"

SKIP_DIRS = {".git", ".claude-plugin", "Delete", "scripts", "_shared", 
             ".INSTRUCTIONS-START-HERE", "OUTBOX", ".OUTPUT", "PIMP-SMACK-APP",
             "macros", "_archive"}

ANTHROPIC_SKILLS = {"algorithmic-art", "artifacts-builder", "brand-guidelines", 
                    "canvas-design", "internal-comms", "mcp-builder", 
                    "skill-creator", "slack-gif-creator", "template-skill", 
                    "theme-factory", "webapp-testing"}


def extract_model_readme(file_path: Path) -> str:
    """Extract the [model_readme] section (section 6) from instruction file."""
    if not file_path.exists():
        return ""
    
    try:
        content = file_path.read_text(encoding='utf-8', errors='replace')
        
        # Pattern for section 6
        pattern = r'6\.\s*\[model_readme\](.*?)(?:\n\d+\.\s*\[|```\s*$|$)'
        match = re.search(pattern, content, re.DOTALL | re.IGNORECASE)
        
        if match:
            readme = match.group(1).strip()
            # Remove trailing markdown code fence if present
            readme = re.sub(r'```\s*$', '', readme).strip()
            return readme
        return ""
    except Exception as e:
        print(f"Error reading {file_path}: {e}")
        return ""


def parse_skill_md_frontmatter(skill_md: Path) -> tuple[str, str]:
    """Extract name and description from SKILL.md frontmatter."""
    if not skill_md.exists():
        return "", ""
    
    text = skill_md.read_text(encoding='utf-8', errors='replace')
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
            desc = line.split(":", 1)[1].strip().strip('"')
    return name, desc


def build_model_guide():
    """Build execution guide JSON for models."""
    print("=== Model Execution Guide Builder ===\n")
    
    skills_data = []
    
    for skill_dir in sorted(ROOT.iterdir()):
        if not skill_dir.is_dir():
            continue
        if skill_dir.name in SKIP_DIRS or skill_dir.name.startswith('.'):
            continue
        
        skill_name = skill_dir.name
        print(f"Processing: {skill_name}")
        
        # Get SKILL.md info
        skill_md = skill_dir / "SKILL.md"
        name, description = parse_skill_md_frontmatter(skill_md)
        
        # Find first instruction file
        instr_dir = skill_dir / f"{skill_name}_instructions"
        first_instr_file = None
        model_readme = ""
        
        if instr_dir.exists():
            numbered_files = sorted([f for f in instr_dir.iterdir() 
                                    if f.is_file() and f.name[0].isdigit()])
            if numbered_files:
                first_instr_file = numbered_files[0]
                model_readme = extract_model_readme(first_instr_file)
        
        # Build skill entry
        skill_data = {
            "skill_name": skill_name,
            "display_name": name or skill_name,
            "description": description,
            "is_anthropic_skill": skill_name in ANTHROPIC_SKILLS,
            "has_execution_instructions": bool(model_readme),
            "model_readme": model_readme,
            "instruction_file": first_instr_file.name if first_instr_file else None
        }
        
        skills_data.append(skill_data)
    
    # Build final JSON
    guide = {
        "generated_at": datetime.now().isoformat(),
        "total_skills": len(skills_data),
        "skills_with_instructions": sum(1 for s in skills_data if s["has_execution_instructions"]),
        "anthropic_skills": sum(1 for s in skills_data if s["is_anthropic_skill"]),
        "custom_skills": sum(1 for s in skills_data if not s["is_anthropic_skill"]),
        "skills": skills_data
    }
    
    # Write JSON
    MODEL_GUIDE_JSON.write_text(json.dumps(guide, indent=2), encoding='utf-8')
    
    # Print summary
    print(f"\n=== Summary ===")
    print(f"Total skills: {guide['total_skills']}")
    print(f"With execution instructions: {guide['skills_with_instructions']}")
    print(f"Anthropic skills: {guide['anthropic_skills']}")
    print(f"Custom skills: {guide['custom_skills']}")
    print(f"\nOutput written: {MODEL_GUIDE_JSON}")
    
    # Show skills without instructions
    no_instructions = [s for s in skills_data if not s["has_execution_instructions"]]
    if no_instructions:
        print(f"\nSkills without model_readme:")
        for s in no_instructions:
            print(f"  - {s['skill_name']}")


if __name__ == "__main__":
    build_model_guide()
