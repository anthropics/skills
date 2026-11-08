#!/usr/bin/env python3
"""Enhanced skills index builder with validation and diff tracking.

Generates:
- Skill_Index.json (extracted 6-section metadata)
- MASTER_LOG.csv (timestamped validation logs)
- Validates 4-item structure per skill
"""

import json
import csv
import re
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Tuple

ROOT = Path(__file__).resolve().parent.parent
OUTPUT_DIR = ROOT / ".OUTPUT"
SKILL_INDEX_JSON = ROOT / ".Skill_Index.json"
MASTER_LOG_CSV = ROOT / ".MASTER_LOG.csv"
DELETE_DIR = ROOT / "Delete"
DEFINITIONS_FILE = Path(__file__).parent / ".SKILL_INDEX_DEFINITIONS.md"

SKIP_DIRS = {".git", ".claude-plugin", "Delete", "scripts", "_shared", 
             ".INSTRUCTIONS-START-HERE", "OUTBOX", ".OUTPUT", "PIMP-SMACK-APP",
             "macros", "_archive", "INPUT"}

ANTHROPIC_SKILLS = {"algorithmic-art", "artifacts-builder", "brand-guidelines", 
                    "canvas-design", "internal-comms", "mcp-builder", 
                    "skill-creator", "slack-gif-creator", "template-skill", 
                    "theme-factory", "webapp-testing"}

REQUIRED_SECTIONS = {
    "Description": r"1\.\s*\[Description\]",
    "requirements": r"2\.\s*\[requirements\]",
    "Cautions": r"3\.\s*\[Cautions\]",
    "Definitions": r"4\.\s*\[Definitions\]",
    "log": r"5\.\s*\[log\]",
    "model_readme": r"6\.\s*\[model_readme\]"
}


def init_master_log():
    """Initialize MASTER_LOG.csv if it doesn't exist."""
    if not MASTER_LOG_CSV.exists():
        with open(MASTER_LOG_CSV, 'w', newline='', encoding='utf-8') as f:
            writer = csv.writer(f, delimiter='|')
            writer.writerow([
                'TIMESTAMP', 'CHECK OR RUN', 'STATUS', 'CHANGES SINCE LAST RUN',
                'SKILL WORKED ON', 'MODEL RUNNING', 'MODEL READ INSTRUCTIONS/CLEAN FILES',
                'CHECK IN OR OUT', 'NOTE'
            ])


def log_to_master(check_or_run: str, status: str, changes: str, skill: str, 
                  model: str, clean_files: str, check_in_out: str, note: str):
    """Append a row to MASTER_LOG.csv."""
    init_master_log()
    with open(MASTER_LOG_CSV, 'a', newline='', encoding='utf-8') as f:
        writer = csv.writer(f, delimiter='|')
        writer.writerow([
            datetime.now().isoformat(),
            check_or_run,
            status,
            changes,
            skill,
            model,
            clean_files,
            check_in_out,
            note
        ])


def extract_section_content(text: str, section_name: str) -> str:
    """Extract content from a numbered section."""
    pattern = REQUIRED_SECTIONS.get(section_name)
    if not pattern:
        return ""
    
    match = re.search(pattern, text, re.IGNORECASE)
    if not match:
        return ""
    
    start = match.end()
    # Find next numbered section or end of file
    next_section = re.search(r'\n\d+\.\s*\[', text[start:])
    end = start + next_section.start() if next_section else len(text)
    
    content = text[start:end].strip()
    return content


def parse_first_instruction_file(file_path: Path) -> Dict:
    """Parse the 6-section template from first instruction file."""
    if not file_path.exists():
        return {}
    
    try:
        content = file_path.read_text(encoding='utf-8', errors='replace')
        
        sections = {}
        for section_name in REQUIRED_SECTIONS.keys():
            sections[section_name] = extract_section_content(content, section_name)
        
        return sections
    except Exception as e:
        print(f"Error parsing {file_path}: {e}")
        return {}


def validate_skill_structure(skill_dir: Path) -> Tuple[bool, List[str]]:
    """Validate that skill has exactly 4 items and proper structure."""
    issues = []
    
    # Skip Anthropic skills
    if skill_dir.name in ANTHROPIC_SKILLS:
        return True, []
    
    # Count items in skill root (should be exactly 4 + optional _examples)
    items = [item for item in skill_dir.iterdir() 
             if not item.name.startswith('.')]
    
    required_items = {
        "SKILL.md": False,
        "LICENSE": False,
        f"{skill_dir.name}_instructions": False,
        f"{skill_dir.name}_example": False
    }
    
    # Allowed optional items
    optional_items = {"_examples", "scripts", ".outbox", "4-scripts", "5-templates", 
                     "6-references", "7-references", "8-templates", "9-brief_data",
                     "3-styles.json", "filing_config.json"}
    
    for item in items:
        if item.name == "SKILL.md":
            required_items["SKILL.md"] = True
        elif item.name in ["LICENSE.txt", "LICENSE"]:
            required_items["LICENSE"] = True
        elif item.name == f"{skill_dir.name}_instructions" and item.is_dir():
            required_items[f"{skill_dir.name}_instructions"] = True
        elif item.name == f"{skill_dir.name}_example" and item.is_dir():
            required_items[f"{skill_dir.name}_example"] = True
        elif item.name not in optional_items:
            # Loose file found (not required, not optional)
            issues.append(f"Loose item found: {item.name}")
    
    # Check for missing required items
    for req_item, found in required_items.items():
        if not found:
            issues.append(f"Missing required: {req_item}")
    
    return len(issues) == 0, issues


def collect_skill_metadata(skill_dir: Path) -> Dict:
    """Collect metadata from a skill directory."""
    skill_name = skill_dir.name
    
    # Parse SKILL.md frontmatter for "uses"
    skill_md = skill_dir / "SKILL.md"
    uses = ""
    if skill_md.exists():
        content = skill_md.read_text(encoding='utf-8', errors='replace')
        fm_match = re.search(r'^---\n(.*?)\n---', content, re.DOTALL | re.MULTILINE)
        if fm_match:
            for line in fm_match.group(1).splitlines():
                if line.startswith("description:"):
                    uses = line.split(":", 1)[1].strip().strip('"')
    
    # Find first instruction file
    instr_dir = skill_dir / f"{skill_name}_instructions"
    first_instr_file = None
    if instr_dir.exists():
        numbered_files = sorted([f for f in instr_dir.iterdir() 
                                if f.is_file() and f.name[0].isdigit()])
        if numbered_files:
            first_instr_file = numbered_files[0]
    
    # Extract 6-section template
    sections = {}
    if first_instr_file:
        sections = parse_first_instruction_file(first_instr_file)
    
    # Validate structure
    valid, issues = validate_skill_structure(skill_dir)
    
    return {
        "skill_name": skill_name,
        "uses": uses,
        "description": sections.get("Description", ""),
        "requirements": sections.get("requirements", ""),
        "cautions": sections.get("Cautions", ""),
        "definitions": sections.get("Definitions", ""),
        "log": sections.get("log", ""),
        "model_readme": sections.get("model_readme", ""),
        "stackable_with": [],  # User can populate later
        "_valid_structure": valid,  # Internal use only
        "_structure_issues": issues  # Internal use only
    }


def calculate_diff(previous: Dict, current: Dict) -> List[str]:
    """Calculate differences between previous and current index."""
    changes = []
    
    if not previous:
        return ["First run - no previous index"]
    
    prev_skills = {s["skill_name"] for s in previous.get("skills", [])}
    curr_skills = {s["skill_name"] for s in current.get("skills", [])}
    
    new_skills = curr_skills - prev_skills
    removed_skills = prev_skills - curr_skills
    
    if new_skills:
        changes.append(f"New skills: {', '.join(new_skills)}")
    if removed_skills:
        changes.append(f"Removed skills: {', '.join(removed_skills)}")
    
    # Check for changes in existing skills
    for curr_skill in current.get("skills", []):
        skill_name = curr_skill["skill_name"]
        prev_skill = next((s for s in previous.get("skills", []) 
                          if s["skill_name"] == skill_name), None)
        if prev_skill:
            if curr_skill.get("sections") != prev_skill.get("sections"):
                changes.append(f"{skill_name}: sections changed")
            if curr_skill.get("structure_issues") != prev_skill.get("structure_issues"):
                changes.append(f"{skill_name}: structure changed")
    
    return changes if changes else ["No changes detected"]


def main():
    """Main execution."""
    print("=== Enhanced Skills Index Builder ===\n")
    
    # Collect all skills
    valid_skills = []
    broken_skills = []
    total_issues = []
    
    for skill_dir in sorted(ROOT.iterdir()):
        if not skill_dir.is_dir():
            continue
        if skill_dir.name in SKIP_DIRS or skill_dir.name.startswith('.'):
            continue
        
        print(f"Processing: {skill_dir.name}")
        metadata = collect_skill_metadata(skill_dir)
        
        # Separate valid from broken
        if metadata.get("_valid_structure"):
            # Clean metadata before adding to index
            clean_metadata = {
                "skill_name": metadata["skill_name"],
                "uses": metadata["uses"],
                "description": metadata["description"],
                "requirements": metadata["requirements"],
                "cautions": metadata["cautions"],
                "definitions": metadata["definitions"],
                "log": metadata["log"],
                "model_readme": metadata["model_readme"],
                "stackable_with": metadata["stackable_with"]
            }
            valid_skills.append(clean_metadata)
        else:
            broken_skills.append({
                "skill_name": metadata["skill_name"],
                "uses": metadata["uses"],
                "issues": metadata["_structure_issues"]
            })
        
        if not metadata["_valid_structure"]:
            total_issues.extend([f"{skill_dir.name}: {issue}" 
                                for issue in metadata["_structure_issues"]])
    
    # Read definitions file content
    definitions_content = ""
    if DEFINITIONS_FILE.exists():
        definitions_content = DEFINITIONS_FILE.read_text(encoding='utf-8')
    
    # Build indexes
    skill_index_data = {
        "_DEFINITIONS": definitions_content,
        "generated_at": datetime.now().isoformat(),
        "total_skills": len(valid_skills),
        "skills": valid_skills
    }
    
    broken_skills_data = {
        "generated_at": datetime.now().isoformat(),
        "total_broken": len(broken_skills),
        "broken_skills": broken_skills
    }
    
    # Write outputs
    SKILL_INDEX_JSON.write_text(json.dumps(skill_index_data, indent=2), encoding='utf-8')
    
    # Write broken skills to separate file
    COPILOT_WAS_HERE = ROOT / "COPILOT_WAS_HERE.json"
    COPILOT_WAS_HERE.write_text(json.dumps(broken_skills_data, indent=2), encoding='utf-8')
    
    # Log to master
    status = "PASS" if len(total_issues) == 0 else "FAIL"
    note = f"{len(total_issues)} issues found" if total_issues else "All skills valid"
    
    log_to_master(
        check_or_run="CHECK",
        status=status,
        changes="Rebuilt skill index",
        skill="ALL",
        model="build_index_enhanced.py",
        clean_files="YES" if len(total_issues) == 0 else "NO",
        check_in_out="CHECK",
        note=note
    )
    
    # Print summary
    print(f"\n=== Summary ===")
    print(f"Valid skills: {len(valid_skills)}")
    print(f"Broken skills: {len(broken_skills)}")
    if broken_skills:
        print(f"\nBroken skills written to: COPILOT_WAS_HERE.json")
        for broken in broken_skills:
            print(f"  X {broken['skill_name']}: {', '.join(broken['issues'])}")
    
    if total_issues:
        print(f"\n=== Issues Found ({len(total_issues)}) ===")
        for issue in total_issues:
            print(f"  - {issue}")
    
    print(f"\nOutputs written:")
    print(f"  - {SKILL_INDEX_JSON}")
    print(f"  - {MASTER_LOG_CSV}")


if __name__ == "__main__":
    main()
