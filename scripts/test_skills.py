import os
import sys
from pathlib import Path

# Define a mapping of skills to their entry point scripts
SKILLS_ROOT = r"D:\Nineth Circuit\CLAUDE_COPILOT HLP\NINTH CIR5\skills"

SKILL_SCRIPTS = {
    "skill-creator": f"{SKILLS_ROOT}/skill-creator/scripts/quick_validate.py",
    "ninth-circuit-cover": f"{SKILLS_ROOT}/PIMP-SMACK-APP/_archive/COVER_GENERATOR_COMPLETE/generate_cover.py",
    "universal-motion-brief": f"{SKILLS_ROOT}/universal-motion-brief/scripts/render_docx.py",
    "slack-gif-creator": f"{SKILLS_ROOT}/slack-gif-creator/scripts/create_gif.py",
    "algorithmic-art": f"{SKILLS_ROOT}/algorithmic-art/scripts/scaffold_art.py",
    "ninth-circuit-opening-brief": f"{SKILLS_ROOT}/ninth-circuit-opening-brief/assemble_opening_brief.py",
}

def validate_skills():
    results = {}
    print("Validating skill entry points...\n")
    
    for skill, script_path in SKILL_SCRIPTS.items():
        print(f"Checking {skill}...")
        
        # Normalize path
        path_obj = Path(script_path)
        
        if path_obj.exists() and path_obj.is_file():
            status = "PASS"
            details = f"Script found at {script_path}"
        else:
            status = "FAIL"
            details = f"Script NOT found at {script_path}"
            
        results[skill] = {"status": status, "details": details}
        print(f"  -> {status}")

    # Report
    print("\nValidation Summary:")
    print("-" * 40)
    for skill, res in results.items():
        print(f"{skill}: {res['status']}")
        if res['status'] == "FAIL":
            print(f"  Details: {res['details']}")
    print("-" * 40)

if __name__ == "__main__":
    validate_skills()
