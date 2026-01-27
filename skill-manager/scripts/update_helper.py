import shutil
import os
import sys
import datetime

def backup_skill(skill_path):
    """
    Backs up SKILL.md to SKILL.md.bak.<timestamp>
    """
    if not os.path.exists(skill_path):
        return False, "Skill path does not exist"
        
    skill_md = os.path.join(skill_path, "SKILL.md")
    if not os.path.exists(skill_md):
        return False, "SKILL.md not found"
        
    timestamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
    backup_name = f"SKILL.md.bak.{timestamp}"
    backup_path = os.path.join(skill_path, backup_name)
    
    try:
        shutil.copy2(skill_md, backup_path)
        return True, backup_path
    except Exception as e:
        return False, str(e)

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python update_helper.py <skill_dir>")
        sys.exit(1)
        
    skill_dir = sys.argv[1]
    success, msg = backup_skill(skill_dir)
    
    if success:
        print(f"Backup created: {msg}")
    else:
        print(f"Backup failed: {msg}")
        sys.exit(1)
