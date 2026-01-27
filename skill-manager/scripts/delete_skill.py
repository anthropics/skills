import os
import sys
import shutil

def delete_skill(skills_root, skill_name):
    skill_dir = os.path.join(skills_root, skill_name)
    
    if not os.path.exists(skill_dir):
        print(f"Error: Skill '{skill_name}' not found at {skill_dir}")
        return False
        
    try:
        # Physical deletion
        shutil.rmtree(skill_dir)
        print(f"Successfully deleted skill: {skill_name}")
        return True
    except Exception as e:
        print(f"Error deleting skill '{skill_name}': {e}")
        return False

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python delete_skill.py <skill_name> [skills_root]")
        sys.exit(1)
        
    name = sys.argv[1]
    root = r"C:\Users\20515\.claude\skills"
    if len(sys.argv) > 2:
        root = sys.argv[2]
        
    delete_skill(root, name)
