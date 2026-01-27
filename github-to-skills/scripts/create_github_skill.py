import sys
import os
import json
import datetime
import subprocess

def create_skill(repo_info, output_dir):
    """
    Scaffolds a new skill directory based on GitHub repository info.
    """
    repo_name = repo_info['name']
    safe_name = "".join(c if c.isalnum() or c in ('-','_') else '-' for c in repo_name).lower()
    skill_path = os.path.join(output_dir, safe_name)
    
    # 1. Create Directory Structure
    os.makedirs(os.path.join(skill_path, "scripts"), exist_ok=True)
    os.makedirs(os.path.join(skill_path, "references"), exist_ok=True)
    os.makedirs(os.path.join(skill_path, "assets"), exist_ok=True)
    
    # 2. Create SKILL.md with Extended Metadata
    skill_md_content = f"""---
name: {safe_name}
description: Skill wrapper for {repo_info['name']}. Generated from {repo_info['url']}.
github_url: {repo_info['url']}
github_hash: {repo_info['latest_hash']}
version: 0.1.0
created_at: {datetime.datetime.now().isoformat()}
entry_point: scripts/wrapper.py
---

# {repo_info['name']} Skill

This skill wraps the capabilities of [{repo_info['name']}]({repo_info['url']}).

## Overview

(Auto-generated context from README)
{repo_info['readme'][:500]}...

## Usage

This skill provides a Python wrapper to interface with the tool. 

### Prerequisites

Ensure the following dependencies are installed:
- [TODO: List dependencies based on requirements.txt]

## Implementation Details

The wrapper script in `scripts/wrapper.py` handles the invocation of the underlying tool.
"""
    
    with open(os.path.join(skill_path, "SKILL.md"), "w", encoding="utf-8") as f:
        f.write(skill_md_content)
        
    # 3. Create Placeholder Wrapper Script
    wrapper_content = f"""import sys
import subprocess

def main():
    print("This is a placeholder wrapper for {repo_name}.")
    # TODO: Implement actual invocation logic here based on {repo_name} usage
    # Example: subprocess.run(['{repo_name}', *sys.argv[1:]])

if __name__ == "__main__":
    main()
"""
    with open(os.path.join(skill_path, "scripts", "wrapper.py"), "w", encoding="utf-8") as f:
        f.write(wrapper_content)

    print(f"Skill scaffolded at: {skill_path}")
    print("Next steps:")
    print("1. Review SKILL.md and refine the description.")
    print("2. Implement the actual logic in scripts/wrapper.py.")
    print(f"3. Run: python package_skill.py {skill_path}")

if __name__ == "__main__":
    if len(sys.argv) < 3:
        print("Usage: python create_github_skill.py <json_info_file> <output_skills_dir>")
        sys.exit(1)
        
    json_file = sys.argv[1]
    output_dir = sys.argv[2]
    
    with open(json_file, 'r', encoding='utf-8') as f:
        repo_info = json.load(f)
        
    create_skill(repo_info, output_dir)
