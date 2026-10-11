import os
import re

def standardize_frontmatter(file_path):
    with open(file_path, 'r') as f:
        content = f.read()

    # Match YAML frontmatter
    match = re.match(r'^---\n(.*?)\n---\n(.*)', content, re.DOTALL)
    if not match:
        return

    frontmatter = match.group(1)
    body = match.group(2)

    new_frontmatter_lines = []
    for line in frontmatter.split('\n'):
        if line.startswith('name:'):
            name_val = line.split('name:', 1)[1].strip()
            # Convert to lowercase and replace non-alphanumeric with hyphens
            # Assuming it might be quoted
            name_val = name_val.strip('"\'')
            name_val = re.sub(r'[^a-z0-9]+', '-', name_val.lower()).strip('-')
            new_frontmatter_lines.append(f"name: {name_val}")
        else:
            new_frontmatter_lines.append(line)

    new_content = f"---\n{chr(10).join(new_frontmatter_lines)}\n---\n{body}"

    with open(file_path, 'w') as f:
        f.write(new_content)

if __name__ == '__main__':
    skills_dir = 'skills'
    for item in os.listdir(skills_dir):
        skill_path = os.path.join(skills_dir, item)
        if os.path.isdir(skill_path):
            skill_md = os.path.join(skill_path, 'SKILL.md')
            if os.path.exists(skill_md):
                standardize_frontmatter(skill_md)
                print(f"Standardized {skill_md}")
