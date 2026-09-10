import os
import re

skills_dir = 'skills'

for root, dirs, files in os.walk(skills_dir):
    if 'SKILL.md' in files:
        filepath = os.path.join(root, 'SKILL.md')
        with open(filepath, 'r') as f:
            content = f.read()

        match = re.match(r'^---\n(.*?)\n---\n(.*)', content, re.DOTALL)
        if match:
            frontmatter = match.group(1)
            body = match.group(2)

            # Check if name is already lowercase and hyphenated
            lines = frontmatter.split('\n')
            new_lines = []
            has_name = False
            for line in lines:
                if line.startswith('name:'):
                    has_name = True
                    name_val = line.split('name:', 1)[1].strip().strip('"\'')
                    name_val = re.sub(r'[^a-z0-9]+', '-', name_val.lower()).strip('-')
                    new_lines.append(f"name: {name_val}")
                else:
                    new_lines.append(line)

            if not has_name:
                skill_name = os.path.basename(root)
                skill_name = re.sub(r'[^a-z0-9]+', '-', skill_name.lower()).strip('-')
                new_lines.insert(0, f"name: {skill_name}")

            new_frontmatter = '\n'.join(new_lines)

            with open(filepath, 'w') as f:
                f.write(f"---\n{new_frontmatter}\n---\n{body}")
        else:
            print(f"No frontmatter found in {filepath}. Creating one.")
            skill_name = os.path.basename(root)
            skill_name = re.sub(r'[^a-z0-9]+', '-', skill_name.lower()).strip('-')

            with open(filepath, 'w') as f:
                f.write(f"---\nname: {skill_name}\ndescription: converted skill\n---\n{content}")
