1. [Description]
This skill provides the canonical guide and tools for creating new skills or updating existing ones. It defines the required structure (SKILL.md, instructions folder, scripts), metadata standards, and best practices for extending the agent's capabilities. It includes scripts to validate the skill structure.

2. [requirements]
- Python 3.x (for validation scripts)
- A text editor
- Understanding of the skill structure defined in `SKILL.md`.

3. [Cautions]
- Always run `scripts/build_index.py` (from the skills root) after creating or modifying a skill to ensure it is indexed correctly.
- Do not deviate from the folder structure: `skills/[skill-name]/SKILL.md` and `skills/[skill-name]/[skill-name]_instructions/`.
- Ensure `SKILL.md` has valid YAML frontmatter.

4. [Definitions]
- **Skill**: A modular package of knowledge and tools.
- **Frontmatter**: YAML metadata at the top of `SKILL.md` (name, description).
- **Instructions Folder**: A directory named `[skill-name]_instructions` containing numbered markdown files.

5. [log]
(No run logs available yet. This section will be populated by the system upon successful execution.)

6. [model_readme]
When creating a new skill:
1. Create a new directory in `skills/` with a kebab-case name.
2. Create `SKILL.md` with the required frontmatter.
3. Create the `[skill-name]_instructions` directory.
4. Add `1-models_readme.md` and populate it with this schema.
5. Add any necessary scripts in a `scripts/` subdirectory.
6. Run `python skills/skill-creator/scripts/quick_validate.py [path_to_new_skill]` to check your work.
7. Run `python skills/scripts/build_index.py` to update the global index.
