---
name: habit-writer
description: Generate the folder structure and write all files (HABIT.md and skills) to the workspace.
---

# Habit Writer

Generate the complete habit folder structure based on all previous design decisions.

## Instructions

1. **Verify Complete Design**: Before writing any files, confirm you have:
   - Habit name (from discovery Q1)
   - Goal (from discovery Q2)
   - Skill list with descriptions (from workflow-analyzer)
   - Skill files with instructions (from skill-designer)
   - Static Matrix (from matrix-builder)
   - Dynamic Matrix Rules (from matrix-builder)
   - Quality Criteria (from matrix-builder)
   - Escalation logic (from discovery Q7)

2. **Pre-Flight Checklist**: Verify all required components exist before writing:
   - [ ] Habit name (kebab-case)
   - [ ] Description (1-2 sentences)
   - [ ] Goal section text
   - [ ] Static Matrix with all skills
   - [ ] Quality Criteria with 4 tiers
   - [ ] Escalation text
   - [ ] At least 2 skill files

3. **Create Directory Structure**:
   Create the habit in the project-level habits directory `.pi/habits/`:
   ```
   .pi/habits/{habit-name}/
   ├── HABIT.md
   └── skills/
       ├── {skill-1}.md
       ├── {skill-2}.md
       └── ...
   ```

4. **Write HABIT.md** with exact format:
   ```markdown
   ---
   name: {habit-name}
   description: {description}
   version: 1.0.0
   quality_target: 90
   max_iterations: 3
   ---

   # {Habit Name}

   ## Goal
   {goal text}

   ## Static Matrix

   | Condition | Skill to Run | Order |
   |-----------|-------------|-------|
   | always    | {skill-1}   | 1     |
   | ...       | ...         | ...   |

   ## Dynamic Matrix Rules
   {rules text}

   ## Skills
   - **{skill-1}**: {description}
   - **{skill-2}**: {description}

   ## Quality Criteria
   - **70**: {text}
   - **80**: {text}
   - **90**: {text}
   - **100**: {text}

   ## Escalation
   {escalation text}
   ```

5. **Write Each Skill File** in `skills/` subdirectory with exact format:
   ```markdown
   ---
   name: {skill-name}
   description: {what this skill does}
   ---

   # {Skill Name}

   ## Purpose
   {purpose text}

   ## Instructions
   {instructions text}

   ## Input
   {input description}

   ## Output
   {output description}

   ## Example
   {concrete example}
   ```

6. **Post-Write Verification**: After writing all files, verify:
   - All files exist
   - HABIT.md has correct frontmatter
   - All skills are in `skills/` subdirectory
   - No files are empty
   - Static Matrix references match skill filenames

7. **Report to User**: Output a summary of what was created:
   ```
   Created {habit-name} habit with:
   - HABIT.md (goal, static matrix, dynamic rules, quality criteria, escalation)
   - skills/{skill-1}.md
   - skills/{skill-2}.md
   - ...

   You can now run this habit with: /habit:{habit-name}
   ```
