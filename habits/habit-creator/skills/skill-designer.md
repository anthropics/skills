---
name: skill-designer
description: Write clear, detailed instructions for each of the private skills in SKILL.md format.
---

# Skill Designer

For each skill in the Final Skill List from the workflow-analyzer, create a detailed skill file.

## Instructions

1. **Read the Final Skill List**: Use the output from workflow-analyzer as your source.

2. **For Each Skill, Write a Skill File** with the following structure:

   ```markdown
   ---
   name: {skill-name}
   description: {what this skill does, in one sentence}
   ---

   # {Skill Name}

   ## Purpose
   {Detailed explanation of what this skill accomplishes}

   ## Instructions
   {Step-by-step instructions for the model to follow when executing this skill}

   ## Input
   {What data/files this skill needs}

   ## Output
   {What this skill produces}

   ## Example
   {A concrete example of input -> output}
   ```

3. **Quality Requirements for Each Skill File**:
   - Instructions must be specific and actionable (not vague like "analyze the code")
   - Include edge cases and how to handle them
   - Specify exact output format (markdown structure, JSON schema, etc.)
   - Include at least one concrete example
   - Keep skills focused on a single responsibility

4. **Present Each Skill File** to the user for review before proceeding.

5. **Wait for Confirmation**: Do NOT proceed to matrix-builder until the user confirms all skill files are correct.
