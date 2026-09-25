---
name: workflow-analyzer
description: Analyze the discovery responses and break down the target workflow into a list of modular private skills.
---

# Workflow Analyzer

Review the responses collected in the discovery phase and analyze the workflow architecture.

## Instructions

1. **Analyze Requirements**: Parse the user's description of the workflow goal and stages from the discovery answers.

2. **Decompose into Skills**: Break the workflow down into a list of modular, private skills. Each skill must have a single, clearly defined responsibility.
   - For example, if the workflow is "Create a website layout and generate code", break it down into:
     - `layout-planner` (architect the page sections)
     - `component-styler` (write styling and design patterns)
     - `code-generator` (compile into final HTML/CSS)
     - `accessibility-checker` (verify contrast and layout semantic tags)
   - **Minimum 2 skills, maximum 8 skills per habit**
   - Each skill should be independently testable

3. **Establish Data Flow**: Determine what inputs and outputs each skill expects, and how context is passed between them (e.g. `layout-planner` passes a section map to `component-styler`).

4. **Present Architecture to User**: You MUST present the proposed skill list to the user for confirmation before proceeding. Format:

   ```
   Proposed Skills for {habit-name}:

   1. {skill-1-name}: {brief description}
      - Input: {what it needs}
      - Output: {what it produces}

   2. {skill-2-name}: {brief description}
      - Input: {what it needs}
      - Output: {what it produces}

   ... (repeat for all skills)

   Does this look correct? Any skills to add, remove, or modify?
   ```

5. **Wait for User Confirmation**: Do NOT proceed to skill-designer until the user confirms the skill list is correct.

6. **Document the Final List**: After confirmation, output a clear summary that the next step (skill-designer) can use:
   ```
   Final Skill List:
   - {skill-1}: {description}
   - {skill-2}: {description}
   - ...
   ```
