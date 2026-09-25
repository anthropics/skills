---
name: matrix-builder
description: Design the Static Matrix, Dynamic Matrix Rules, and Quality Criteria for the new Habit.
---

# Matrix Builder

Design the execution matrix and quality rubric for the new Habit based on the confirmed skill list.

## Instructions

1. **Build the Static Matrix**: Create a table defining execution order and conditions.

   Format:
   ```markdown
   ## Static Matrix

   | Condition | Skill to Run | Order |
   |-----------|-------------|-------|
   | always    | {skill-1}   | 1     |
   | always    | {skill-2}   | 2     |
   | when {condition} | {skill-3} | 3 |
   ```

   Rules:
   - Each skill from the Final Skill List must appear exactly once
   - Order reflects data dependencies (skills that produce output go before skills that consume it)
   - Use `always` for unconditional skills
   - Use `when {condition}` for conditional skills (e.g., "when user has design system")

2. **Design Dynamic Matrix Rules**: Define conditional logic based on discovery answers.

   Format:
   ```markdown
   ## Dynamic Matrix Rules
   - If Q5 answer contains "skip style guide", skip step 3 (style-generator)
   - If Q4 answer specifies JSON output, use json-formatter instead of markdown-formatter
   ```

3. **Define Quality Criteria**: Create a scoring rubric with 4 tiers.

   Format:
   ```markdown
   ## Quality Criteria
   - **70**: {minimum viable output - what's included at this level}
   - **80**: {good output - what additional quality is present}
   - **90**: {great output - comprehensive and production-ready}
   - **100**: {exceptional - exceeds expectations, handles all edge cases}
   ```

4. **Present to User**: Show the complete matrix and criteria for confirmation before proceeding.

5. **Wait for Confirmation**: Do NOT proceed to habit-writer until the user confirms.
