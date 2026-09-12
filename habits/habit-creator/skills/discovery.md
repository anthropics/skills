---
name: discovery
description: Gather user context about the workflow they want to automate in order to build the execution matrix and skills structure.
---

# Discovery

Ask the user the following questions ONE AT A TIME. Wait for their answer before asking the next question. This ensures we gather detailed, high-quality information.

## Instructions

1. Ask each question individually in order
2. If the user's answer is vague or short, ask follow-up questions to get more detail
3. After all questions are answered, summarize what you understood and ask for confirmation before proceeding
4. Do NOT proceed to the next phase until the user confirms the summary is accurate

## Discovery Mode Rules

- Never collect all answers at once.
- Ask exactly one question.
- Wait for response.
- Validate response.
- Ask follow-up if needed.
- Store answer.
- Continue to next question.
- After final answer, generate summary.
- Require explicit user confirmation before workflow-analyzer.

## Questions

### Q1: Habit Name
- **Question:** What is the name of the Habit you want to create? Use lowercase kebab-case (e.g., `theme-creator`, `ux-strategy`, `api-documenter`).
- **Type:** free_text
- **Maps to:** Folder name, HABIT.md `name` field.
- **Validation:** Must be lowercase, alphanumeric + hyphens only, no spaces.

### Q2: Primary Goal
- **Question:** What is the primary goal of this Habit? What problem does it solve or what outcome does it produce? Be specific about the end result.
- **Type:** free_text
- **Maps to:** The Goal section in `HABIT.md`.
- **Follow-up if vague:** Can you describe what the final output looks like? What does "done" mean for this workflow?

### Q3: Workflow Stages
- **Question:** What are the key stages or steps in this workflow, from start to finish? List each stage with a brief description of what it does.
- **Type:** free_text
- **Maps to:** The private skills that need to be created.
- **Follow-up if vague:** For each stage, what inputs does it need? What does it produce? Are there any decision points?

### Q4: Inputs & Outputs
- **Question:** For each workflow stage, what are the specific inputs (files, data, user responses) and outputs (files, text, decisions)?
- **Type:** free_text
- **Maps to:** Skill input/output specifications in each private skill's instructions.
- **Follow-up if vague:** Can you give an example of what a typical input looks like? What format should the output be in?

### Q5: Edge Cases & Conditions
- **Question:** Are there any conditions under which steps should be skipped, run differently, or have special handling? What edge cases should the Habit handle gracefully?
- **Type:** free_text
- **Maps to:** Dynamic Matrix Rules and conditional logic in the Habit.
- **Examples:** "If the user already has a design system, skip the style-guide step", "If the API returns an error, retry up to 3 times", "If the input is a PDF, extract text first".

### Q6: Quality Criteria
- **Question:** How do you define a high-quality outcome? What are the 3-5 most important criteria for evaluating the result? What would make you reject the output?
- **Type:** free_text
- **Maps to:** Quality Criteria section and quality_target in `HABIT.md`.
- **Follow-up if vague:** What does a perfect result look like? What are common mistakes to avoid?

### Q7: Escalation & Failure
- **Question:** If the Habit cannot produce a good result after multiple attempts, what should happen? Should it ask the user for guidance, simplify the output, or report the issue?
- **Type:** free_text
- **Maps to:** Escalation section in `HABIT.md`.

## Matrix Mapping

| Answer | Effect on Matrix |
|--------|-----------------|
| All answered | Proceed to `workflow-analyzer` |
| Q5 has conditions | Add conditional rules to Dynamic Matrix |
| Q6 has specific criteria | Use as Quality Criteria rubric |
