# Discovery

Ask the user the following questions to gather the requirements for the new Habit.

## Questions

### Q1: Goal & Name
- **Question:** What is the name of the Habit you want to create (in kebab-case, e.g., `theme-creator`), and what is its primary goal?
- **Type:** free_text
- **Maps to:** Habit name, folder name, and the Goal section in `HABIT.md`.

### Q2: Core Workflow Stages
- **Question:** What are the key stages, steps, or tasks involved in this workflow from beginning to end?
- **Type:** free_text
- **Maps to:** The private skills that need to be created.

### Q3: Conditional Logic / Dynamic Paths
- **Question:** Are there any conditions under which certain steps should be skipped, run out of order, or have different settings? (e.g., "if tokens already exist, skip primitive-mapper")
- **Type:** free_text
- **Maps to:** Dynamic Matrix Rules and options in the Habit's `discovery.md`.

### Q4: Quality Targets & Rubric
- **Question:** How do you define a high-quality outcome? What are the key criteria Claude should use to grade the final output on a scale of 0 to 100?
- **Type:** free_text
- **Maps to:** Quality Criteria, quality_target, and escalation rules.

## Matrix Mapping

| Answer | Effect on Matrix |
|--------|-----------------|
| All answered | Proceed to `workflow-analyzer` |
