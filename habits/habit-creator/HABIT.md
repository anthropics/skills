---
name: habit-creator
description: Meta-Habit that helps you design and build new Habits. Use this when you want to design, structure, and generate a new Habit folder with custom private skills, dynamic execution matrices, and quality rubrics.
version: 1.0.0
quality_target: 90
max_iterations: 3
---

# Habit Creator

## Goal
To orchestrate the generation of a complete, high-quality, and correctly formatted Habit folder structure containing `HABIT.md` and all required custom private skills.

## Static Matrix

| Condition | Skill to Run | Order |
|-----------|-------------|-------|
| always    | discovery   | 1     |
| always    | workflow-analyzer | 2 |
| always    | skill-designer | 3 |
| always    | matrix-builder | 4 |
| always    | habit-writer | 5 |

## Dynamic Matrix Rules
- None for the Habit Creator itself (it always runs all steps in sequence).

## Skills
- **discovery**: Gathers target workflow requirements, input/output structures, and success criteria from the user.
- **workflow-analyzer**: Breaks down the target workflow into logical sub-tasks and designs the custom private skill list.
- **skill-designer**: Writes clear, detailed instructions for each of the private skills in `SKILL.md` format.
- **matrix-builder**: Designs the Static Matrix, Dynamic Matrix Rules, and Quality Criteria for the new Habit.
- **habit-writer**: Generates the folder structure and writes all files (`HABIT.md`, `discovery.md`, and skills) to the workspace.

## Quality Criteria
- **70**: Core files are generated, but the custom private skills lack details, or the Quality Criteria are too generic.
- **80**: All files generated, private skills are functional, but edge cases are not handled, and Dynamic Matrix Rules are simplistic.
- **90**: Complete and comprehensive Habit directory. Every private skill has explicit instructions and example usages. `HABIT.md` contains robust Static Matrix, conditional Dynamic Matrix rules, clear quality thresholds, and detailed escalation logic.
- **100**: Flawless Habit setup with exceptionally detailed instructions, extensive edge-case coverage, complex dynamic rules (with mappings), and robust verification/scoring procedures.

## Escalation
If `max_iterations` is reached without achieving a quality score of 90+, halt execution, report the detailed gaps to the user, and ask for manual alignment on the missing details.
