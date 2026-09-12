# Habits — Agent Habits Specification

> Habits are orchestrated containers that wrap multiple Skills into a repeatable, quality-driven workflow. Where a Skill teaches Claude *how* to do one thing, a Habit teaches Claude *when*, *in what order*, and *how well* to do many things together.

---

## Concepts

### Skill
A single-purpose instruction file (`SKILL.md`) that teaches Claude how to perform one specific task. Skills are the atomic unit — they don't know about each other.

### Habit
A folder-based container (`HABIT.md` + `skills/`) that:
- Defines a **goal** (the desired outcome)
- Contains **custom Skills** tailored to this Habit's context
- Runs a **Discovery Phase** to build a Matrix from user input
- **Orchestrates** Skills dynamically based on the Matrix
- **Evaluates** output quality and loops or switches Skills until the target is met

---

## Folder Structure

```
habits/
└── {habit-name}/
    ├── HABIT.md          ← Orchestration logic, static matrix, quality targets
    └── skills/
        ├── discovery.md  ← Questions to ask the user
        ├── {skill-1}.md
        ├── {skill-2}.md
        └── {skill-n}.md
```

**Rules:**
- Every Habit MUST have a `HABIT.md` and a `skills/` folder
- Every Habit MUST have a `discovery.md` skill
- Skills inside a Habit are **private** — not shared with other Habits
- Skill filenames are lowercase with hyphens

---

## HABIT.md Structure

```markdown
---
name: habit-name
description: What this Habit accomplishes and when to use it
version: 1.0.0
quality_target: 90        ← Minimum score to accept output (0-100)
max_iterations: 3         ← Max retry loops before escalating
---

# {Habit Name}

## Goal
One sentence describing the desired final output.

## Static Matrix
[Pre-defined rules that always apply regardless of user input]

| Condition | Skill to Run | Order |
|-----------|-------------|-------|
| always    | discovery   | 1     |
| ...       | ...         | ...   |

## Dynamic Matrix Rules
[How Claude builds the execution plan from discovery answers]

## Skills
[List of available skills with their purpose]

## Quality Criteria
[How to score the output — what counts as 70, 80, 90, 100]

## Escalation
[What to do if max_iterations is reached without hitting quality_target]
```

---

## Lifecycle

```
START
  │
  ▼
1. DISCOVERY PHASE
   └── Run discovery.md
   └── Ask user the Matrix questions
   └── Build Dynamic Matrix from answers
  │
  ▼
2. PLAN PHASE
   └── Merge Static Matrix + Dynamic Matrix
   └── Determine: which skills, what order, what quality gates
  │
  ▼
3. EXECUTE PHASE
   └── Run skills in planned order
   └── Pass output between skills as context
  │
  ▼
4. EVALUATE PHASE
   └── Score output against Quality Criteria (0-100)
   └── If score >= quality_target → DONE ✓
   └── If score < quality_target AND iterations < max_iterations → back to EXECUTE
   └── If max_iterations reached → ESCALATE
  │
  ▼
5. OUTPUT
```

---

## Discovery Phase

The `discovery.md` skill defines the questions Claude asks before executing. Answers feed directly into the Dynamic Matrix.

### discovery.md Structure

```markdown
---
name: discovery
description: Gather user context to build the execution matrix
---

# Discovery

Ask the user the following questions. Collect all answers before proceeding.

## Questions

### Q1: {Question text}
- **Type:** single_choice | multi_choice | free_text | scale
- **Options:** [if applicable]
- **Maps to:** {what matrix dimension this affects}

### Q2: ...

## Matrix Mapping

| Answer | Effect on Matrix |
|--------|-----------------|
| Q1 = A | Use skill-x before skill-y |
| Q1 = B | Skip skill-y, run skill-z |
| Q2 = high | Set quality_target = 95 |
```

---

## Matrix

The Matrix is the execution plan. It has two layers:

### Static Matrix
Defined in `HABIT.md`. Rules that always apply:
- Required skills that always run
- Fixed ordering constraints
- Hard quality gates

### Dynamic Matrix
Built at runtime from Discovery answers:
- Which optional skills to include
- Order adjustments
- Quality target overrides
- Parameter overrides per skill

### Final Matrix (Merged)
```
Static Matrix + Dynamic Matrix = Execution Plan

Execution Plan = [
  { skill: "discovery",   order: 1, required: true  },
  { skill: "skill-a",     order: 2, required: true  },
  { skill: "skill-b",     order: 3, required: false, condition: "Q1 = A" },
  { skill: "validator",   order: 4, required: true  },
]
```

---

## Quality Evaluation

Every Habit defines its own quality rubric. Claude scores the output after each execution cycle.

### Scoring Format
```
Quality Score: {0-100}
Breakdown:
  - Criterion 1: {score}/25
  - Criterion 2: {score}/25
  - Criterion 3: {score}/25
  - Criterion 4: {score}/25

Gap: {what's missing to reach quality_target}
Next action: {which skill to re-run or adjust}
```

### Score Thresholds (default)
| Score | Meaning |
|-------|---------|
| 90-100 | ✅ Accept — meets quality_target |
| 75-89  | 🔄 Retry — re-run last skill with gap context |
| 50-74  | 🔄 Re-plan — rebuild execution plan from Matrix |
| 0-49   | ⚠️ Escalate — inform user, ask for guidance |

---

## Habit Creator

The **Habit Creator** is a meta-Habit that helps you build new Habits. It is itself a Habit.

### What it does
1. Asks you what workflow you want to automate
2. Identifies the Skills needed
3. Writes the `discovery.md` questions
4. Builds the Static Matrix
5. Defines the quality rubric
6. Generates the complete Habit folder structure

### Location
```
habits/
└── habit-creator/
    ├── HABIT.md
    └── skills/
        ├── discovery.md
        ├── workflow-analyzer.md
        ├── skill-designer.md
        ├── matrix-builder.md
        └── habit-writer.md
```

---

## Habit Runner

The **Habit Runner** is the execution engine. It reads a Habit and runs it end-to-end.

### Responsibilities
- Load `HABIT.md` and all skills in `skills/`
- Run the lifecycle (Discovery → Plan → Execute → Evaluate → Output)
- Maintain iteration state
- Pass context between skills
- Report quality scores to user

---

## Naming Conventions

| Thing | Convention | Example |
|-------|-----------|---------|
| Habit folder | kebab-case | `token-binder` |
| HABIT.md | uppercase | `HABIT.md` |
| Skill files | kebab-case + `.md` | `semantic-mapper.md` |
| Habit name (frontmatter) | kebab-case | `token-binder` |

---

## Example: Token Binder Habit

```
habits/
└── token-binder/
    ├── HABIT.md
    └── skills/
        ├── discovery.md        ← asks about component type, brand, complexity
        ├── primitive-mapper.md ← maps raw values to primitive tokens
        ├── semantic-mapper.md  ← maps primitives to semantic tokens
        ├── component-binder.md ← binds semantic tokens to component props
        └── validator.md        ← validates token hierarchy and naming
```

**HABIT.md excerpt:**
```yaml
name: token-binder
quality_target: 90
max_iterations: 3
```

**Flow:**
1. Discovery asks: component type? brand colors? token naming convention?
2. Matrix decides: skip `primitive-mapper` if tokens already exist
3. Execute: run mapper → binder → validator
4. Evaluate: score token coverage, naming consistency, hierarchy correctness
5. If score < 90: re-run `semantic-mapper` with gap context
6. Output: validated token bindings ready for Figma

---

## Relationship to Skills Repo

```
anthropics/skills (repo)
├── skills/          ← Public, shared, reusable Skills
└── spec/            ← Skills specification

habits/ (this spec)
├── SPEC.md          ← This document
├── habit-creator/   ← Meta-Habit for building Habits
└── {habit-name}/
    ├── HABIT.md
    └── skills/      ← Private Skills, scoped to this Habit only
```

Habits sit **above** Skills in the hierarchy. A Habit can reference concepts from public Skills as inspiration, but its own `skills/` are always custom and private.
