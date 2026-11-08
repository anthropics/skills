---
name: skill-composer
description: Compose multiple skills into a unified workflow pipeline. Combine research, creativity, review, and other skills into custom multi-step processes. Use when a task requires chaining skills together, creating custom workflows, or designing compound skill sequences. Triggers on "워크플로우", "workflow", "파이프라인", "pipeline", "스킬 조합", "combine skills", "복합 프로세스".
argument-hint: "[workflow goal or skill combination request]"
allowed-tools: Read, Write, Edit, Glob, Grep, Bash
---

# Skill Composer

Modular workflow builder that chains skills into compound pipelines.

> Core principle: Feature Layer + Persona Layer separation, modular addon composition

## Rules (Absolute)

1. **Separation of concerns.** Every skill in a pipeline has exactly one responsibility. No skill does two things.
2. **Explicit data flow.** The output of skill N must be defined input for skill N+1. No implicit state.
3. **Composability over complexity.** Prefer chaining 3 simple skills over creating 1 complex one.
4. **Layer isolation.** Function layer (what to do) is separate from persona layer (how to communicate).
5. **Fail-forward.** If one skill in the pipeline fails, the pipeline should degrade gracefully, not crash.

## Architecture

### Two-Layer Model

Inherited from the 기본설정 에드온 system's modular design:

```
┌─────────────────────────────────────┐
│         Persona Layer               │
│  (tone, style, communication mode)  │
│  e.g., concise / detailed / Korean  │
├─────────────────────────────────────┤
│        Function Layer               │
│  (what the workflow actually does)  │
│  Skill A → Skill B → Skill C       │
└─────────────────────────────────────┘
```

- **Function Layer:** The pipeline of skills that process the task
- **Persona Layer:** Communication style applied uniformly across all steps

### Pipeline Patterns

#### Sequential Pipeline
```
[Input] → Skill A → Skill B → Skill C → [Output]
```
Each skill transforms the output of the previous one.

**Example:** Research → Analyze → Review
```yaml
pipeline: research-then-review
steps:
  1: { skill: cross-verified-research, input: "$TOPIC" }
  2: { skill: deep-dive-analyzer, input: "step.1.output" }
  3: { skill: adversarial-review, input: "step.2.output" }
```

#### Fork-Join Pipeline
```
         ┌→ Skill B ─┐
[Input] →│            │→ Merge → [Output]
         └→ Skill C ─┘
```
Parallel analysis merged into unified output.

**Example:** Multi-perspective evaluation
```yaml
pipeline: multi-perspective
steps:
  1: { skill: creativity-sampler, input: "$DECISION" }
  2a: { skill: adversarial-review, input: "step.1.option_chosen", parallel: true }
  2b: { skill: cross-verified-research, input: "step.1.option_chosen", parallel: true }
  3: { merge: ["step.2a", "step.2b"], format: "comparison-table" }
```

#### Iterative Pipeline
```
[Input] → Skill A → [Check] → Pass? → [Output]
                        ↓ No
                     Skill B → Skill A (retry)
```
Loop until quality gate passes.

**Example:** Write-review-refine cycle
```yaml
pipeline: quality-loop
steps:
  1: { skill: implement, input: "$TASK" }
  2: { skill: adversarial-review, input: "step.1.output" }
  3: { gate: "step.2.verdict == PASS", retry: 1, max_retries: 2 }
```

## Process

### Step 1: Identify the Goal

What is the end-to-end outcome?
- "Evaluate a technology choice with full rigor"
- "Design, implement, and validate a feature"
- "Research, decide, and document an architecture decision"

### Step 2: Select Skills

Browse available skills and select those that map to pipeline stages:

| Category | Available Skills |
|----------|-----------------|
| Research | `cross-verified-research`, `search-first` |
| Creativity | `creativity-sampler`, `brainstorming` |
| Analysis | `deep-dive-analyzer`, `adversarial-review` |
| Testing | `tiered-test-generator` |
| Persona | `persona-architect` |
| Planning | `writing-plans`, `plan` |
| Review | `code-review`, `full-review` |

### Step 3: Define Data Flow

For each transition between skills, specify:
- What data flows from skill N to skill N+1
- What format the data should be in
- Whether the transition is automatic or requires user approval

### Step 4: Build the Pipeline

Write the pipeline as a sequence of skill invocations with clear handoff points.

## Output Format

```markdown
## Workflow: [Name]

### Goal
[What this workflow achieves]

### Pipeline
```
[Step 1] ──→ [Step 2] ──→ [Step 3] ──→ [Output]
  skill        skill        skill
```

### Steps

#### Step 1: [Name] (skill: [skill-name])
- **Input:** [what it receives]
- **Action:** [what it does]
- **Output:** [what it produces]
- **Gate:** [pass/fail criteria, if any]

#### Step 2: [Name] (skill: [skill-name])
...

### Execution Notes
- [Any special considerations]
- [User approval points]
- [Fallback behavior]
```

## Pre-Built Workflows

### 1. Full-Rigor Decision
```
creativity-sampler → cross-verified-research → adversarial-review
```
Generate options → verify facts → stress-test the choice.

### 2. Research-to-Architecture
```
cross-verified-research → creativity-sampler → adversarial-review → architecture ADR
```
Research the domain → explore approaches → challenge the choice → document the decision.

### 3. Implementation Quality Gate
```
implement → tiered-test-generator → adversarial-review → [merge/reject]
```
Build it → generate tests → review it → gate the merge.

### 4. Deep Learning Pipeline
```
deep-dive-analyzer → tiered-test-generator → [assess gaps] → deep-dive-analyzer (retry)
```
Analyze deeply → test understanding → fill gaps → iterate.

## When to Use

- Tasks that span multiple concerns (research + decide + validate)
- When you want a repeatable, named workflow
- When quality gates between steps are needed
- When multiple skills should work together in a defined sequence

## When NOT to Use

- Simple tasks where a single skill suffices
- When the workflow is obvious and doesn't need formal definition
- One-off tasks that won't be repeated
