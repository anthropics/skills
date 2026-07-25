---
name: task-decomposition
description: Breaks down complex software, writing, or research tasks into small, atomic, independently completable units with dependency graphs and milestone breakdowns. Use when the user asks to plan a project, decompose a feature, create subtasks, split up work, or needs help organizing a large piece of work into a step-by-step plan. Triggered by phrases like "break down", "decompose", "where do I start", "too big", "split into tasks", "work breakdown", or "task list".
version: 1.0.0
triggers:
  - break down
  - decompose
  - split into tasks
  - too big
  - where to start
  - complex task
tags:
  - planning
  - decomposition
  - tasks
  - organization
difficulty: beginner
estimatedTime: 10
relatedSkills:
  - planning/design-first
  - planning/verification-gates
---

# Task Decomposition

You are breaking down a complex task into smaller, atomic units. Each unit should be independently completable and verifiable.

## Core Principle

**If a task feels too big, it is too big. Break it down until each piece is obvious.**

A well-decomposed task should take no more than a few hours to complete and have a clear definition of done. Aim for tasks that are small, independent, testable, and clearly scoped.

## Decomposition Techniques

### 1. Vertical Slicing

Break by user-visible functionality (each slice is deployable and testable independently):

```
Feature: User Registration
  Slice 1: Email/password signup — form, validation, account creation
  Slice 2: Email verification — send email, verify link, UI state
  Slice 3: Social login (OAuth) — Google button, OAuth flow, account link
```

### 2. Horizontal Layering

Break by system layer:

```
Feature: Order Processing
  Layer 1: Data Model       — entities, migrations
  Layer 2: Data Access      — repository, CRUD, queries
  Layer 3: Business Logic   — service, validation rules
  Layer 4: API Endpoints    — routes, error handling
  Layer 5: Frontend         — form, API client, loading/error states
```

### 3. Workflow Decomposition

Break by process steps:

```
Task: Checkout flow
  Step 1: Cart validation   — stock check, quantities, totals
  Step 2: Payment           — collect details, validate, process
  Step 3: Order creation    — record, payment link, inventory update
  Step 4: Confirmation      — email, success page, invoice
```

### 4. Component Decomposition

Break by UI or system component:

```
Task: Dashboard page
  Component 1: Header       — logo, nav, user menu
  Component 2: Stats cards  — revenue, orders, customers
  Component 3: Chart        — sales trend, data fetch/transform
  Component 4: Orders table — sort, pagination, row actions
```

> For more detailed worked examples of each technique, see `EXAMPLES.md`.

## Task Template

For each decomposed task, define:

```markdown
## Task: [Brief Title]

**Description:**
[What needs to be done in 1-2 sentences]

**Files to Create/Modify:**
- [ ] path/to/file1.ts
- [ ] path/to/file2.ts

**Steps:**
1. [First specific step]
2. [Second specific step]
3. [Third specific step]

**Done When:**
- [ ] [Success criterion 1]
- [ ] [Success criterion 2]
- [ ] Tests pass

**Dependencies:**
- Requires: [Other task if any]
- Blocks: [What this enables]
```

## Dependency Management

### Identify Dependencies

```
Task Graph:

[Data Model] ──┬──▶ [Repository]
               │
               └──▶ [API Types]
                        │
[Repository] ──────────▶ [Service]
                              │
[API Types] ──────────────────┤
                              ▼
                         [API Endpoints]
```

### Minimize Dependencies

- Prefer tasks that can run in parallel
- Use interfaces to decouple dependencies
- Start with foundational tasks first

### Order by Dependencies

```
Phase 1 (No dependencies):
- Task A: Data model
- Task B: API type definitions
- Task C: UI component skeletons

Phase 2 (Depends on Phase 1):
- Task D: Repository (needs A)
- Task E: API client (needs B)
- Task F: UI logic (needs C)

Phase 3 (Depends on Phase 2):
- Task G: Service (needs D)
- Task H: Connected UI (needs E, F)
```

## Decomposition Checklist

For each task, verify:

- [ ] **Atomic?** — Can be done without interruption
- [ ] **Clear?** — Scope is unambiguous
- [ ] **Testable?** — Know when it's done
- [ ] **Independent?** — Minimal dependencies
- [ ] **Small?** — Less than half a day

## Integration with Other Skills

- Use **design-first** to understand the full scope before decomposing
- Use **verification-gates** to define checkpoints between phases
- Use **testing/red-green-refactor** to implement each task
