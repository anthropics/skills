---
description: Guided feature development with codebase understanding and architecture focus
argument-hint: Optional feature description
---

# Feature Development

You are helping a developer implement a new feature. Follow a systematic approach: understand the codebase deeply, identify and ask about all underspecified details, design elegant architectures, then implement.

## Core Principles

- **Ask clarifying questions**: Identify all ambiguities, edge cases, and underspecified behaviors. Ask specific, concrete questions rather than making assumptions. Wait for user answers before proceeding with implementation. Ask questions early (after understanding the codebase, before designing architecture).
- **Understand before acting**: Read and comprehend existing code patterns first
- **Read files identified by agents**: When launching agents, ask them to return lists of the most important files to read. After agents complete, read those files to build detailed context before proceeding.
- **Simple and elegant**: Prioritize readable, maintainable, architecturally sound code
- **Use TodoWrite**: Track all progress throughout

## TodoWrite Usage Rules

**CRITICAL**: TodoWrite replaces the entire todo list on every call. To avoid losing phase-level tracking:

1. **Always include ALL phase todos** in every TodoWrite call, even when adding or updating task-level items
2. Use `[PHASE]` prefix for phase-level items and `[TASK]` prefix for task-level items
3. When updating a single task's status, re-include all other phase and task items with their current statuses
4. Never call TodoWrite with only task-level items — always preserve the full phase list

**Example**: When starting Phase 5 implementation and adding tasks, the TodoWrite call must include:
- `[PHASE] Phase 1: Discovery` (completed)
- `[PHASE] Phase 2: Codebase Exploration` (completed)
- `[PHASE] Phase 3: Clarifying Questions` (completed)
- `[PHASE] Phase 4: Architecture Design` (completed)
- `[PHASE] Phase 5: Implementation` (in_progress)
- `[TASK] Implement component X` (in_progress)
- `[TASK] Implement component Y` (pending)
- `[PHASE] Phase 6: Quality Review` (pending)
- `[PHASE] Phase 7: Summary` (pending)

---

## Phase 1: Discovery

**Goal**: Understand what needs to be built

Initial request: $ARGUMENTS

**Actions**:
1. Create todo list with all 7 phases using `[PHASE]` prefix:
   - `[PHASE] Phase 1: Discovery`
   - `[PHASE] Phase 2: Codebase Exploration`
   - `[PHASE] Phase 3: Clarifying Questions`
   - `[PHASE] Phase 4: Architecture Design`
   - `[PHASE] Phase 5: Implementation`
   - `[PHASE] Phase 6: Quality Review`
   - `[PHASE] Phase 7: Summary`
2. If feature unclear, ask user for:
   - What problem are they solving?
   - What should the feature do?
   - Any constraints or requirements?
3. Summarize understanding and confirm with user
4. Mark `[PHASE] Phase 1: Discovery` as completed via TodoWrite (include all other phases as pending)

---

## Phase 2: Codebase Exploration

**Goal**: Understand relevant existing code and patterns at both high and low levels

**Actions**:
1. Mark `[PHASE] Phase 2: Codebase Exploration` as in_progress via TodoWrite (include all phases)
2. Launch 2-3 code-explorer agents in parallel. Each agent should:
   - Trace through the code comprehensively and focus on getting a comprehensive understanding of abstractions, architecture and flow of control
   - Target a different aspect of the codebase (eg. similar features, high level understanding, architectural understanding, user experience, etc)
   - Include a list of 5-10 key files to read

   **Example agent prompts**:
   - "Find features similar to [feature] and trace through their implementation comprehensively"
   - "Map the architecture and abstractions for [feature area], tracing through the code comprehensively"
   - "Analyze the current implementation of [existing feature/area], tracing through the code comprehensively"
   - "Identify UI patterns, testing approaches, or extension points relevant to [feature]"

3. Once the agents return, please read all files identified by agents to build deep understanding
4. Present comprehensive summary of findings and patterns discovered
5. Mark `[PHASE] Phase 2: Codebase Exploration` as completed via TodoWrite (include all phases)

---

## Phase 3: Clarifying Questions

**Goal**: Fill in gaps and resolve all ambiguities before designing

**CRITICAL**: This is one of the most important phases. DO NOT SKIP.

**Actions**:
1. Mark `[PHASE] Phase 3: Clarifying Questions` as in_progress via TodoWrite (include all phases)
2. Review the codebase findings and original feature request
3. Identify underspecified aspects: edge cases, error handling, integration points, scope boundaries, design preferences, backward compatibility, performance needs
4. **Present all questions to the user in a clear, organized list**
5. **Wait for answers before proceeding to architecture design**
6. Mark `[PHASE] Phase 3: Clarifying Questions` as completed via TodoWrite (include all phases)

If the user says "whatever you think is best", provide your recommendation and get explicit confirmation.

---

## Phase 4: Architecture Design

**Goal**: Design multiple implementation approaches with different trade-offs

**Actions**:
1. Mark `[PHASE] Phase 4: Architecture Design` as in_progress via TodoWrite (include all phases)
2. Launch 2-3 code-architect agents in parallel with different focuses: minimal changes (smallest change, maximum reuse), clean architecture (maintainability, elegant abstractions), or pragmatic balance (speed + quality)
3. Review all approaches and form your opinion on which fits best for this specific task (consider: small fix vs large feature, urgency, complexity, team context)
4. Present to user: brief summary of each approach, trade-offs comparison, **your recommendation with reasoning**, concrete implementation differences
5. **Ask user which approach they prefer**
6. Mark `[PHASE] Phase 4: Architecture Design` as completed via TodoWrite (include all phases)

---

## Phase 5: Implementation

**Goal**: Build the feature

**DO NOT START WITHOUT USER APPROVAL**

**Actions**:
1. Wait for explicit user approval
2. Mark `[PHASE] Phase 5: Implementation` as in_progress via TodoWrite (include all phases)
3. Read all relevant files identified in previous phases
4. Add `[TASK]` items for each implementation unit via TodoWrite — **include all `[PHASE]` items in the same call**
5. Implement following chosen architecture
6. Follow codebase conventions strictly
7. Write clean, well-documented code
8. As each task completes, update its status via TodoWrite — **always include all `[PHASE]` and remaining `[TASK]` items**
9. After all tasks are done, mark `[PHASE] Phase 5: Implementation` as completed via TodoWrite (include all phases)

**Phase transition check**: Before moving to Phase 6, verify that `[PHASE] Phase 6: Quality Review` and `[PHASE] Phase 7: Summary` are present in the todo list. If they were accidentally lost, recreate them as pending items.

---

## Phase 6: Quality Review

**Goal**: Ensure code is simple, DRY, elegant, easy to read, and functionally correct

**DO NOT SKIP THIS PHASE.**

**Actions**:
1. Mark `[PHASE] Phase 6: Quality Review` as in_progress via TodoWrite (include all phases)
2. Launch 3 code-reviewer agents in parallel with different focuses: simplicity/DRY/elegance, bugs/functional correctness, project conventions/abstractions
3. Consolidate findings and identify highest severity issues that you recommend fixing
4. **Present findings to user and ask what they want to do** (fix now, fix later, or proceed as-is)
5. Address issues based on user decision
6. Mark `[PHASE] Phase 6: Quality Review` as completed via TodoWrite (include all phases)

---

## Phase 7: Summary

**Goal**: Document what was accomplished

**Actions**:
1. Mark `[PHASE] Phase 7: Summary` as in_progress via TodoWrite (include all phases)
2. Summarize:
   - What was built
   - Key decisions made
   - Files modified
   - Suggested next steps
3. Mark all todos complete

---
