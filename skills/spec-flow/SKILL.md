---
name: spec-flow
description: Interactive spec-driven development workflow with phase-by-phase confirmation. Each phase waits for user confirmation before proceeding. Trigger phrases include "spec-flow", "spec mode", "need a plan", or "structured development". Creates .spec-flow/ directory with proposal, requirements, design, and tasks documents.
---

# Spec-Flow - Structured Development Workflow

Structured workflow for complex feature development. Creates living documentation that guides implementation and serves as team reference.

## ⚠️ Interaction Rules (MUST Follow)

This skill uses a **phase-by-phase confirmation** workflow, ensuring users can review and adjust at each stage.

### Core Principles

1. **One phase at a time**: Only work on the current phase. NEVER generate documents for subsequent phases in advance.
2. **Mandatory confirmation**: After completing each phase, you MUST stop and wait for user confirmation.
3. **User-driven progression**: Only proceed to the next phase when user explicitly says "continue", "ok", "next", "looks good", "继续", "好", "下一步", etc.

### Confirmation Template

After completing each phase, you MUST use this format to request confirmation:

```
📋 **[Phase Name] Complete**

Created `.spec-flow/active/<feature>/<file>.md` containing:
- [Key content summary]

**Please review**:
1. [Review question]?
2. [Review question]?

✅ Say "continue" to proceed to next phase
✏️ Tell me what to modify if needed
```

### ❌ Prohibited Behaviors

- Generating multiple phase documents after user describes a feature
- Automatically proceeding to next phase without user confirmation
- Creating both proposal.md and requirements.md in one response
- Assuming user wants to skip confirmation for speed

### ✅ Correct Flow Example

```
User: I want to implement user authentication
AI: [Creates only proposal.md] + confirmation prompt

User: continue
AI: [Creates only requirements.md] + confirmation prompt

User: looks good, next
AI: [Creates only design.md] + confirmation prompt

User: continue
AI: [Creates only tasks.md] + confirmation prompt
```

### Fast Mode (Optional)

If user explicitly requests to skip phase-by-phase confirmation:
- "generate all documents at once"
- "fast mode"
- "skip confirmations"

Then you may generate all documents consecutively, but still request final overall confirmation.

## Quick Start

1. Initialize spec directory: Run `scripts/init-spec-flow.sh <feature-name>` or manually create `.spec-flow/active/<feature-name>/`
2. Copy templates from this skill's `templates/` directory
3. Follow four-phase workflow below
4. Archive completed specs to `.spec-flow/archive/` when done

## Four-Phase Workflow

### Phase 1: Proposal

**Goal**: Define WHY this change is needed

Create `.spec-flow/active/<feature>/proposal.md` using `templates/proposal.md.template`:

- **Background**: Context and motivation for the change
- **Goals**: What we want to achieve (with checkboxes)
- **Non-Goals**: What we explicitly won't do (reduces scope creep)
- **Scope**: In-scope vs out-of-scope boundaries
- **Risks**: Potential issues and mitigations
- **Open Questions**: Items needing clarification before proceeding

**Exit Criteria**: Proposal reviewed, open questions resolved, scope agreed.

**⏸️ Phase Checkpoint**: After creating proposal.md, ask user:
- Is the background accurate?
- Are goals clear and measurable?
- Is the scope boundary reasonable?
- Is risk assessment complete?

→ Wait for user confirmation before proceeding to Requirements phase

### Phase 2: Requirements

**Goal**: Define WHAT the system should do

Create `.spec-flow/active/<feature>/requirements.md` using `templates/requirements.md.template`:

**Use EARS Format** (see `references/ears-format.md`):
- **Ubiquitous**: "The system shall..."
- **Event-Driven**: "When [trigger], the system shall..."
- **State-Driven**: "While [state], the system shall..."
- **Unwanted Behavior**: "If [condition], then the system shall NOT..."

**Include**:
- Functional requirements (FR-001, FR-002, ...)
- Non-functional requirements: Performance, Security, Reliability (NFR-001, ...)
- Acceptance criteria (AC-001, AC-002, ...)

**Exit Criteria**: All requirements testable, acceptance criteria clear.

**⏸️ Phase Checkpoint**: After creating requirements.md, ask user:
- Do functional requirements cover all use cases?
- Are non-functional requirements (performance/security/reliability) sufficient?
- Are acceptance criteria testable?

→ Wait for user confirmation before proceeding to Design phase

### Phase 3: Design

**Goal**: Define HOW to implement

Create `.spec-flow/active/<feature>/design.md` using `templates/design.md.template`:

- **Architecture Overview**: High-level component diagram (use Mermaid)
- **Component Design**: Responsibilities and interfaces for each component
- **API Design**: Endpoints, request/response schemas
- **Data Model**: Entity relationships (use Mermaid erDiagram)
- **Error Handling**: Error codes, descriptions, resolutions
- **Migration Plan**: Steps for data/schema migrations (if applicable)

**Exit Criteria**: Design addresses all requirements, trade-offs documented.

**⏸️ Phase Checkpoint**: After creating design.md, ask user:
- Does the architecture meet all requirements?
- Is the API design clear?
- Are there any missing edge cases?

→ Wait for user confirmation before proceeding to Tasks phase

### Phase 4: Tasks

**Goal**: Break down into EXECUTABLE steps

Create `.spec-flow/active/<feature>/tasks.md` using `templates/tasks.md.template`:

**Task Guidelines** (see `references/task-decomposition.md`):
- Each task completable in 1-2 tool calls
- Include complexity estimate: Low/Medium/High
- List affected files
- Define dependencies between tasks
- Group into phases: Setup → Implementation → Testing → Documentation

**Progress Tracking**:
- ⏳ Pending → 🔄 In Progress → ✅ Done
- ❌ Blocked (add notes explaining blocker)

**Exit Criteria**: All tasks completed, tests passing, documentation updated.

**⏸️ Phase Checkpoint**: After creating tasks.md, ask user:
- Is the task granularity appropriate?
- Are dependencies correct?
- Ready to start implementation?

→ Wait for user confirmation before starting implementation

## ⚠️ Phase 5: Implementation

**Goal**: Execute tasks according to tasks.md

### 🎛️ Execution Modes

Implementation supports **three execution modes**. Default is **Step Mode** unless user specifies otherwise.

| Mode | Trigger Phrases | Behavior |
|------|-----------------|----------|
| **Step Mode** (Default) | "start implementation", "开始执行" | Execute ONE task, wait for confirmation, repeat |
| **Batch Mode** | "execute all", "一口气执行", "全部执行", "batch mode" | Execute ALL tasks consecutively, report at end |
| **Phase Mode** | "execute phase 1", "执行第一阶段", "execute setup" | Execute all tasks in ONE phase, then wait |

### 📋 Step Mode (Default)

Execute tasks one at a time with user confirmation between each.

**When to use**: Complex tasks, need careful review, first time using spec-flow

**Flow**:
```
User: start implementation

AI: 🔄 **Task T-001**: [description]
    [Executes task]
    ✅ Completed (1/10)
    👉 Say "continue" for next task

User: continue

AI: 🔄 **Task T-002**: [description]
    ...
```

### ⚡ Batch Mode

Execute all remaining tasks consecutively without waiting.

**When to use**: Simple tasks, trusted plan, want speed

**Trigger phrases**:
- "execute all tasks" / "全部执行"
- "batch mode" / "批量执行"
- "一口气执行完"
- "run all remaining tasks"

**Flow**:
```
User: execute all tasks

AI: ⚡ **Batch Mode Activated**

    🔄 T-001: [description] → ✅
    🔄 T-002: [description] → ✅
    🔄 T-003: [description] → ✅
    ...

    📊 **Batch Complete**: 10/10 tasks done

    **Summary**:
    - Files created: [list]
    - Files modified: [list]

    ⚠️ Stopped early? Check error above.
```

**Batch Mode Rules**:
1. Still update tasks.md after each task
2. Stop immediately if any task fails or has error
3. Provide summary at the end
4. User can interrupt with "stop" or "暂停"

### 📦 Phase Mode

Execute all tasks within a specific phase, then wait for confirmation.

**When to use**: Want to review after each phase (Setup → Core → Testing → Docs)

**Trigger phrases**:
- "execute phase 1" / "执行第一阶段"
- "execute setup phase" / "执行 Setup"
- "run all setup tasks"

**Flow**:
```
User: execute setup phase

AI: 📦 **Phase Mode: Setup**

    🔄 T-001: [description] → ✅
    🔄 T-002: [description] → ✅

    ✅ **Setup Phase Complete** (2/10 total)

    **Next phase**: Core Implementation (T-010 to T-015)
    👉 Say "continue" or "execute next phase"
```

### 🚨 BEFORE Starting Any Task (All Modes)

You MUST do these steps before executing:

1. **Read tasks.md** - Get current task list and statuses
2. **Identify target tasks** - Based on mode (one task / all tasks / phase tasks)
3. **Check dependencies** - Ensure dependency tasks are completed (`- [x]`)
4. **Read design.md** - Review relevant design sections

### ✅ REQUIRED Behaviors (All Modes)

| Action | Step Mode | Batch Mode | Phase Mode |
|--------|-----------|------------|------------|
| Read tasks.md before starting | ✅ | ✅ | ✅ |
| Check dependencies | ✅ | ✅ | ✅ |
| Update `- [ ]` to `- [x]` after each task | ✅ | ✅ | ✅ |
| Show progress | After each | After each | After each |
| Wait for confirmation | After each task | After all done | After phase done |
| Stop on error | ✅ | ✅ | ✅ |

### ❌ PROHIBITED Behaviors (All Modes)

| Prohibited Action | Why It's Wrong |
|-------------------|----------------|
| Skip a task | Breaks dependency chain |
| Execute tasks out of order | Dependencies may not be met |
| Do work not in tasks.md | Scope creep, untracked changes |
| Forget to update tasks.md | Progress tracking inaccurate |
| Continue after error without user approval | May cause cascading failures |

### 🛑 When to STOP (All Modes)

Stop and ask user for guidance when:
- A task fails or produces errors
- Design is incomplete for current task
- A dependency is missing or blocked
- Task description is ambiguous
- Need a decision not covered in design.md

## Directory Structure

```
project-root/
└── .spec-flow/
    ├── steering/           # Global project context (optional)
    │   ├── constitution.md # Project governance principles
    │   ├── product.md      # Product vision and goals
    │   ├── tech.md         # Technology constraints
    │   └── structure.md    # Code organization patterns
    ├── active/             # Work in progress
    │   └── <feature-name>/
    │       ├── proposal.md
    │       ├── requirements.md
    │       ├── design.md
    │       ├── tasks.md
    │       └── .meta.json  # Status, timestamps, owner
    └── archive/            # Completed features (for reference)
        └── <feature-name>/
            └── ...
```

## Steering Documents (Optional)

For larger projects, create `.spec-flow/steering/` documents to provide consistent context across all specs:

| Document | Purpose | Template |
|----------|---------|----------|
| `constitution.md` | Project governance, decision-making principles | `templates/steering/constitution.md.template` |
| `product.md` | Product vision, target users, key metrics | `templates/steering/product.md.template` |
| `tech.md` | Tech stack, constraints, dependencies | `templates/steering/tech.md.template` |
| `structure.md` | Code organization, naming conventions | `templates/steering/structure.md.template` |

## Workflow Tips

### Phase Transitions

| From | To | Condition |
|------|-----|-----------|
| Proposal | Requirements | Proposal approved, questions resolved |
| Requirements | Design | Requirements complete, testable |
| Requirements | Tasks | Simple feature, design implicit |
| Design | Tasks | Design approved |
| Tasks | Done | All tasks complete, archived |

### When to Skip Phases

- **Skip Design**: For simple features where architecture is obvious
- **Never Skip**: Proposal and Tasks (always clarify intent and break down work)

### Best Practices

1. **Keep specs updated**: Update status as work progresses
2. **Link to code**: Reference commits, PRs, file paths in tasks
3. **Archive completed specs**: Move to `.spec-flow/archive/` when done
4. **Review steering docs**: Reference them when writing new specs
5. **Validate completeness**: Run `scripts/validate-spec-flow.py` before implementation

## References

- **Complete workflow guide**: See `references/workflow.md`
- **EARS requirement format**: See `references/ears-format.md`
- **Task decomposition patterns**: See `references/task-decomposition.md`
- **Real-world examples**: See `references/examples/`

## Compatibility

This skill works with any AI agent that supports the Skills format:
- Claude Code (`~/.claude/skills/`)
- Blade (`~/.blade/skills/`)
- Other compatible agents

The `.spec-flow/` directory is Git-friendly and can be committed with your project for team collaboration.
