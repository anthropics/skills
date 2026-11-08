---
name: clawhup
description: >
  Use this skill for spec-driven AI development workflows — turning vague requirements
  into traceable, reviewable, executable specs before writing a single line of code.
  Invoke /clawhup <requirement> to walk through the full PRD → Design → Impl → AgentTask
  lifecycle on the ClawHup platform. Use /clawhup run <taskId> to resume an existing task.
  Each iteration creates auditable L1/L2/L3 Spec documents, requires user approval at
  every layer, and runs code changes only inside a started Agent Task with step-by-step
  progress reporting.
license: MIT
---

# ClawHup — Spec-Driven AI Development

> Stop vibe-coding. Lock the spec first, then let Claude execute.

ClawHup is a platform for structured, traceable AI-assisted software development.
This skill implements the **Four-Layer Methodology** — PRD → Design → Impl → Agent Task —
so every change has a paper trail and every code edit is preceded by written, approved specs.

Learn more: https://www.clawhup.com/methodology

## Usage

```
/clawhup <requirement>     # full lifecycle from requirements
/clawhup run <taskId>      # resume an existing Agent Task
```

## Four-Layer Methodology

| Layer | Output | Gate |
|-------|--------|------|
| **L1 PRD** | Requirements doc, user stories, acceptance criteria | User approval before L2 |
| **L2 Design** | Technical design, data model, API contracts | User approval + `confirmed` status before L3 |
| **L3 Impl** | Executable spec ≤8 steps, one responsibility per step | User approval + `frozen` status before Agent Task |
| **∞ Continuity** | Step 1 always queries prior task history for the same topic | Prevents repeating past failures |

## Workflow

### Starting a new iteration

1. **Research** — query existing specs (`clawhup_spec_list`) and task history (`clawhup_agent_task_list`) before writing anything
2. **L1 PRD** — write and upload requirements; wait for user approval
3. **L2 Design** — write technical design; wait for user approval
4. **L3 Impl Spec** — write executable steps; wait for user approval; freeze spec
5. **Agent Task** — create task bound to the frozen L3 spec with a detailed `planJson`
6. **Execute** — run each step, report progress with `clawhup_agent_step_report`, verify at the end
7. **Deploy** — use `/deploy` after code is merged

### Rules

- **Never write code without a running Agent Task** bound to a frozen L3 spec
- **Never skip approval gates** — `confirmed` and `frozen` status changes are user actions, not Claude actions
- **Every planJson must end with a verification step** — curl/Playwright/test confirming the feature works
- **Report every step** — no jumping from step 1 to `task_complete`

## MCP Tools

| Tool | Purpose |
|------|---------|
| `clawhup_spec_list` | Browse existing specs |
| `clawhup_spec_create` | Create L1/L2/L3 spec (requires `parentDocId` for L2/L3) |
| `clawhup_spec_update` | Write content / advance status |
| `clawhup_spec_get` | Read spec detail |
| `clawhup_agent_task_create` | Create task bound to a frozen L3 spec |
| `clawhup_agent_task_start` | Start the task |
| `clawhup_agent_step_report` | Report each step's outcome |
| `clawhup_agent_task_complete` | Mark complete (triggers spec → implemented) |
| `clawhup_agent_task_fail` | Mark failed |

## Setup

Install the ClawHup MCP server and get an API key at https://www.clawhup.com/mcp

```json
{
  "mcpServers": {
    "clawhup": {
      "command": "npx",
      "args": ["-y", "@clawhup/mcp-server"],
      "env": { "CLAWHUP_API_KEY": "<your-key>" }
    }
  }
}
```
