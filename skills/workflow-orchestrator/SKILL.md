---
name: workflow-orchestrator
description: Orchestrate multi-step workflows, pipelines, and task sequences by defining steps as a DAG, chaining skill/tool outputs between steps, running independent steps in parallel, and tracking progress in a state file. Use this skill whenever the user wants to run a workflow, orchestrate tasks, build a pipeline, chain tasks together, do X then Y then Z, automate a multi-step process, batch process items, run things in order or in parallel, or mentions "workflow", "pipeline", "orchestrate", "sequence of steps", or "chain these tasks" — even if they don't use those exact words. Any time a user describes more than two dependent tasks that need coordination, this skill applies.
---

# Workflow Orchestrator

Orchestrate multi-step workflows where each step maps to a skill invocation or tool call, with dependency tracking, parallel execution, and failure handling.

## Core Concepts

A **workflow** is a directed acyclic graph (DAG) of **steps**. Each step has:
- An `id` (unique within the workflow)
- A `skill` or `tool` to invoke
- An `input` prompt (may reference outputs from upstream steps via `{{step_id}}`)
- A `depends_on` list of step IDs that must complete before this step runs
- Optional `retry` and `fallback` configuration

Steps with no dependencies (or whose dependencies are all satisfied) run in parallel using multiple Agent tool calls in the same turn. Steps with unmet dependencies wait.

## Workflow Definition

Accept workflows in either YAML or natural language. When the user describes steps informally ("do X, then Y, then Z"), convert to the structured format before executing.

### Structured Format

```yaml
workflow:
  name: my-workflow
  steps:
    - id: step1
      skill: "skill-name-or-description"
      input: "what to do in this step"
      depends_on: []
    - id: step2
      skill: "another-skill"
      input: "use the output from {{step1}} to do this"
      depends_on: [step1]
    - id: step3
      skill: "third-skill"
      input: "combine {{step1}} and {{step2}}"
      depends_on: [step1, step2]
      retry:
        max_attempts: 2
        on_failure: "skip"  # or "abort" or "fallback"
      fallback:
        skill: "simpler-alternative"
        input: "do a simpler version instead"
```

Read `references/workflow-schema.md` for the complete schema definition with all fields and validation rules.

### Natural Language

When a user says something like "research topic X, then write a report based on the research, and also generate charts from the data — the report and charts can happen at the same time", parse it into the structured format:

```yaml
workflow:
  name: research-and-report
  steps:
    - id: research
      skill: "web research"
      input: "research topic X thoroughly"
      depends_on: []
    - id: report
      skill: "document writing"
      input: "write a report based on {{research}}"
      depends_on: [research]
    - id: charts
      skill: "data visualization"
      input: "generate charts from the data in {{research}}"
      depends_on: [research]
```

Always confirm the parsed workflow with the user before executing: show them the steps, dependencies, and parallel groups, and ask "Does this look right?"

## State Tracking

Create a `workflow-state.json` file in the current working directory to track execution progress. Update it after each step completes or fails.

```json
{
  "workflow_name": "my-workflow",
  "status": "running",
  "started_at": "2026-04-02T10:00:00Z",
  "completed_at": null,
  "steps": {
    "step1": {
      "status": "completed",
      "started_at": "2026-04-02T10:00:01Z",
      "completed_at": "2026-04-02T10:00:45Z",
      "output_summary": "Brief summary of what step1 produced",
      "error": null,
      "attempts": 1
    },
    "step2": {
      "status": "running",
      "started_at": "2026-04-02T10:00:46Z",
      "completed_at": null,
      "output_summary": null,
      "error": null,
      "attempts": 1
    },
    "step3": {
      "status": "pending",
      "started_at": null,
      "completed_at": null,
      "output_summary": null,
      "error": null,
      "attempts": 0
    }
  }
}
```

This file serves as both a progress tracker and a recovery mechanism. If execution is interrupted, read the state file to determine which steps completed and resume from where things left off.

## Execution Algorithm

### 1. Parse and Validate

- Parse the workflow definition (YAML or natural language)
- Validate: no circular dependencies, all referenced step IDs exist, all `depends_on` targets are valid
- Build the dependency graph

### 2. Initialize State

- Create `workflow-state.json` with all steps set to `pending`
- Set workflow status to `running`

### 3. Execute in Waves

Repeat until all steps are completed or the workflow is aborted:

1. **Find ready steps**: steps whose status is `pending` and whose dependencies are all `completed`
2. **Dispatch ready steps in parallel**: for each ready step, spawn an Agent tool call. If multiple steps are ready at the same time, spawn them all in the same turn so they run concurrently.
3. **Collect results**: as each Agent call returns, update the state file:
   - On success: set status to `completed`, record `output_summary`
   - On failure: set status to `failed`, record `error`, check retry/fallback config
4. **Handle failures**:
   - If the step has retries remaining, reset to `pending` and increment `attempts`
   - If a fallback is defined, create and dispatch the fallback step
   - If `on_failure` is `skip`, mark as `skipped` and continue (downstream steps that depend on it will also be skipped)
   - If `on_failure` is `abort`, halt the entire workflow
   - Default behavior (no retry/fallback config): mark as `failed`, skip downstream dependents, continue with independent branches

### 4. Passing Outputs Between Steps

When a step's `input` contains `{{step_id}}`, replace it with the `output_summary` from that step's state entry. The Agent prompt for downstream steps should include the full context:

```
Previous step outputs:
- step1: "Summary of step1's output"
- step2: "Summary of step2's output"

Your task: [the step's input with templates resolved]
```

This keeps downstream agents informed without requiring them to re-derive upstream work.

### 5. Report Results

When all steps are done (or the workflow is aborted), update the state file's top-level status and `completed_at`, then present a summary:

```
Workflow "my-workflow" completed.
  step1: completed (45s)
  step2: completed (1m 12s)
  step3: failed — "error message" (skipped after 2 retries)
  step4: skipped (depends on step3)

Overall: 2/4 steps succeeded, 1 failed, 1 skipped.
```

## Workflow Templates

Several predefined workflow templates are available for common patterns. Read `references/templates.md` for the full list. When a user's request matches a template pattern, suggest it: "This looks like a research-and-report workflow. Want me to use that template, or define custom steps?"

Templates are starting points — the user can modify steps, add/remove them, or change dependencies before execution.

## Agent Dispatch Pattern

When dispatching a step via the Agent tool, structure the prompt like this:

```
You are executing step "{step_id}" of the workflow "{workflow_name}".

Context from previous steps:
{resolved upstream outputs, if any}

Your task:
{step input with {{templates}} resolved}

Important:
- Focus only on this specific task
- Produce a clear, concise output summary when done
- Save any files to the working directory
- If you encounter an error you cannot resolve, report it clearly
```

## Resuming Interrupted Workflows

If a `workflow-state.json` already exists in the working directory when the user asks to run a workflow, check its status:
- If `running` with some steps `completed`: offer to resume from where it left off
- If `completed`: inform the user and ask if they want to re-run
- If `failed`: show which steps failed and offer to retry just those (and their downstream dependents)

## Tips for Effective Workflows

- Keep steps granular — each step should do one thing well
- Use meaningful step IDs that describe what the step does (e.g., `fetch-data`, `analyze-results`, not `step1`, `step2`)
- When a step produces files, have it mention the file paths in its output so downstream steps can find them
- For long workflows, check in with the user after major milestones rather than running everything silently
