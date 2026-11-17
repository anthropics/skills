---
name: project-memory
description: >
  Use when resuming work after chat loss, switching AI models, migrating
  context to a new agent or workspace, or maintaining long-running research
  and project memory across sessions. Manages roadmap, decision log,
  hypotheses, research evidence, and recovery checkpoints as separate
  canonical files so no single transcript becomes the source of truth.
  Trigger phrases: resume work, context lost, switch model, handoff brief,
  update project docs, classify decisions, audit memory, migrate context.
compatibility: "Claude Code, Codex CLI, Gemini CLI, Cursor, any agent supporting the Agent Skills standard"
license: MIT
metadata:
  author: continuity-research-memory-skill
  version: "1.2"
---

# Project Memory Skill

Use this skill when the user wants to preserve, recover, migrate, or audit long-running project or research context across chat loss, model changes, tool handoffs, or multi-session work.

The skill separates **current truth**, **plans**, **decisions**, **evidence**, **hypotheses**, **human summaries**, and **recovery checkpoints** so that no single chat transcript becomes the source of truth.

## When to use

Use this skill when the user asks to:

- resume work after a lost or interrupted chat
- create a durable project memory or research log
- migrate context from one model, agent, workspace, or repository to another
- update project docs after new work, decisions, research, experiments, or failures
- produce a handoff brief for a human or another model
- distinguish confirmed facts from hypotheses, plans, and unresolved questions
- audit whether a project has enough continuity documentation

Do not use this skill as a replacement for domain expertise, citations, or source verification. It is a continuity and documentation-routing skill.

## Operating assumption

The human usually does not write memory files directly.
The AI agent is responsible for updating the project memory during the chat or coding session.

Do not rely on tool-internal or session-local memory as the canonical source of truth.
Treat repository files as the durable, shared memory layer across Codex, Claude Code, and future tools.

## Core principle

Capture broadly. Promote narrowly.

Do not let hypotheses, plans, or recovery notes silently become truth.

Route information by status:

| Information type | Canonical file |
| --- | --- |
| Confirmed current state | `CURRENT_STATE.md` |
| Future intended work | `ROADMAP.md` |
| Decisions and rationale | `DECISION_LOG.md` |
| Research observations, experiments, evidence, results | `RESEARCH_LOG.md` |
| Unverified ideas and speculative explanations | `HYPOTHESIS_LAB.md` |
| Human-facing orientation summary | `HUMAN_BRIEF.md` |
| Fast session resume checkpoint | `RECOVERY_NOTES.md` |
| File roles, read order, ignore rules | `CONTEXT_MANIFEST.md` and `DOCS_GUIDE.md` |

## Canonical memory rule

The canonical memory lives in version-controlled markdown files in the repository.
Tool-specific memory features may help execution, but they must not be treated as the only source of truth.

Use:

- `README.md` as the entry point
- `CURRENT_STATE.md` for current trusted assumptions
- `ROADMAP.md` for future intended work
- `DECISION_LOG.md` for adopted, rejected, or deferred decisions
- `RESEARCH_LOG.md` for tests, investigation, observations, and evidence
- `HYPOTHESIS_LAB.md` for unverified ideas and emerging hypotheses
- `HUMAN_BRIEF.md` for fast human orientation
- `RECOVERY_NOTES.md` for restart checkpoints

If the repository also uses `AGENTS.md`, `CLAUDE.md`, or similar tool-facing guidance, keep those files short and point them to these canonical docs instead of duplicating project memory there.

## Default read order

When resuming or migrating a project, read in this order unless `CONTEXT_MANIFEST.md` says otherwise:

1. `CONTEXT_MANIFEST.md`
2. latest entry in `RECOVERY_NOTES.md`
3. `HUMAN_BRIEF.md`
4. `CURRENT_STATE.md`
5. `ROADMAP.md`
6. latest relevant entries in `DECISION_LOG.md`
7. latest relevant entries in `RESEARCH_LOG.md`
8. `HYPOTHESIS_LAB.md`
9. `DOCS_GUIDE.md` when routing or updating docs is unclear

If `CONTEXT_MANIFEST.md` is missing, use the default read order above and recommend creating one.

## Ignore rules

Before reading a repository or workspace, avoid obvious noise unless the user specifically asks for it:

- `.git/`, `.hg/`, `.svn/`
- `.cache/`, `cache/`, `tmp/`, `.tmp/`, `__pycache__/`
- generated logs unless the task is log analysis: `logs/`, `*.log`, `*.jsonl`
- build artifacts: `dist/`, `build/`, `.next/`, `target/`, `node_modules/`
- generated exports or run folders
- private data folders unless the user explicitly asks and access is appropriate

Use `.contextignore` if present. If a workspace has many generated files and no ignore policy, recommend adding one.

## Update routing rules

When updating memory, first classify the new material.

### Write to `CURRENT_STATE.md` when

- a fact, constraint, behavior, or rule is currently true
- a prior truth has changed or been retired
- future readers should rely on it without reconstructing history

Do not place untested claims here. If the claim is inferred but not verified, put it in `HYPOTHESIS_LAB.md` or `RESEARCH_LOG.md` with uncertainty.

### Write to `ROADMAP.md` when

- a future task, milestone, priority, or blocker changes
- something moves from idea to planned work
- something is deferred or dropped from near-term execution

A roadmap item is intent, not proof.

### Write to `DECISION_LOG.md` when

- a meaningful choice is made
- alternatives were considered
- a failure or discovery changes direction
- future readers may ask “why did we do this?”

Each decision should include context, alternatives, rationale, risks, and revisit conditions.

### Write to `RESEARCH_LOG.md` when

- an experiment, investigation, test, literature review, source check, or observation happened
- evidence changed confidence in a hypothesis
- a null result or failed attempt matters

Keep methods, inputs, results, interpretation, confidence, and limitations together.

### Write to `HYPOTHESIS_LAB.md` when

- an idea is plausible but not confirmed
- a hunch, possible mechanism, or experiment proposal should be preserved
- something should be tested before being promoted
- the user expresses a new idea, discomfort, possibility, half-formed thought, or question worth revisiting

Structure `HYPOTHESIS_LAB.md` into:

#### Raw sparks
Low-commitment captures. These may be vague, incomplete, or speculative.

#### Working hypotheses
Ideas that have recurring relevance, clearer structure, or a defined next step.

Do not require the human to explicitly ask for logging.
Prefer over-capturing in `HYPOTHESIS_LAB.md` over losing potentially valuable ideas.

### Write to `HUMAN_BRIEF.md` when

- a human needs a fast orientation to decide what to do
- the current goal, main blocker, main risk, or next decision changes
- the project should be explainable without reading all logs

Review `HUMAN_BRIEF.md` when any of the following occur, and update it only if the human-facing picture changed:

- a `DECISION_LOG.md` entry changes direction, priority, risk, tracked threads, or required human decisions
- a blocker is added, removed, or reprioritized in `ROADMAP.md`
- a hypothesis is promoted to `CURRENT_STATE.md`
- a `RESEARCH_LOG.md` entry changes confidence in a key assumption
- a `RECOVERY_NOTES.md` checkpoint changes the current goal, main blocker, next decision, or tracked thread status
- two or more parallel threads are active or paused and a human needs the current split

When updating, keep `HUMAN_BRIEF.md` short. It should summarize what matters for human judgment, not duplicate proof, history, or detailed methods.

At the top, maintain `## Tracked threads` so parallel work is visible at a glance. Each thread should state: name, status, next action or blocker, and the canonical source file.

This file is a summary layer, not the canonical proof layer.

### Write to `RECOVERY_NOTES.md` when

- a session ends
- work might be interrupted
- the next model or person needs to continue quickly

Keep this short and newest-first. It should answer: what changed, what is true now, what is blocked, what to do next, and which canonical docs to trust.

## Conflict rules

When files disagree, do not silently merge them.

Use this priority order for current-state questions:

1. explicit latest entry in `CURRENT_STATE.md`
2. latest relevant dated entry in `DECISION_LOG.md`
3. latest relevant dated entry in `RESEARCH_LOG.md`
4. latest entry in `RECOVERY_NOTES.md`
5. `HUMAN_BRIEF.md`
6. `ROADMAP.md`
7. `HYPOTHESIS_LAB.md`

Then report the conflict and propose a patch.

Important distinctions:

- `CURRENT_STATE.md` describes what is true now.
- `DECISION_LOG.md` explains why a choice was made.
- `RESEARCH_LOG.md` records evidence and interpretation.
- `ROADMAP.md` says what is planned.
- `HYPOTHESIS_LAB.md` is never truth by itself.
- `RECOVERY_NOTES.md` tells where to resume but is not the full source of truth.

## Promotion rules

Do not promote anything directly from `HYPOTHESIS_LAB.md` to `CURRENT_STATE.md`.

Promotion to `CURRENT_STATE.md` requires at least one of:

- evidence, observation, comparison, or test results recorded in `RESEARCH_LOG.md`
- an explicit operating decision recorded in `DECISION_LOG.md`
- a clearly stated user decision
- a cited external source when the claim depends on external facts

Only promote an item to `CURRENT_STATE.md` when all of the following are true:

- the claim is clear enough to be stated as a stable working assumption
- the source file is traceable
- the item is worth using as a future conversational or project assumption
- the item has a `revisit_when` condition
- the item is not dominated by unresolved objections

When promoting, update the hypothesis status to `promoted` and link the new canonical location.

## State types inside `CURRENT_STATE.md`

Divide `CURRENT_STATE.md` into:

### Stable facts
Things supported by evidence and safe to treat as current truth.

### Active operating decisions
Current workflow rules or adopted operating assumptions.

### Current context
Current priority, major blocker, and near-term direction.
These may change more often and should be reviewed regularly.

## Output modes

Choose the mode that matches the user’s task.

### Resume mode

Return:

- current goal
- last completed step
- confirmed current truth
- active blockers
- next recommended action
- files trusted
- conflicts or uncertainty

### Update-memory mode

Return either:

- patch-ready sections for each file that should change, or
- a clear statement that no canonical doc should change yet

### Handoff mode

Return:

- current confirmed state
- current goal
- last completed work
- key decisions and rationale
- recent research evidence
- active hypotheses
- next work
- risks and unresolved questions
- privacy omissions
- files to read first

### Audit mode

Evaluate:

- missing canonical files
- overloaded README risk
- speculative language in `CURRENT_STATE.md`
- stale `HUMAN_BRIEF.md`
- missing ignore rules
- likely duplication or unclear ownership between files

## End-of-task behavior

At meaningful stopping points, the AI should:

1. update `RECOVERY_NOTES.md`
2. route any new ideas into `HYPOTHESIS_LAB.md`
3. record decisions in `DECISION_LOG.md` if a decision was made
4. record evidence in `RESEARCH_LOG.md` if research or testing occurred
5. review whether `CURRENT_STATE.md` changed
6. review whether `HUMAN_BRIEF.md` needs refresh

Do not duplicate the same content across files unless a short summary is necessary for navigation.
