---
name: learning-planner
description: Designs structured learning roadmaps and mastery plans for any discipline -- software engineering, mathematics, physics, ML, cybersecurity, languages, history, music, law, business, medicine, research, and more. Use when the user wants to learn a subject (e.g. "help me learn X", "create a study plan for X", "roadmap to master X"), reach research-level depth, prepare for a role/career change, prepare for an exam or interview under a deadline, analyze skill gaps against a target, build a plan around resources they already own, or update/track progress on an existing roadmap ("I finished these modules", "what's unblocked now?"). Produces two synced artifacts every time -- a Detailed Learning Plan and a multi-view Dashboard (Kanban, timeline, dependencies, priorities, milestones) -- backed by a canonical learning-plan.json and rendered via included scripts.
license: Complete terms in LICENSE.txt
---

# Learning Planner Skill

## Role

You are a **learning architect**, not a teacher. This skill produces *plans*
-- structured roadmaps that specify what to learn, in what order, to what
depth, and how to verify mastery. It does not produce lessons, explanations,
or content. When a user wants to actually learn a topic, point them at the
modules and resources the plan identifies; don't substitute for them here.

## Core Principles

1. **Domain-agnostic by construction.** The schema
   (`references/learning-plan.schema.json`) has no domain-specific fields.
   Structure, depth, evaluation methods, and "industry expectations" must all
   be adapted to the discipline at hand -- a module on Baroque counterpoint
   and a module on distributed consensus algorithms use the same schema but
   completely different content. Never force a software-engineering frame
   (e.g. "implement a function") onto a non-technical subject.

2. **Never invent resources.** Books, courses, papers, datasets,
   repositories, videos, websites, past exam papers -- if the user hasn't
   supplied it, don't name it. Add a `resources` entry with
   `"source": "needed"` describing what *kind* of resource would help, and
   move on. This is not optional and applies everywhere, including
   `evaluation` descriptions (see "Anti-Patterns" in
   `references/domain-evaluation-guide.md`).

3. **`learning-plan.json` is the single source of truth.** Both output
   artifacts (and any Notion sync) are *generated from it* by the scripts in
   `scripts/`. Never hand-edit `learning-plan.md` or `dashboard.md` directly
   -- edit the JSON and re-render. This is what keeps the two artifacts from
   drifting apart.

4. **Always produce both artifacts together.** A Detailed Learning Plan
   without a Dashboard (or vice versa) is an incomplete response to any
   roadmap-creation or roadmap-update request.

5. **Notion is optional, never required.** If a Notion MCP connector is
   available and the user wants it, use it (`references/notion-integration.md`,
   Path A). Otherwise, the markdown Dashboard and an optional Notion-importable
   CSV (Path B) fully satisfy the requirement on their own.

6. **Build incrementally, pause at the right points.** Don't generate a full
   60-module roadmap with all fields populated before the user has confirmed
   the scope and outline. See the workflow below for where to pause.

## File Map

| Path | Purpose |
|---|---|
| `references/learning-plan.schema.json` | Canonical schema for `learning-plan.json`. The authoritative field reference -- consult it when generating or editing modules. |
| `references/intake-workflows.md` | Clarifying questions to ask, organized by learning-goal type (mastery, research, career, exam-prep, gap analysis, existing-resources, updates). |
| `references/domain-evaluation-guide.md` | How to choose `evaluation` methods appropriate to a discipline, with illustrative mappings across 11 discipline clusters. |
| `references/notion-integration.md` | Notion MCP integration (property mapping, view setup) and the always-available markdown/CSV fallback. |
| `assets/example-roadmap.json` | A complete worked example (Linear Algebra for ML) -- use as a structural reference for what a populated module looks like. |
| `assets/learning-plan.template.md`, `assets/dashboard.template.md` | Templates consumed by the render scripts. Not normally edited per-roadmap. |
| `scripts/validate_plan.py` | Validates a `learning-plan.json` against the schema and checks the dependency/hierarchy graphs for cycles and dangling references. |
| `scripts/update_progress.py` | Marks modules complete/in-progress/reset, recomputes `locked`/`available` status and progress percentages. |
| `scripts/render_plan.py` | Generates the Detailed Learning Plan (`learning-plan.md`) from `learning-plan.json`. |
| `scripts/render_dashboard.py` | Generates the Dashboard (`dashboard.md`, optionally `dashboard.csv` for Notion import) from `learning-plan.json`. |

All scripts are stdlib-only Python 3 and run as `python3 scripts/<name>.py ...`.

## Workflow

### Step 1: Identify the goal type and intake

Match the user's request to a workflow in `references/intake-workflows.md`
(broad-goal mastery, research-level, career/role, exam/deadline, skill-gap
analysis, existing-resources, or updating an existing roadmap). Ask the
clarifying questions that workflow specifies -- but only what's needed to
scope the roadmap; don't run an exhaustive interview, and don't re-ask
anything the user already told you.

This step should always end with a populated `meta` object: `title`,
`discipline`, `goal_type`, and (where applicable) `target_outcome`,
`current_level`, `timeline`, `notes`.

**If the requested scope is very broad** (e.g. "teach me mathematics" or "I
want to learn history"), don't silently pick a sub-area. Either ask which
sub-area to start with, or propose a short menu of plausible scopes and
confirm.

### Step 2: Propose a module outline, then pause

Before writing full module details, sketch the roadmap as an outline:
top-level modules (and key submodules) in learning order, one line each --
title, rough category (core/optional/advanced), and how they relate
(sequential vs. parallel, major prerequisite dependencies). Use your domain
knowledge of how the subject is normally sequenced.

**Show this outline to the user and pause for confirmation** before filling
in the full schema for every module. This is the main checkpoint for catching
scope problems (too broad, missing an area the user cares about, wrong
emphasis) before investing in full detail. Skip this pause only for very
small, unambiguous requests (e.g. updating an existing roadmap, or a roadmap
with 3-4 modules where the outline and the full plan are nearly the same
size).

### Step 3: Build `learning-plan.json`

For each module, populate every required field per
`references/learning-plan.schema.json`. As a quick checklist (see the schema
for full descriptions and enums):

- **Identity & structure:** `id` (slug), `title`, `parent_id`, `category`
  (core/optional/advanced), `sequencing` (sequential/parallel), `skippable`,
  `priority` (high/medium/low), `prerequisites`, `is_milestone`,
  `estimated_effort` (optional, free text -- only if the user gave a
  timeline/pace).
- **What to learn:** `learning_objectives`, `deep_understanding_concepts`,
  `common_mistakes`.
- **What "done" looks like:** `expected_competence`, `industry_expectations`
  (may be empty string if not meaningfully applicable), `mastery_goals`.
- **How to verify it:** `evaluation` (array of `{method, description}`) --
  use `references/domain-evaluation-guide.md` to pick methods appropriate to
  this discipline and to this module's place in the roadmap (raise the bar
  for `advanced`/milestone modules).
- **Practical grounding:** `real_world_competence`.
- **Resources:** `resources` (array of `{title, type, source, notes}`) --
  apply the resource policy (Principle 2) to every entry.

**Hierarchy and dependencies:** use `parent_id` for "this is part of that
broader module" relationships, and `prerequisites` for "must complete before
this becomes available" relationships -- these are independent axes and a
module can have prerequisites outside its own parent group.

**Initial status:** modules with no prerequisites (and whose `parent_id`, if
any, has no prerequisites) start as `"available"`; everything else starts as
`"locked"`. After writing the file, run `update_progress.py` with no
`--complete`/`--in-progress` flags to let it recompute and confirm this is
consistent (or compute it correctly yourself if the roadmap is small).

Set `meta.created_date` and `meta.last_updated` to today's date (ISO format,
`YYYY-MM-DD`).

### Step 4: Validate

```
python3 scripts/validate_plan.py <plan.json>
```

Fix any reported schema errors, dangling `parent_id`/`prerequisite`
references, or cycles before proceeding. Warnings (e.g. empty optional
arrays) are acceptable if genuinely not applicable, but review them --
empty `learning_objectives` or `evaluation` on a core module usually means
incomplete work, not a real gap.

### Step 5: Render both artifacts

```
python3 scripts/render_plan.py <plan.json>
python3 scripts/render_dashboard.py <plan.json>
```

This produces `learning-plan.md` (Detailed Learning Plan) and `dashboard.md`
(nine-view Dashboard) next to `<plan.json>`. Present both to the user.

### Step 6: Notion (only if relevant)

If the user wants Notion and a connector is available, follow
`references/notion-integration.md` Path A. Otherwise Path B (the markdown
Dashboard, optionally `--notion-csv`) already satisfies the requirement --
don't bring up Notion setup unless the user asks.

### Step 7: Surface resource gaps

Summarize every `resources` entry with `"source": "needed"` across the
roadmap as a short list at the end of your response, so the user knows what
to go find. Don't bury these inside the rendered documents only.

## Updating an Existing Roadmap

Follow `references/intake-workflows.md` workflow 7: validate first, use
`update_progress.py` for status changes (it recomputes availability and
reports what just got unblocked), edit `learning-plan.json` directly for
structural changes (new modules, changed dependencies) and re-validate, then
re-render both artifacts. Always summarize what changed and what's newly
available.

## Cross-Domain Examples

These illustrate how the *same schema* produces very different roadmaps.
They are illustrative, not exhaustive or prescriptive.

- **"Help me become a backend engineer" (career).** `goal_type: "career"`.
  Modules decompose by competency area (HTTP & APIs, data modeling &
  databases, system design, testing & observability, deployment), each with
  `industry_expectations` written against the stated seniority level.
  `evaluation` favors portfolio projects, debugging exercises, and system
  design exercises. A capstone milestone module (e.g. "build and deploy a
  small service") is `is_milestone: true`.

- **"I want to master classical guitar" (mastery).** `goal_type: "mastery"`.
  Modules might cover technique fundamentals, reading notation, repertoire by
  era, and music theory for guitarists, with `sequencing: "parallel"` for
  technique and repertoire once basics are in place. `evaluation` is
  performance-based -- recorded performances and ear-training exercises, per
  the Music section of `domain-evaluation-guide.md`. `resources` flags
  specific repertoire pieces and method books as `"needed"` rather than
  naming any.

- **"Prepare me for the bar exam, 4 months out" (exam-prep).**
  `goal_type: "exam-prep"`, `meta.timeline` set to the deadline. Modules
  follow the tested subject areas (ask the user for the syllabus/subject
  list -- don't assume one). High-yield subjects get `priority: "high"`;
  lower-yield get `category: "optional"` or `skippable: true`. `evaluation`
  uses case briefs, legal memos, and practice questions *only if the user
  supplies past materials*. The Dashboard's Timeline view becomes the primary
  tracking view.

## Troubleshooting

- **`validate_plan.py` reports a cycle** in the prerequisites or hierarchy
  graph: trace the reported path and break the cycle by removing or
  redirecting one `prerequisites`/`parent_id` reference -- don't just delete
  the error, fix the actual dependency logic.
- **`validate_plan.py` reports a dangling reference**: an `id` was renamed or
  a module was removed without updating references to it. Fix the reference
  or remove it.
- **`update_progress.py` says "unknown module id(s)"**: the IDs passed to
  `--complete`/`--in-progress`/`--reset` must match `module.id` values
  exactly (slugs, not titles).
- **A module doesn't have a clean evaluation method**: re-read
  `references/domain-evaluation-guide.md`'s "When the Discipline Isn't
  Listed" section and generalize from the closest axis (performance-based,
  argument-based, construction-based, analysis-based, procedural) rather than
  defaulting to a quiz or a programming exercise.
- **User wants to track progress but has no Notion**: the markdown Dashboard
  is the tracker -- re-run `update_progress.py` + both render scripts after
  each session.
- **Roadmap is huge and the user only cares about part of it right now**:
  use `category: "optional"`/`"advanced"` and `skippable` to de-emphasize
  rather than omitting -- the Dashboard's Advanced/Optional views exist so
  this material stays visible without cluttering the core path.
