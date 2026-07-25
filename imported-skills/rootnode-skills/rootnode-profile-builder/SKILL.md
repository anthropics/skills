---
name: rootnode-profile-builder
description: >-
  Conversational profile builder. Produces validated JSON config files for
  any rootnode Skill that consumes profile-shaped configuration (handoff
  trigger check, mode router, critic gate, future Skills). Reads a target
  JSON Schema (draft-07), conducts a progressive-depth interview using
  plain-language questions, validates answers, and writes the resulting
  JSON to a destination path. Schema-agnostic — works with any profile
  schema conforming to draft-07. Use when a user needs to create, clone,
  or revise a profile and you do not want them hand-editing JSON. Trigger
  on: "build me a profile," "create a profile," "I need a profile for X,"
  "set up my profile," "edit my profile," "clone the X profile," "walk me
  through making a profile." Do NOT use when the user already has a
  working profile and only wants to invoke the consuming Skill, when the
  schema cannot be located, or for non-profile JSON config work. Always
  validate before writing.
license: Apache-2.0
metadata:
  author: rootnode
  version: "1.0.2"
  original-source: "root.node design 2026 — runtime layer (gates, router, profile builder)"
  companion-files: "examples/sample-interview-flow.md, references/schema-walking-patterns.md, references/common-schema-shapes.md, references/troubleshooting.md"
  changelog: "1.0.2 (2026-05-05): Brand-strip patch per Phase 27/28 methodology absorption. Six SKILL.md cchq references replaced with rootnode framing (description, body lines 29, 31, 154, 157); default output path convention rewritten from ~/.cchq/profiles/ to ~/.rootnode/profiles/ (line 53); four corresponding path references updated in examples/sample-interview-flow.md (lines 135, 136, 146, 147). Behavior identical to 1.0.1 — no methodology, schema, or workflow changes. 1.0.1 (2026-05-01): Structural patch to align with rootnode authoring convention. Added references/ folder with three on-demand-loaded files (schema-walking-patterns, common-schema-shapes, troubleshooting). SKILL.md body slimmed via content extraction; behavior identical to 1.0. Deployment target: Claude.ai Project (CP) side of CP/CC split."
  discipline_post: phase-30
---

# Profile Builder

Conversational interview that produces validated JSON profile files for any rootnode Skill. Solves the "users won't hand-edit JSON" problem by walking them through one plain-language question at a time, then writing a validated file.

The Skill is **schema-agnostic by design**. It does not encode knowledge of any specific profile schema. It reads the target schema, parses required fields and constraints, generates the interview from the schema, validates answers against the schema, and writes the result. This is what makes the Skill portable across the entire rootnode runtime layer — every Skill that takes profile config uses the same builder, no per-Skill builder forks.

## Important

**Progressive depth, not interrogation.** Walk the user through 5-7 substantive questions that determine the profile's shape. Set sensible defaults for everything else. Offer "review and customize defaults" only at the end for users who want it. Never ask 30 questions in sequence — produces bad answers and exhausts users.

**Plain language, never machine names.** Translate every enum option into a meaningful description. "Choose `threshold_rule`: `all_must_pass` / `min_count` / `weighted`" is wrong. "How strict should this be? (a) Every condition must pass — strictest, for unattended runs. (b) Most conditions must pass — balanced. (c) Weight conditions by importance — advanced." is right.

**Validate before writing.** Run the schema validation against the assembled profile before any file is created. If validation fails, identify the failing constraint, ask the missing question, retry. Never write an invalid file.

**Show summary, not JSON, before saving.** Final confirmation step shows a human-readable summary of choices made. The JSON is an implementation detail — the user shouldn't have to read it to verify the profile.

**One file per profile.** No bundling. No multi-profile artifacts. Each profile is a discrete file the user can move, clone, edit, or share.

---

## Workflow

### Step 1 — Locate inputs

Required:
- **Target schema** — JSON Schema draft-07 file describing the profile shape. Caller provides path or content. If the user names a Skill ("build me a handoff profile"), look for the schema in that Skill's installed `schema/` directory.
- **Output destination** — filesystem path where the profile JSON will be written. Defaults to `~/.rootnode/profiles/{schema-name}/{profile-name}.json` if not specified by the caller.

Optional:
- **Starter profile** — existing profile to clone and modify. When provided, the interview becomes a delta walk ("here's what's set, what do you want to change?") rather than a full interview.
- **Profile name** — pre-supplied name. If absent, ask first.

If schema is not provided or cannot be located, halt and ask the user. Do not attempt to write a profile against an unknown schema.

### Step 2 — Parse the schema

Extract:
- Required fields (drives mandatory questions)
- Field types and constraints (drives input validation per question)
- Enum values for constrained fields (drives multiple-choice questions)
- Conditional dependencies (e.g., `if threshold_rule = weighted, then condition_weights required`) — drives follow-up question logic
- Field descriptions (used as question prompts when no plain-language override is provided)

If the schema includes `schema_version`, use the current value when writing the profile.

For per-construct semantics (how each JSON Schema construct should drive interview behavior — required vs optional, enum walking, polymorphic types like oneOf/anyOf, arrays, conditional dependencies, nested objects), consult `references/schema-walking-patterns.md`. For a JSON Schema draft-07 quick reference (type constructs, validation constraints, composition, $ref resolution, annotations, and constructs the builder cannot handle), consult `references/common-schema-shapes.md`.

### Step 3 — Plan the interview

Group questions by substantive impact:

**Tier 1 — Identity & purpose (always asked):**
- Profile name (validate against schema's name pattern)
- One-sentence description: "When does this profile apply?"

**Tier 2 — Substantive shape (5-7 questions max):**
- One question per major branching decision in the schema
- Use enums to drive multiple-choice
- Translate enum values into plain-language descriptions of what they mean operationally

**Tier 3 — Numeric tuning (defaults offered):**
- Bounded numeric fields (margins, thresholds, counts)
- Present a sensible default with rationale, accept override
- Format: "Suggested: X (because Y). Accept, or enter your own value:"

**Tier 4 — Optional details (skipped unless requested):**
- Free-text fields (notes, descriptions beyond the one-sentence purpose)
- Optional fields the schema doesn't require
- Show: "Want to add notes / advanced settings? (y/n)"

**Conditional follow-ups:** When an answer triggers a dependent requirement (e.g., choosing `weighted` threshold requires per-condition weights), insert the dependent questions immediately after, in plain language.

### Step 4 — Conduct the interview

Ask questions one at a time. Wait for the user's answer. Validate each answer against the schema constraint for that field. If invalid, explain why in plain language and re-ask. Do not bury validation errors in stack traces.

When the user gives a clearly informal answer (e.g., "yeah" to a numeric prompt), interpret charitably and confirm: "I'll take that as accepting the default of X — confirm?"

When the user is uncertain ("I don't know what to pick"), provide a recommendation with one-sentence rationale based on the schema's field description and the profile's stated purpose.

### Step 5 — Show summary and confirm

Before writing, present a plain-text summary:

```
Profile summary: {name}

Purpose: {description}

Behavior:
- {plain-language summary of each substantive choice}

Numeric settings:
- {field}: {value} ({explanation if non-default})

Will be saved to: {destination path}

Confirm save? (y/n/edit)
```

If user chooses `edit`, return to the relevant question. If `n`, ask whether to abandon or save as draft. If `y`, proceed.

### Step 6 — Validate and write

Final validation pass against the schema. If validation fails at this stage (should be rare given per-question validation), do not write — surface the specific failing constraint and the question that needs revision.

On successful validation, write the JSON file (pretty-printed, 2-space indent) to the destination path. Confirm to the user with the absolute path.

Optionally generate a companion `{profile-name}.notes.md` containing:
- Date created, schema version
- One-paragraph summary of the profile's intent
- Key choices made and why (drawn from interview answers)
- Suggested re-evaluation triggers (e.g., "Reconsider this profile if your daily token budget changes by more than 30%")

The notes file is for audit trail and for sharing patterns with other users. Skip if the user declines.

---

## Examples

A complete sample interview flow showing the builder building a handoff-trigger-check profile from scratch, with full question-and-answer sequences, is in `examples/sample-interview-flow.md`. Three additional walkthrough patterns — building from scratch, cloning an existing profile (delta walk), and handling user uncertainty — are in `references/schema-walking-patterns.md` (in the "Worked Walkthrough Examples" section). Consult either file when modeling a new Skill's profile schema against a tested interview pattern.

---

## When to Use This Skill

Use this Skill when:
- A user needs to create a new profile config for any rootnode Skill that consumes profile-shaped configuration
- A user wants to clone and modify an existing profile
- A user needs to revise a profile after a schema update or changed circumstances
- A user is being onboarded to a rootnode Skill that requires a profile and doesn't have one yet

Do NOT use this Skill when:
- The user already has a working profile and only wants to invoke the consuming Skill (call the consuming Skill directly)
- No target schema has been provided or can be located (halt and request)
- The user is editing arbitrary JSON config that isn't profile-shaped (different problem; use a JSON editor)
- The user explicitly wants to hand-edit JSON (respect that; provide schema reference and exit)

---

## Troubleshooting

Common failure modes and resolution guidance — covering schema and input issues (schema not found, non-draft-07 schemas, unrecognized fields, custom keywords), interview behavior issues (skipping questions, advanced control, confusing prompts, conditional follow-ups not firing), validation issues (final-pass validation failures, user disagrees with constraint, consuming Skill rejects builder output), output issues (path not writable, cancel-at-summary draft handling, overwrite handling), and user experience issues (uncertainty handling, informal answers, interview fatigue, hand-edit pivot) — are in `references/troubleshooting.md`. Consult that file when the interview is producing unexpected behavior or the resulting profile doesn't match what the user intended.
