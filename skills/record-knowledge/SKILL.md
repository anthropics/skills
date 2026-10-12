---
name: record-knowledge
description: >-
  Record tacit knowledge — quirks, pitfalls, dependencies, decisions, root causes — as tagged
  Markdown entries in `.claude/knowledge/entries/`. Use this skill whenever discoveries are made
  during work, when the user shares undocumented system behavior, or at plan completion to capture
  lessons learned. Also use when Claude Code makes a mistake pointed out by the user — record what
  happened, why it was wrong, and what to do next time.
license: MIT
allowed-tools: Read, Grep, Glob, Edit, Write
---

# Record Knowledge

## Goal

Capture tacit knowledge discovered during work and make it available for future sessions.

## When to Reference
- **New session start**: Search `.claude/knowledge/entries/` for active entries related to the current task before starting work
- **Progress update**: Check if related entries need updating based on new discoveries
- Not needed when resuming a session (context is already preserved)

## When to Record

- Undocumented behavior, quirks, or pitfalls
- Hardware/service characteristics shared by the user
- Dependencies or coupled settings discovered during configuration
- Decision rationale (why a particular approach was chosen)
- Root causes and fixes found during troubleshooting
- **Claude Code's own mistakes and prevention measures** — errors pointed out by the user, incorrect output, tool misuse, etc. Record specifically: what happened, why it was wrong, and what to do next time. Tag with `#pitfall`

## Setup

Copy `assets/knowledge-CLAUDE.md` to `.claude/knowledge/CLAUDE.md`:

```bash
mkdir -p .claude/knowledge/entries
cp assets/knowledge-CLAUDE.md .claude/knowledge/CLAUDE.md
```

This creates the tag registry and search reference used by the skill.

## Recording Flow

1. Create `.claude/knowledge/entries/YYYYMMDD-HHMMSS-author-slug.md` with YAML frontmatter
2. For new discoveries without enough detail yet, write a temporary note in the working directory and convert to an entry later
3. Do NOT add links to subdirectory `CLAUDE.md` files — use tag search to find entries instead
4. Claude Code acts autonomously — create and edit entries without asking for user confirmation

## Entry Location

- `.claude/knowledge/entries/YYYYMMDD-HHMMSS-author-slug.md` — one file per entry
- Timestamp prefix ensures chronological ordering and collision avoidance
- Author field uses your Git hosting platform account name (without `@`)
- Slug is descriptive kebab-case
- Example: `20260302-143052-alice-docker-compose-port-conflict.md`
- Existing entries without timestamp prefix remain as-is (no rename required)

## Entry Format (YAML Frontmatter)

```markdown
---
title: <title>
author: "@<username>"
created: YYYY-MM-DD
status: active | deprecated
tags: "#tag1 #tag2 ..."
---

<body — concrete facts, procedures, code examples, etc.>

- ref: [display text](URL or relative path)
- see: [related entry title](related-entry-slug.md) — relationship description
```

- Entry body has no size constraint — include command examples, error messages, config values, decision context as needed

### Tag Guidelines

- Claude Code assigns tags autonomously for optimal searchability
- Naming: lowercase kebab-case with `#` prefix (e.g., `#docker`, `#typescript`, `#pitfall`)
- Add new tags freely as needed
- Check the tag registry in `.claude/knowledge/CLAUDE.md` before creating new tags to avoid duplicates

#### Similarity Check (on every entry creation)

Before assigning tags to a new entry, scan the tag registry for near-duplicates:

- **Singular/plural**: `#backup` vs `#backups` → use the existing form
- **Abbreviation/full**: `#k8s` vs `#kubernetes` → use the existing form
- **Synonym**: `#error` vs `#bug` → use the existing form
- **Substring overlap**: `#windows-service` vs `#win-service` → use the existing form

If a near-duplicate is found, reuse the existing tag. Do not create a new one.

### ref / see Link Format

- Use Markdown links for URLs and repo paths (clickable in your Git hosting platform's web UI)
  - External: `- ref: [title](https://example.com/...)`
  - In-repo: `- ref: [path](../../../relative-path)` (relative from `.claude/knowledge/entries/`)

### see Links (Synapse Formation Between Entries)

- Add `see:` links to related entries when creating or editing an entry
- Within `entries/`, use filename only: `- see: [title](slug.md) — relationship`
- Describe the relationship briefly after `—` (e.g., "another port conflict", "prerequisite step")
- Relevance criteria:
  - **Sequential steps**: procedure step dependencies, workflow stages
  - **Same technology, different pitfalls**: multiple gotchas for one tool
  - **Prerequisite → application**: setup steps → usage caveats
  - **Design decision ↔ rationale**: architecture choice ↔ supporting evidence
- Bidirectional links by default (if A → B, add B → A too)
- When adding a new entry, update related existing entries with see links

## Status Definitions

| Status | Meaning | Claude Code Behavior |
|--------|---------|---------------------|
| `active` | Current, valid knowledge | Use as basis for decisions |
| `deprecated` | Obsolete or proven incorrect | Do not reference; use only for historical context |

## Amendment Rules

- Entries are **mutable** — edit in place (git tracks change history)
  - Adding info, corrections, supplementary examples → edit directly
  - Use `git log entries/<slug>.md` to review change history
- Use `deprecated` only when knowledge is genuinely obsolete
  - Example: service decommissioned, fundamental spec change, "should no longer be referenced"

## Procedure

1. Extract knowledge from user input or work discoveries
2. Read the tag registry in `.claude/knowledge/CLAUDE.md`
3. Select tags — reuse existing tags; check for near-duplicates before creating any new tag
4. Create `.claude/knowledge/entries/YYYYMMDD-HHMMSS-author-slug.md` (or edit existing entry)
5. If a new tag was created, add it to the tag registry
6. Add see links to related existing entries if applicable
7. Briefly notify the user what was recorded (no confirmation needed beforehand)
