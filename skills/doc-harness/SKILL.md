---
name: doc-harness
description: "Document-based project control for AI-human collaboration. Use '/doc-harness init' to create a status documentation system for any project (new or existing), or '/doc-harness check' to audit documentation health and reflect on working principles. Keeps projects organized, principles enforced, and information persistent across context resets."
---

# Doc Harness — Document-Based Project Control

Doc Harness creates and maintains a structured documentation system for any project, enabling any AI agent or human collaborator to understand and resume project work purely from reading files — no external memory needed.

**Repository with full documentation, templates, and Chinese version**: https://github.com/cilidinezy-commits/doc-harness

## Commands

### `/doc-harness init [project-name] [description]`

Creates 5 documents in the current directory:

| Document | Role |
|----------|------|
| **CLAUDE.md** | Project entry point — overview, recovery chain, iron rules, embedded operational rules |
| **CURRENT_STATUS.md** | Active state — recent history, current work detail, next steps, working principles |
| **FILE_INDEX.md** | File catalog organized by category |
| **WORKLOG.md** | Permanent work history (append-only) |
| **DOC_HARNESS_SPEC.md** | Complete specification (reference) |

**How to use**: Just say "set up project documentation" or "create a status doc system for this project." The agent will ask about your project and create tailored documents. Works for new projects and projects already in progress.

**Information gathering**: Extract project details from conversation context first. For anything unclear, ask the user — don't guess. Required: project name, description, first phase name, first task.

### `/doc-harness check`

Runs a two-part audit:

**Part 1 — File Health**: Checks all 4 core documents exist, CURRENT_STATUS is fresh, FILE_INDEX matches actual files on disk, WORKLOG TOC is consistent, car body isn't too long.

**Part 2 — Principle Reflection**: Reads the project's iron rules and working principles, prompts honest reflection: "Am I following these?" Includes a "Write It Down" check for unsaved information.

**How to use**: Just say "check the status documentation" or "run a doc-harness check in the background."

## Core Principle: "Write It Down or Lose It"

All information in context is temporary. Important information must be **written to a file** and **registered in FILE_INDEX**. Not written = lost. Not registered = undiscoverable = effectively lost.

## CURRENT_STATUS Structure ("Moving Car")

| Section | What's in it |
|---------|-------------|
| **Recent History** (Tire Tracks) | 2-3 summaries of recently completed phases |
| **Current Phase Detail** (Car Body) | Full record of active work — steps, files, decisions |
| **Next Steps** (Headlights) | Immediate actions + future plans |
| **Phase Principles** (Driving Manual) | Working guidelines for this phase |

When a phase ends: car body → archived to WORKLOG, compressed to tire track summary, cleared for new phase.

## Key Rules for Agents

**Session start**: Read CLAUDE.md → CURRENT_STATUS → continue working.

**During work**:
- Complete a meaningful step → update CURRENT_STATUS car body
- Create a file → register in FILE_INDEX + record in CURRENT_STATUS
- Important insight or decision → save to file immediately (Write It Down!)

**Session end checklist**:
- [ ] CURRENT_STATUS car body reflects all work?
- [ ] Next steps accurate?
- [ ] Dates refreshed?
- [ ] New files registered in FILE_INDEX?
- [ ] Anything unsaved in context? → Write it down!

**Phase transition** (5 steps, strictly in order):
1. Copy car body to WORKLOG (protect data first)
2. Compress to tire track summary in CURRENT_STATUS
3. Remove oldest tire track if >3
4. Clear car body for new phase; update driving manual
5. Update CLAUDE.md status; update WORKLOG TOC

## License

MIT — https://github.com/cilidinezy-commits/doc-harness
