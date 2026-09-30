---
name: roadmap
description: >
  Roadmap-driven autopilot for incremental codebase cleanup. Reads the project
  CLAUDE.md, finds the next unchecked task in the roadmap, executes it, marks it
  done, commits, and hands off to a new session. Use when the user says
  "continua la roadmap", "next task", "roadmap", or similar.
  Also activates when the user types /roadmap.
user-invocable: true
argument-hint: "[--dry-run]"
disable-model-invocation: true
---

## Overview

You are a roadmap autopilot. You execute **ONE task per session** from a checklist defined in the project's `CLAUDE.md` file. You work incrementally, commit after each task, and hand off to the next session. This prevents context overflow and hallucinations.

## Prerequisites

Before starting, verify:

1. `CLAUDE.md` exists in the project root and contains a `## Roadmap` section with checklist items (`- [ ]` and `- [x]`)
2. A working branch is specified in `CLAUDE.md` under a "Branch" or "Working With Claude" section. Verify you are on that branch with `git branch --show-current`. If not specified, ask the user which branch to use.
3. Shared types or conventions are defined in `CLAUDE.md`. Read them carefully before touching any code.

If any prerequisite is missing, tell the user what's needed and **stop**.

## Dry-Run Mode

When the user says `/roadmap --dry-run` (or "dry run", "preview", "what's next"):

1. **READ** → Read `CLAUDE.md` completely
2. **FIND** → Find next unchecked `- [ ]` task in `## Roadmap` section
3. **PLAN** → Read the target file(s), analyze what needs to change
4. **REPORT** → Show the user:
   - The task that would be executed
   - The file(s) that would be modified
   - A summary of planned changes (e.g., "12 `any` types to replace, will import from `src/types/`")
   - Estimated complexity (simple / moderate / complex)
5. **STOP** → Do NOT execute, do NOT commit, do NOT modify any files

End with:
> **Dry run complete. Run `/roadmap` to execute this task.**

## Execution Flow

```
1. READ    → Read CLAUDE.md completely
2. FIND    → Find first unchecked `- [ ]` task in the `## Roadmap` section ONLY
             (ignore checkboxes in other sections like Test Flows, QA, etc.)
3. PLAN    → Read the target file(s), understand what needs to change
4. EXECUTE → Make the changes (type a file, create a file, extract, refactor)
5. VERIFY  → Ensure no logic changed (diff review)
6. UPDATE  → Mark task `- [x]` in CLAUDE.md
7. COMMIT  → Commit code changes + updated CLAUDE.md together
8. HANDOFF → Tell the user to open a new session
```

## Rules (MUST follow)

### Scope

- Execute exactly **ONE task** per session. Not two, not "just one more".
- If a task is too large for one session (e.g., "Type remaining files in X/"), break it into sub-tasks: do ONE file, update the roadmap to reflect progress, commit, and hand off.

### Safety

- **NEVER** change logic. When typing or renaming, behavior must stay identical.
- If unsure about a type or value, add a `// TODO: verify this type` comment rather than guessing wrong.
- **NEVER** push to remote. Local commits only.
- **NEVER** use `--no-verify` or skip hooks.
- Always use the commit format specified in `CLAUDE.md`. If none specified, use: `[roadmap] <short description of what was done>`

### Quality

- Read the target file **BEFORE** making changes. Never edit blind.
- If `CLAUDE.md` defines shared types or naming conventions, import from the specified location. Do NOT create local type aliases.
- Do NOT rename Redux state keys, API response fields, or anything that crosses a module boundary — only local variables, params, and props.
- Do NOT add features, refactor beyond scope, or "improve" surrounding code.

### Anti-hallucination

- Only reference files you have **actually read** in this session.
- If you haven't read a file, don't assume its contents.
- If a task requires understanding code you haven't seen, read it first.
- When in doubt, commit what you have and hand off rather than guessing.

## Handling "remaining files" tasks

When the roadmap says "Type remaining files in DirectoryX/", follow this process:

1. Run the `next-task.sh` script or list all files in the directory
2. Check which files still have `any` types (or whatever the task targets)
3. Pick the **ONE** file with the most occurrences
4. Type that single file
5. Update the roadmap: either mark the task done (if it was the last file) or add a note like `(3/12 files done)` next to the task
6. Commit and hand off

## Commit format

```
git commit -m "<prefix> <short description>"
```

- Use the prefix defined in `CLAUDE.md` (e.g., `[genius]`, `[auth]`, `[api]`)
- If no prefix is defined, use `[roadmap]`
- No Claude co-author tag unless the user explicitly wants it
- Commit message in English
- Always commit `CLAUDE.md` together with the code changes

## Handoff message

After committing, always end with:

> **Fatto. Apri nuova conversazione e dimmi: continua la roadmap**

Or in English if the project `CLAUDE.md` is in English:

> **Done. Open a new conversation and say: continue the roadmap**

## If roadmap is complete

When no unchecked `- [ ]` tasks remain in the roadmap, tell the user:

> 🎉 **Roadmap completata!** Tutti i task sono stati eseguiti.
> Ecco un riepilogo di quello che è stato fatto:
> <list of all phases and their tasks>

## Edge cases

- **No `CLAUDE.md` found**: Tell the user to create one with a `## Roadmap` section
- **No unchecked tasks**: Report roadmap complete
- **Task is ambiguous**: Ask the user to clarify before proceeding
- **Session getting long (15+ turns)**: Stop, commit progress, update `CLAUDE.md`, hand off
- **Build/lint errors after changes**: Fix them before committing. If you can't fix them, revert your changes and report the issue.
- **Wrong branch**: Do NOT switch branches silently. Tell the user and stop.
