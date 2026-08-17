---
name: plan-file-hygiene
description: Keeps working plans and scratch notes from multiplying and going stale. Before creating any PLAN.md, NOTES.md, TODO.md, or scratch markdown file, discover what already exists and update it instead of spawning a duplicate; never regenerate a shared plan file from memory; supersede old plans explicitly and archive them when their task completes. Use when starting or resuming multi-step work that tracks state in markdown files, or when a working directory has accumulated stray plan, notes, or scratch files that need consolidation.
license: Apache-2.0. Complete terms in LICENSE.txt
---

# Plan File Hygiene

Long-running agentic work tends to leave a trail: each planning or research step spawns its own `PLAN.md`, `NOTES.md`, or scratch file, and nothing ever merges, prunes, or supersedes them. Returning to the project, neither the agent nor the human can tell which plan is current.

There is a second, quieter failure mode that makes this worse: "refreshing" a plan by rewriting the whole file from what the current session remembers. When more than one writer touches a plan — a parallel session, an earlier run, a human — a whole-file rewrite silently deletes every section the current session did not know about. The file still looks healthy afterward, so the loss goes unnoticed until someone needs the missing sections.

These rules come from a production multi-writer setup where repeated plan-file losses were traced, via file version history, not to sync races but to exactly that whole-file-rewrite habit — and were eliminated by the discipline below.

## Rule 1: Discover before you create

Before creating any plan, notes, or scratch markdown file:

1. **Search for existing candidates** in the working directory (and `docs/` if present):
   - `PLAN*.md`, `*-plan.md`, `plan-*.md`
   - `NOTES*.md`, `TODO*.md`, `SCRATCH*.md`, `scratch-*.md`
   - Any markdown file at the repo root modified in the last few days
2. **Read what you find** and classify each file: *current* (this task, still accurate), *superseded* (an older plan for the same work), *stale* (task finished or abandoned), or *unrelated* (different task, leave alone).
3. **Decide**: exactly one file should be current for a given task.
   - A matching plan exists → update it in place (Rule 2). Do not create a sibling.
   - Scratch findings for a task that already has a plan file belong **in the plan file** — fold them in rather than growing a parallel notes file. Keep a separate notes file only while it serves a genuinely distinct purpose; once it overlaps the plan, merge it in and remove it.
   - No match → create one file with a predictable name: `PLAN.md` for single-task repos, or `plan-<task-slug>.md` when several tasks share the directory.

Never skip discovery because "this is just a quick scratch file" — quick scratch files are precisely what accumulates.

## Rule 2: Merge, don't spawn; append, don't regenerate

When a plan file already exists:

- **Update means: re-read, then edit.** Read the file immediately before modifying it, then make a targeted edit — add your section, update your items, correct what changed. Base the edit on what is *in the file now*, not on what you remember being there.
- **Never write the whole file from memory.** A regenerated plan contains only what the current session knows and deletes everyone else's sections. If your tooling only supports whole-file writes, do read → minimal diff → write back as one short operation, and if the file changed under you meanwhile, re-read and redo. Note that read-then-rewrite is still not race-safe: two writers can both read, then the later write erases the earlier one. When concurrent writers are a real possibility, use per-writer append-only sections (see Edge cases) — or, for a robust fix, route all writes through a single lock-protected append script.
- **Do not create version-suffixed siblings** (`PLAN-v2.md`, `PLAN-final.md`, `PLAN-new.md`). A restructured plan replaces the old one explicitly (Rule 3); anything less is an edit to the existing file.

Warning signs that you are about to clobber:

- You are writing to a plan file you have not read in this turn.
- You are "cleaning up" or "consolidating" by rewriting the file wholesale.
- Your output is noticeably **smaller** than the existing file. Plans grow until they are archived; a plan file shrinking *in place* is a red flag, not a cleanup. (Deleting a scratch file whose content you just merged elsewhere is not a shrink — the content demonstrably moved.)

## Rule 3: One current plan; supersede explicitly

Adding or updating sections in place is a targeted edit (Rule 2). A restructure — the case for this rule — is when the successor would discard or reorder most of the existing content. Supersede only plans for **your own task**: another writer's plan is theirs to restructure — propose the supersede in your report instead of doing it. If your plan genuinely needs it:

1. Mark the old file at the very top, naming the successor:
   ```markdown
   > **Superseded** by [plan-checkout-rewrite.md](plan-checkout-rewrite.md) on 2026-07-25. Kept for history.
   ```
2. Create the successor file.
3. Move the superseded file out of the current location (see Rule 4) in the same working session.

The marker goes on first deliberately: if the work is interrupted midway, a marker pointing at a successor still being written is recoverable, while two files both claiming to be the current plan is the original problem, restated.

## Rule 4: Close the lifecycle when the task ends

Plans need an explicit end of life:

- **On task completion**: mark the plan done at the top (`> Done 2026-07-25`), then either archive it (move to `archive/` or `plans/archive/`, keeping the name) or delete it if it is pure scratch with no decisions worth keeping.
- **Staleness sweep** when entering a cluttered directory: a plan or scratch file untouched for roughly two weeks (adjust to the project's cadence) whose task appears finished or abandoned is a candidate. Files belonging to *your own* task that are clearly finished → archive directly and say so in the report. Files whose ownership or state is uncertain → flag and propose, don't act.
- **Delete only what is yours and absorbed.** Deleting is reserved for files you created (this session or a prior run of your own task) whose useful content is either nil or demonstrably merged elsewhere. Archive rather than delete whenever the file records decisions, constraints, or context.
- **Respect other writers — and untracked always wins.** Never silently delete or archive a file you did not create. In a git repository, check `git status` first — an untracked plan or notes file may be someone's uncommitted work in progress. Untracked-and-not-yours overrides every other rule here, including staleness: flag it in the report, touch nothing.

## Rule 5: Verify after you write

Rule 2 guards against clobbering before you edit; this rule catches what slipped through anyway. After every write to a shared plan file:

1. **Diff old vs. new.** Compare the file's content immediately before your edit against what's on disk now — `git diff` in a repo, or a copy of the pre-edit content otherwise. Read the diff; don't just trust that the edit tool call succeeded.
2. **Confirm only your change is there.** The diff should show the lines you intended to add, remove, or change, and nothing else. A section you didn't touch showing up as removed-then-re-added is a red flag even if its final content looks right — a full rewrite that happens to reproduce old text still risks losing a concurrent writer's edit that landed between your read and your write.
3. **On an unexpected deletion, stop and re-read** — don't patch the gap from memory. The file changed under you; redo the edit as a fresh targeted diff against its current content. Papering over a missing section from what you remember it said is the same regenerate-from-memory failure Rule 2 warns about, one step later.
4. **Note the check in your report**: which lines changed, and that nothing else did.

This is one cheap diff read, and it's the only check that happens after the write has actually landed — treat a shrinking or unexpected diff here with the same suspicion as the pre-write red flags in Rule 2.

## Report the hygiene pass

After applying these rules, state briefly:

- which file is the current plan;
- what was merged into it, and from where;
- what was archived, superseded, or flagged as stale;
- what was left untouched and why (unrelated, uncommitted, uncertain);
- confirmation that the post-write diff (Rule 5) showed only the intended change.

This report is what lets the next session — or the human — trust the directory again.

## Worked example

A working directory contains:

| File | Observation |
|---|---|
| `PLAN.md` | current task, updated 3 days ago, has open checkboxes |
| `NOTES.md` | your own scratch findings from the same task, overlaps PLAN.md |
| `plan-old-refactor.md` | task shipped a month ago, untouched since |
| `TODO-ideas.md` | untracked in git, not yours |

Actions: fold the still-relevant findings from `NOTES.md` into `PLAN.md` as a targeted edit (re-read first), then delete `NOTES.md` — it is yours and its content now lives in the plan; mark `plan-old-refactor.md` done and move it to `archive/` (tracked, clearly finished, so act directly); leave `TODO-ideas.md` in place but flag it in the report as someone else's uncommitted file. Result: one current plan, one archived plan, one flagged file — and a report saying exactly that.

## Edge cases

- **Concurrent writers on one plan**: give each writer its own `##` section and append-only discipline within it; always re-read immediately before writing.
- **Several active tasks in one directory**: one `plan-<task-slug>.md` per task; a plan index file is optional and only worth it above three or four active plans.
- **Ephemeral scratch that must exist mid-task**: name it so discovery finds it (`scratch-<task-slug>.md`) and delete it in the same session that finishes the task — scratch that outlives its session becomes someone else's mystery.
