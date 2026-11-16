---
name: closeout
description: Wrap up a coding session by writing a structured closeout doc, updating per-repo context.md / progress.md, and actively scanning for unfinished work (uncommitted changes, unpushed commits, untested deploys, broken refs). Use at the end of an interactive coding session, when the user says "wrap up", "closeout", or "summarize the session", or when asked what's left to do. Takes an optional session slug as an argument.
---

# Session Closeout

A session is not done when the last edit lands. It is done when (a) the work is documented in places future sessions will actually read, and (b) every loose end has been either fixed or explicitly listed. This skill enforces both.

## Pre-Flight (read before acting)

Before writing anything, gather context. Skipping this is the #1 reason closeouts produce empty or wrong content.

1. **Identify touched repos.** Anything edited, committed, or where commands ran. If unsure, `git status` in candidate dirs.
2. **Collect commits.** For each touched repo: `git log --oneline @{u}..HEAD 2>/dev/null` for unpushed; `git log --since="6 hours ago" --oneline` for recent. (Git accepts relative dates natively, so this is portable across Linux/macOS without needing `date -d`.)
3. **Diff state.** `git status` and `git diff --stat` in each touched repo. Note uncommitted/unstaged.
4. **Confirm with the user** if the session boundary is ambiguous (e.g., "this session started when you asked X, right?"). Do not guess if the scope is wide.

If `[slug]` is missing, derive one from the dominant theme of the work (`fix-auth-redirect`, `add-csv-export`). Keep it kebab-case and short.

## Procedure

### Step 1: Write the closeout doc

Default location: `.claude/closeouts/YYYY-MM-DD-[slug].md` inside the primary repo for the session. If the work spanned multiple repos with no clear primary, pick the repo with the most commits or ask. If `.claude/closeouts/` does not exist, create it.

Use this structure (omit sections that don't apply, but don't omit because the section is hard to fill — fill it):

```markdown
# <Session Title>
**Date:** YYYY-MM-DD
**Duration:** approximate
**Repos touched:** list

## Context & Motivation
Why this work was initiated. The user's original request and any refinements during the session.

## Decisions Made
For each significant decision:
- **Decision:** What was decided
- **Alternatives considered:** What else was on the table
- **Rationale:** Why this option was chosen
- **Trade-offs:** What was given up

## What Was Built / Changed
Chronological narrative. File paths, commit hashes, PR links.

## Architecture & Design
For new systems or non-trivial changes: how it works, data flow, key constraints.

## Open Items & Follow-ups
(Filled in by Step 3 — leave empty placeholder for now.)

## Key Files
Links to important files created or modified.
```

### Step 2: Update per-repo context files (most commonly skipped)

This is the highest-leverage step. New Claude Code sessions load each repo's `CLAUDE.md` and any nearby `context.md` / `progress.md`. They do *not* read closeout docs. If you only write the closeout doc, future sessions will not see your work.

For **every** touched repo:

1. **`context.md`** (at repo root or `docs/context.md`, follow existing convention if present):
   - Current state: working / broken / in-progress
   - What changed in this session (one-paragraph summary)
   - Key decisions and rationale (link to closeout doc for detail)
   - Open items for this repo specifically

2. **`progress.md`** (optional but recommended for repos with active iteration):
   - Append a dated entry with commit hashes and one-line summaries

If the repo has neither file, create `context.md`. Don't create `progress.md` if there's no convention for it in the repo — that's clutter.

### Step 3: Open-items scan (do not skip)

Before declaring the closeout done, actively scan for unfinished work. Many sessions are declared done with dirty state — this step catches that.

Run through each check explicitly. Do not write "none" without performing the check.

1. **Uncommitted changes.** `git status` in every touched repo. Anything staged or unstaged is an open item.
2. **Unpushed commits.** `git log --oneline @{u}..HEAD 2>/dev/null` in every touched repo.
3. **Untested deploys.** Was anything deployed, restarted, or rolled out this session? If yes: was it verified working (curl, browser check, log inspection)? "It deployed without errors" is not verification.
4. **Broken references.** Did the session produce docs, comments, or PR descriptions referencing files, URLs, or symbols? Verify they exist.
5. **Promised but undelivered.** Read back the user's original request. Was every part addressed? Gaps are open items.
6. **Follow-up work surfaced.** Did the session reveal future work (migration step 2, cleanup pass, deferred refactor)? Note it.
7. **Documentation gaps.** Did the work reveal missing docs in the repo's CLAUDE.md or similar? Flag it.

For each item found:
- **Fixable in under 2 minutes:** fix it now. Do not list it.
- **Requires a user decision:** list it with context and options.
- **Future work:** note it as a follow-up.

Fill the **Open Items & Follow-ups** section of the closeout doc with the remaining (post-fix) items. If the list is empty after scanning, that's fine — but only after scanning.

### Step 4: Stage the changes — then ask before committing

Stage the closeout doc and any updated `context.md` / `progress.md` files in each touched repo (`git add` only). Then **stop and ask the user** before committing or pushing.

Show the user:
- One line per repo: `repo-name: N files staged (closeout + M context updates)`
- A proposed commit message per repo, e.g. `closeout: <session title>`
- The pushed remotes that would receive the change

Then ask explicitly: "Commit and push to N repos? (y/N)". Do not commit or push without an explicit yes from the user.

This skill does not silently mutate git history. If the user declines, leave the staged changes in place so they can commit themselves.

## Quality Gates (mandatory before declaring done)

- [ ] Closeout doc written and staged in the primary repo
- [ ] `context.md` updated (or created) and staged in **every** touched repo
- [ ] User has been shown the staged changes and asked to confirm commit + push
- [ ] If user confirmed: all commits created and pushed; `git status` clean
- [ ] If user declined: staged changes left in place (do not unstage)
- [ ] Open-items scan performed item by item (not skipped, not "none" without checking)
- [ ] If anything was deployed this session, deployment verified working

If any gate fails, do not declare the closeout complete. Either fix the gap or call it out explicitly to the user.

## Open Items Scan (for this skill itself)

This skill makes changes. Apply its own rules to its own execution:
- All files written? (closeout doc + context updates)
- All intended files staged? (`git diff --cached` shows what you meant to commit)
- If the user confirmed commit + push in Step 4: all commits actually created and pushed?
- If the user declined: staged changes still in place, not silently unstaged?
- Anything promised in the closeout doc but not actually done? (e.g., "fixed X" written into the doc but no corresponding edit on disk)

## Notes

- **Active scan, not passive list.** "Open items" sections in closeout docs are usually wrong because the writer didn't actually look. Step 3 exists to force a real scan. Treat it as a checklist, not a prompt.
- **Closeout docs are reference, not memory.** Don't write the closeout doc and skip context.md updates — future sessions won't find the closeout doc on their own.
- **Don't fabricate.** If you don't know how long the session was, write "approximate" or leave it. Don't make up commit hashes, PR numbers, or decisions that weren't actually made.
- **One closeout per session, not per task.** If the user asks for closeout mid-session and continues, that's fine — write a partial closeout, then update at the real end. Don't pile up half-closeouts.
