---
name: session-memory
description: Preserve critical technical facts across context compaction and session restarts. Use when working on multi-step coding tasks, debugging sessions, or any long-running work where file edits, test results, and decisions need to survive context resets. Activates automatically when context is filling up or when resuming interrupted work.
---

# Session Memory

Compaction silently discards all tool outputs — file contents, test results, applied patches, command output. After compaction, you retain only a vague LLM summary plus recent user messages. This skill gives you a structured way to save what matters *before* it disappears, and recall it *after* compaction replaces your context.

---

## The problem this solves

In a typical coding session, 79% of tokens are tool results (file reads, test output, patches). Compaction drops all of them. After compaction you may:

- Forget which file was modified and what the change was
- Lose the test result that confirmed a fix worked
- Miss that a downstream path (e.g. `mobile.rs`) was already checked

This skill teaches you to write a checkpoint file **proactively**, so the facts survive compaction and can be restored.

---

## Checkpoint file

All session memory lives in one file: **`.claude/session-memory.md`**

Create the `.claude/` directory if it doesn't exist. The file is human-readable and git-committable, so teammates see the same context you do.

---

## When to write

Write to `.claude/session-memory.md` after any of these events:

| Trigger | Why |
|---|---|
| Applied a patch / wrote a file | Exact diffs are the first thing compaction drops |
| Test run completed | Pass/fail state is high-value, easy to lose |
| Made a scoping decision | "X doesn't need changes" is invisible to compaction |
| Read a file at a specific line | The content and location both disappear |
| Approaching context limit | Write *before* compaction triggers, not after |
| Resuming a session | Read the file first, then confirm what's still accurate |

**Do not wait for compaction to happen.** Write incrementally after each meaningful action.

---

## Entry format

Each entry has a type tag, a location/label, and verbatim content. Keep entries concise — prefer exact snippets over prose summaries.

```markdown
# Session Memory
_Updated: 2026-03-13 · task: fix auth token refresh race_

## [PATCH] src/auth.rs:47
```diff
 if decoded.exp < Utc::now().timestamp() + 300 {
+    cache::invalidate(&decoded.sub);
     let new_token = generate_token(&decoded.sub)?;
```

## [TEST] cargo test auth:: — 14 tests
BEFORE: test_concurrent_refresh FAILED (assertion: old_token_invalid)
AFTER:  all 14 passed ✅

## [FILE] src/auth.rs — refresh_token() signature
pub fn refresh_token(token: &str) -> Result<Token>
Bug was at line 47: cache::set() called before cache::invalidate().

## [DECISION] src/api/mobile.rs — no change needed
mobile.rs:89 calls auth::refresh_token() directly → picks up fix automatically.
Checked: web.rs:67 also confirmed in scope, same conclusion.

## [DECISION] regression test added
src/auth_test.rs: test_token_invalidated_on_concurrent_refresh
Uses user_42, asserts cache::get("user_42") != original token after concurrent refresh.
```

### Entry types

| Tag | Use for |
|---|---|
| `[PATCH]` | Exact diff hunks — the most critical to preserve |
| `[TEST]` | Test suite results, before/after state |
| `[FILE]` | Key function signatures, line numbers, relevant snippets |
| `[DECISION]` | Scoping decisions, things explicitly ruled out |
| `[CMD]` | Command output that informed a decision |
| `[STATE]` | Current status of a multi-step task |

---

## When to read

Read `.claude/session-memory.md` at the start of **every** turn after these events:

- **Session start** — always read first before touching any files
- **After compaction** — your history was replaced; this file is your ground truth
- **When uncertain** — if you're about to re-run a test or re-read a file, check whether the result is already saved

If the file doesn't exist, note that no checkpoint has been written yet and proceed normally.

---

## Maintenance

Keep the file lean to avoid inflating your own context:

- **Token budget**: aim for < 2,000 tokens total
- **Prune on write**: when adding a new entry, remove entries that are no longer relevant (completed subtasks, superseded decisions)
- **One file per task**: when starting a new unrelated task, archive or clear the file
- **Verbatim over verbose**: a 3-line diff is more useful than a 3-paragraph description of what the diff does

---

## Compaction warning

When you see the system message:

> *"Heads up: Long threads and multiple compactions can cause the model to be less accurate."*

This means compaction just happened. **Immediately read `.claude/session-memory.md`** and confirm your understanding of the current task state before continuing.

---

## Example workflow

```
User: fix the auth token refresh bug
You:  [read .claude/session-memory.md — file doesn't exist yet, start fresh]
      [read src/auth.rs]
      → write [FILE] entry with the function signature and bug location

      [run cargo test auth::]
      → write [TEST] entry with BEFORE result

      [apply patch]
      → write [PATCH] entry with exact diff

      [run cargo test auth:: again]
      → update [TEST] entry with AFTER result

      [grep mobile.rs]
      → write [DECISION] entry: no change needed

      <<< compaction happens here — tool outputs are gone >>>

      [read .claude/session-memory.md — checkpoint restored]
      You now know: what was fixed, at what line, that tests pass, that mobile.rs is clear
      Continue task without re-reading files you already processed.
```
