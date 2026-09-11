# session-memory

A Claude Code skill that preserves critical technical facts across context compaction and session restarts — with zero dependencies.

## The problem

When Claude Code's context window fills up, compaction silently discards all tool outputs: file contents you read, test results, applied patches, command output. After compaction, only a vague LLM summary remains. The model may forget which file was modified, what the test result was, or which paths were already ruled out.

Empirically: in a typical coding session, **tool results account for ~79% of tokens but 0% survive compaction**. After two compactions, all critical technical facts are gone.

## How this skill helps

Session Memory teaches Claude to write a structured checkpoint file (`.claude/session-memory.md`) **proactively** — after each patch, test run, and key decision — so facts survive compaction and can be restored.

No MCP server. No embeddings. No installation beyond adding the skill.

## Install

```bash
claude skills add https://github.com/anthropics/skills/tree/main/skills/session-memory
```

Or add to your project's `.claude/settings.json`:

```json
{
  "skills": ["session-memory"]
}
```

## What gets saved

| Entry type | Example |
|---|---|
| `[PATCH]` | Exact diff hunks applied to files |
| `[TEST]` | Test suite results before and after |
| `[FILE]` | Key function signatures, line numbers |
| `[DECISION]` | Scoping decisions, paths ruled out |
| `[CMD]` | Command output that informed a decision |

## What it looks like

After a coding session, `.claude/session-memory.md` might contain:

```markdown
# Session Memory
_Updated: 2026-03-13 · task: fix auth token refresh race_

## [PATCH] src/auth.rs:47
```diff
+    cache::invalidate(&decoded.sub);
```

## [TEST] cargo test auth:: — 14 tests
BEFORE: test_concurrent_refresh FAILED
AFTER:  all 14 passed ✅

## [DECISION] src/api/mobile.rs — no change needed
Calls auth::refresh_token() directly, picks up fix automatically.
```

## Background

This skill was developed alongside a quantitative analysis of compaction information loss ([openai/codex#14589](https://github.com/openai/codex/issues/14589)). The same problem exists in all LLM coding agents that use in-context compression.

## License

MIT
