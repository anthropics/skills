# Per-harness paths and formats

Snapshot verified **2026-07-13** — these locations change as harnesses evolve. Before relying on one, confirm it exists; before publishing a skill that encodes one, re-verify against the harness's current docs.

Detect what's on this machine:

```bash
ls -d ~/.claude/projects ~/.codex/sessions ~/.local/share/opencode/storage ~/.pi/agent/sessions 2>/dev/null
```

## Session history (what you mine)

| Harness | Location | Format notes |
|---|---|---|
| Claude Code | `~/.claude/projects/<project-dir>/*.jsonl` | One JSONL file per session; top-level files are main sessions, subdirectories hold subagent transcripts. Project dir name is the slugified cwd. |
| Codex CLI | `~/.codex/sessions/YYYY/MM/DD/rollout-*.jsonl` | One rollout JSONL per session: user/assistant turns, tool calls, token usage. Date-partitioned, so cluster by the `cwd` recorded inside each file, not by directory. |
| opencode | `~/.local/share/opencode/storage/` | Split across `session/` (index), `message/`, `part/` (content), `session_diff/`. Newer versions also keep a SQLite DB at `~/.local/share/opencode/opencode.db`. Join messages to sessions via `session_id`. |
| pi | `~/.pi/agent/sessions/` | Auto-saved sessions organized by working directory. |

All of these can be tens of MB per session or grow to GBs total — index and digest, never read whole files.

## Skill install directories (where the output goes)

| Harness | User-level | Project-level | Also reads |
|---|---|---|---|
| Claude Code | `~/.claude/skills/` | `.claude/skills/` | plugins (`~/.claude/plugins/`) |
| Codex CLI | `~/.codex/skills/` | `.codex/skills/` | — |
| opencode | `~/.config/opencode/skills/` | `.opencode/skills/` | `~/.claude/skills/`, `.claude/skills/`, `~/.agents/skills/`, `.agents/skills/` |
| pi | `~/.pi/agent/skills/` | `.pi/skills/` | `~/.claude/skills/`, `.claude/skills/` |

Practical consequence: installing a skill to `~/.claude/skills/` makes it visible to Claude Code, opencode, **and** pi; only Codex needs its own copy.

## Standing instructions (Phase 0 inventory)

| Harness | Files |
|---|---|
| Claude Code | `CLAUDE.md` (global `~/.claude/CLAUDE.md` + per-project), memory files |
| Codex CLI | `AGENTS.md` (global `~/.codex/AGENTS.md` + per-project) |
| opencode | `AGENTS.md`, opencode rules/config (`opencode.json`) |
| pi | `AGENTS.md` / `CLAUDE.md` per-project |
