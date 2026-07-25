# TC Tracker

Structured tracking for technical changes (TCs) with a strict state machine, append-only revision history, and a session-handoff block that lets a new AI session resume in-progress work cleanly.

## Quick Start

```bash
# 1. Initialize tracking in your project
python3 scripts/tc_init.py --project "My Project" --root .

# 2. Create a new TC
python3 scripts/tc_create.py --root . \
  --name "user-auth" \
  --title "Add JWT authentication" \
  --scope feature --priority high \
  --summary "Adds JWT login + middleware" \
  --motivation "Required for protected endpoints"

# 3. Move it to in_progress and record some work
python3 scripts/tc_update.py --root . --tc-id <TC-ID> \
  --set-status in_progress --reason "Starting implementation"

python3 scripts/tc_update.py --root . --tc-id <TC-ID> \
  --add-file src/auth.py:created \
  --add-file src/middleware.py:modified

# 4. Write a session handoff before stopping
python3 scripts/tc_update.py --root . --tc-id <TC-ID> \
  --handoff-progress "JWT middleware wired up" \
  --handoff-next "Write integration tests" \
  --handoff-blocker "Waiting on test fixtures"

# 5. Check status
python3 scripts/tc_status.py --root . --all
```

## Included Scripts

- `scripts/tc_init.py` — Initialize `docs/TC/` in a project (idempotent)
- `scripts/tc_create.py` — Create a new TC record with sequential ID
- `scripts/tc_update.py` — Update fields, status, files, handoff, with atomic writes
- `scripts/tc_status.py` — View a single TC or the full registry
- `scripts/tc_validator.py` — Validate a record or registry against schema + state machine

All scripts:
- Use Python stdlib only
- Support `--help` and `--json`
- Use exit codes 0 (ok) / 1 (warnings) / 2 (errors)

## References

- `references/tc-schema.md` — JSON schema reference
- `references/lifecycle.md` — State machine and transitions
- `references/handoff-format.md` — Session handoff structure

## Slash Command

When installed with the rest of this repo, the `/tc <subcommand>` slash command (defined at `commands/tc.md`) dispatches to these scripts.

## Installation

### Claude Code

```bash
cp -R engineering/tc-tracker ~/.claude/skills/tc-tracker
```

### OpenAI Codex

```bash
cp -R engineering/tc-tracker ~/.codex/skills/tc-tracker
```
