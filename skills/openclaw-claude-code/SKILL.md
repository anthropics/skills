---
name: openclaw-claude-code
description: "Control and operate Claude Code CLI for all coding tasks via OpenClaw. Use this skill when building features, fixing bugs, exploring a codebase, planning architecture, reviewing PRs, or running tests. Triggers on /ca, /code, claude code, or any non-trivial coding request."
---

# OpenClaw Claude Code Skill

Control and orchestrate Claude Code (`claude` CLI) from OpenClaw. Sam (OpenClaw) orchestrates; Claude Code executes. Sam never writes non-trivial code directly.

---

## /ca command routing

| Command | Action |
|---------|--------|
| `/ca explore <q>` | haiku, plan mode, read-only codebase map |
| `/ca plan <task>` | opus, plan mode, output to docs/plans/<slug>.md |
| `/ca build <task>` | worktree + opus + acceptEdits + test run |
| `/ca test` | run tests (unit + integration) in worktree |
| `/ca review` | diff review vs dev |
| `/ca e2e <task>` | full pipeline: explore → plan → build → test → PR |
| `/ca resume` | `claude --resume` interactive picker |
| `/ca pr <num>` | `claude --from-pr <num>` — continue in PR context |

---

## Quick reference

```bash
# New feature (isolated worktree, opus, auto-accept edits)
cd <repo>
claude --worktree feat/task-name --permission-mode acceptEdits --model opus

# Explore first (haiku, read-only, fast + cheap)
claude --permission-mode plan --effort low --model claude-haiku-4-6 \
  -p "Map where X is called and how data flows through it."

# Resume a session (interactive picker)
claude --resume

# Resume for PR review comments
claude --from-pr <pr-number>

# Automated one-shot from OpenClaw (bare = minimal overhead)
claude --bare --dangerously-skip-permissions --no-session-persistence \
  --model sonnet -p "Run pytest tests/api/ -xvs. Report results."

# Overnight supervised run (gates on permission relay to Telegram via OpenClaw)
claude --worktree feat/task --permission-mode auto --channels --model opus \
  -p "Implement X. Ask for approval before any git push."
```

---

## Permission modes

| Mode | Use when |
|------|---------|
| `plan` | Phase 1 — read-only exploration, no edits |
| `acceptEdits` | Phase 2 — auto-accept file edits, ask for bash |
| `bypassPermissions` | Automated/trusted runs |
| `auto` | Overnight runs — Claude decides per action |
| `default` | Interactive supervised sessions |

---

## Effort + model pairing

| Task | Model | Effort |
|------|-------|--------|
| Explore / "where is X?" | haiku | low |
| Root cause analysis | sonnet | medium |
| Architecture planning | opus | max |
| Feature build | opus | high |
| Automated/scripted | sonnet | low |

---

## Worktree isolation (mandatory for all builds)

Never run Claude Code in the main checkout.

```bash
# Preferred: built-in --worktree flag
cd <repo>
claude --worktree feat/my-task --permission-mode acceptEdits --model opus
# Claude Code creates branch + worktree automatically

# With tmux (iTerm2 native panes)
claude --worktree feat/my-task --tmux --model opus

# Manual (when scripting)
git fetch origin && git checkout dev && git pull origin dev
git worktree add ../worktrees/feat/my-task -b feat/my-task

# Cleanup after PR merged
git worktree remove ../worktrees/feat/my-task
git branch -d feat/my-task
```

---

## Testing gate (mandatory before any PR)

```bash
# Inside worktree:
source scripts/load_env.sh local
pytest tests/ -x -q --override-ini addopts=            # unit tests
pytest tests/api/ -xvs -m deployment_tests             # integration tests

# Docker-based (CI parity, handles port conflicts across concurrent sessions):
PORT=$(python3 -c "
import socket; p=8083
while True:
    with socket.socket() as s:
        if s.connect_ex(('localhost', p)) != 0: print(p); break
    p += 1")
sed -i '' "s|API_BASE_URL=http://localhost:[0-9]*/|API_BASE_URL=http://localhost:$PORT/|" src/.env_local
HOST_PORT=$PORT ./docker/docker-manager.sh -c local -a test -M deployment_tests
```

### Always include in build prompts:
```
After implementing:
1. source scripts/load_env.sh local
2. pytest tests/ -x -q --override-ini addopts=
3. Fix failures before committing — do not commit broken tests
4. Self-review your full diff: edge cases, unintended changes, regressions
5. Commit locally. Do NOT push or open a PR.
```

---

## Session management

```bash
claude --resume                           # interactive picker
claude --resume <session-id>              # by ID
claude --from-pr <number>                 # resume in PR context
claude --resume <id> --fork-session       # branch the conversation
claude --name "fix-sourcing-1518" ...     # name for later recall
```

---

## Full pipeline: /ca e2e

```
1. EXPLORE   claude --permission-mode plan --effort low --model claude-haiku-4-6
             → map relevant files + call chains

2. PLAN      claude --permission-mode plan --effort high --model opus
             → architecture, pseudocode, test plan, risks
             → save to docs/plans/<slug>.md
             → Sam reviews; escalate to human if needed

3. BUILD     claude --worktree feat/<slug> --permission-mode acceptEdits --effort high --model opus
             → implement from plan doc
             → run tests, self-review diff, commit locally

4. REVIEW    Sam reads diff (git diff dev...HEAD)
             → checks scope creep, test coverage, unrelated changes

5. PR        git push + gh pr create --base dev
             → PR body: root cause, files changed, test results, post-merge steps
             → notify human

6. ITERATE   claude --from-pr <number>
             → resume in context of review comments
```

---

## OpenClaw automation (--bare)

For cron/background tasks spawned by OpenClaw:
```bash
claude --bare --dangerously-skip-permissions --no-session-persistence \
  --model sonnet -p "Run tests. Report results as plain text."
```
`--bare` skips hooks, LSP, plugin sync, auto-memory, keychain reads — faster and cleaner for automation.

---

## Supervised overnight runs (--channels)

OpenClaw's MCP permission relay lets Claude Code gate on Telegram approval for destructive actions:
```bash
claude --worktree feat/big-task --name "overnight-refactor" \
  --permission-mode auto --channels --model opus \
  -p "Refactor X. Ask for approval before any git push or AWS change."
```

---

## PR rules

- Always branch from `dev`, never from another feature branch
- Branch prefix: `feat/` or `fix/`
- PR targets `dev`, never `main`
- Sam reviews diff before `git push`
- Human tests PRs — never merge without explicit approval
- Conventional commits: `feat:` `fix:` `docs:` `refactor:` `chore:`

---

## Division of labour

| OpenClaw (Sam) | Claude Code |
|---------------|-------------|
| Receives task from human | Explores codebase |
| Routes to right approach | Writes code |
| Kicks off worktree | Runs tests |
| Reviews plan + diff | Self-reviews diff |
| Pushes + opens PR | Commits locally only |
| Monitors CI + review comments | |
