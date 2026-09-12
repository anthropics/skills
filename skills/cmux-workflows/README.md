# cmux-workflows

Minimal orchestration layer for running parallel Claude Code subagents via cmux.

## Architecture

```
cmux-workflows/
  SKILL.md              ← Claude Code skill (auto-loaded by skills system)
  scripts/
    cmux-task           ← wrapper script: creates workspaces + surfaces + starts workers
  templates/
    implementer.txt     ← role prompt templates ({{TASK}}, {{ROLE}}, {{CWD}} substituted)
    tester.txt
    reviewer.txt
    researcher.txt
    summarizer.txt
    orchestrator.txt    ← optional; for when orchestrator needs its own worker context
  README.md
```

## How It Works

1. **Orchestrator** (your current Claude session) calls `cmux-task` to set up a session
2. `cmux-task` creates a cmux workspace with one surface per role, starts `claude` in each
3. After a brief wait, it injects each role's prompt template (with task substituted)
4. Orchestrator monitors workers via `cmux read-screen` and `output/*.md` files
5. When all workers complete, orchestrator synthesizes from `output/*.md` and closes the session

## Quickstart

```bash
# In your project directory:
cmux-task feature "add rate limiting to the API" --cwd /path/to/project
cmux-task bugfix "fix race condition in job queue" --cwd /path/to/project
cmux-task research "compare Prisma vs Drizzle for this project"
cmux-task custom "refactor auth module" --roles implementer,reviewer
```

Preview without creating anything:
```bash
cmux-task feature "my task" --dry-run
```

Skip automatic prompt injection (start claude manually in each surface):
```bash
cmux-task feature "my task" --no-prompts
```

## Installation

`cmux-task` is symlinked to `~/.local/bin/cmux-task`. That directory must be in `$PATH`.

If `cmux-task` is not found after install, add to `~/.zshrc`:
```bash
export PATH="$HOME/.local/bin:$PATH"
```
Then reload: `source ~/.zshrc`

To reinstall the symlink:
```bash
ln -sf /path/to/skills/cmux-workflows/scripts/cmux-task ~/.local/bin/cmux-task
```

## Assumptions Made

- `cmux` is installed and reachable in PATH
- `claude` (Claude Code CLI) is installed and reachable in PATH
- Workers run in the same project directory as the orchestrator
- Workers write output to `$CWD/output/<role>.md` — orchestrator reads from there
- Claude takes ≤3 seconds to start (controlled by `CLAUDE_START_WAIT` in the script)
- Roles are disjoint in scope; no two workers edit the same file

## Role Scopes

| Role | Writes to | Reads from |
|------|-----------|------------|
| implementer | production code, `output/implementer.md` | task description |
| tester | test files, `output/tester.md` | task description |
| reviewer | `output/reviewer.md` only | all code + other output/*.md |
| researcher | `output/researcher.md` only | external sources, codebase |
| summarizer | `output/summarizer.md` | `output/researcher.md` |
| orchestrator | `output/orchestrator.md` | all `output/*.md`, user input |

## Limitations

- **Timing:** The 3-second wait for claude to start is a heuristic. On slow machines, increase `CLAUDE_START_WAIT` in the script.
- **Merge automation:** Not automated. The orchestrator reads `output/*.md` and synthesizes manually. This is intentional — automated code merges are brittle.
- **Conflict detection:** No built-in conflict detection if workers violate scope rules. Rely on discipline and disjoint file assignments.
- **Session naming:** Workspace names are truncated at 40 chars. cmux may further truncate in the UI.
- **Single machine only:** All workers run locally. No distributed execution.

## Extending

**Add a new role:**
1. Add `templates/<rolename>.txt` with `{{TASK}}`, `{{ROLE}}`, `{{CWD}}` placeholders
2. Use it via `cmux-task custom "task" --roles <rolename>`

**Add a new task type:**
1. Edit `scripts/cmux-task`, add a `case` entry in the TASK_TYPE switch
2. List the roles for that type

**Change the default wait:**
```bash
CLAUDE_START_WAIT=5 cmux-task feature "my task"
```

**Override template directory:**
```bash
TEMPLATES_DIR=/path/to/my/templates cmux-task feature "my task"
```
(Export `TEMPLATES_DIR` before running — not yet a CLI flag, add it to the script if needed)
