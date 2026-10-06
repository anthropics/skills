# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What This Project Is

`cmux-workflows` is a shell-based orchestration layer for running parallel Claude Code subagents via cmux (a terminal multiplexer with a Unix socket API). The `cmux-task` script spawns multiple Claude instances in separate cmux surfaces, injects role-specific prompts from templates, and coordinates their work via `output/<role>.md` files.

## Commands

There are no build/test/lint steps — this is a pure shell + text project.

**Install the script:**
```bash
ln -sf "$(pwd)/scripts/cmux-task" ~/.local/bin/cmux-task
```

**Run orchestration:**
```bash
cmux-task feature "<description>" --cwd /path/to/project
cmux-task bugfix "<description>" --cwd /path/to/project
cmux-task research "<description>" --cwd /path/to/project
cmux-task custom "<description>" --roles role1,role2 --cwd /path/to/project
```

**Options:**
```bash
--dry-run          # Preview surfaces and prompts without creating anything
--no-prompts       # Create surfaces but skip auto-injecting prompts
CLAUDE_START_WAIT=5  # Override default 3s wait for Claude startup (env var)
TEMPLATES_DIR=/... # Override default templates/ directory (env var)
```

**Monitor workers:**
```bash
cmux read-screen --workspace $WS --surface $SURF
cmux close-workspace --workspace $WS
```

## Architecture

### How It Works

1. **Orchestrator** (your current Claude session) calls `cmux-task`
2. `cmux-task` script:
   - Creates a cmux workspace with one surface per role
   - Starts `claude` in each surface with `cd $CWD && claude`
   - Waits `CLAUDE_START_WAIT` seconds (default: 3)
   - Injects the rendered template prompt into each surface
3. **Subagents** (parallel Claude instances) work independently and write `output/<role>.md` when done
4. **Orchestrator** reads `output/*.md` files and synthesizes the final result

### Role-to-Workstream Mapping

| Task Type | Roles Created |
|-----------|--------------|
| `feature` | implementer, tester, reviewer |
| `bugfix`  | implementer, tester |
| `research`| researcher, summarizer |
| `custom`  | whatever `--roles` specifies |

### File Ownership (Safety Invariant)

- **implementer** → production code only, no test files
- **tester** → test files only, no production code
- **reviewer** → read-only across all files
- **researcher** → no code changes, research only
- **summarizer** → waits for `output/researcher.md`, then synthesizes

This one-writer-per-file constraint prevents merge conflicts.

### Template Rendering

Templates in `templates/` use three placeholders substituted by `cmux-task`:
- `{{TASK}}` — the task description passed on the CLI
- `{{ROLE}}` — the role name (implementer, tester, etc.)
- `{{CWD}}` — the working directory for the workers

### Key Script Internals (`scripts/cmux-task`)

- `render_template()` — substitutes placeholders via `sed`
- `surface_send()` / `surface_run()` — sends keystrokes/commands to cmux surfaces
- `extract_ref()` — parses workspace/surface IDs from cmux output
- Task type resolution maps `feature`/`bugfix`/`research` to role lists

### Permissions

`.claude/settings.local.json` whitelists Bash commands Claude Code may invoke in this directory — primarily cmux commands, installation helpers, and GitHub CLI.
