---
name: cmux-workflows
description: Use when a task has 2+ genuinely independent workstreams (feature build, bugfix with parallel test writing, multi-angle research) and you are about to spawn subagents. Do NOT use for sequential tasks, small one-file changes, or anything that can be done in a single focused session.
---

# cmux Multi-Agent Orchestration

## What is cmux

cmux is a terminal multiplexer with a Unix socket API. It manages **workspaces** (tabs) each containing **panes** that hold **surfaces** (terminal tabs within a pane). You control it with `cmux <command>` from any shell.

Key commands used in orchestration:
```
cmux new-workspace --cwd <path>                        # create workspace, returns "OK workspace:N"
cmux new-surface --workspace <ref>                     # create surface, returns "OK surface:N pane:N workspace:N"
cmux rename-workspace --workspace <ref> <title>        # name the workspace
cmux rename-tab --workspace <ref> --surface <ref> <name>  # name the tab
cmux send --workspace <ref> --surface <ref> <text>     # send text to surface
cmux send-key --workspace <ref> --surface <ref> Return # press Enter
cmux read-screen --workspace <ref> --surface <ref>     # read current screen content
cmux close-workspace --workspace <ref>                 # tear down workspace
```

Extract refs from output with: `grep -o 'workspace:[0-9]*' | head -1`

## When to Use cmux

**USE** when:
- Task has 2+ independent workstreams (e.g., implement feature + write tests in parallel)
- Research task requires surveying multiple independent sources simultaneously
- Code review + implementation can proceed in parallel on disjoint files
- Estimated total time > 20 min and parallelism meaningfully reduces wall time

**DO NOT USE** when:
- Tasks are sequential (A must finish before B starts)
- Single-file or tightly coupled changes (agents would conflict)
- Task is < 15 minutes of focused work
- Subagents would need to coordinate writes to the same files

## Standard Workflow

### 1. Decompose and Assign Disjoint Scopes

Before invoking cmux-task, identify:
- Which files/modules each subagent owns exclusively
- What each subagent should produce as output (written to `output/<role>.md`)
- The synthesis step that only the orchestrator performs

### 2. Set Up Session with cmux-task

```bash
# Feature work: implementer + tester + reviewer
cmux-task feature "add OAuth2 login flow" --cwd /path/to/project

# Bug investigation: implementer + tester
cmux-task bugfix "race condition in job queue" --cwd /path/to/project

# Research: researcher + summarizer
cmux-task research "compare state management libraries for React" --cwd /path/to/project

# Custom roles
cmux-task custom "refactor auth module" --roles implementer,reviewer --cwd /path/to/project
```

The script creates workspaces, surfaces, and starts `claude` in each. It outputs workspace ref and surface refs for each role. You then inject the task-specific prompt.

### 3. Inject Initial Prompts

`cmux-task` handles prompt injection automatically (3s wait for claude to start, then sends template text). You can skip this with `--no-prompts` if you want to type prompts manually.

To send a custom prompt to a specific worker manually:
```bash
cmux send --workspace "$WS" --surface "$SURF_IMPL" "Your custom prompt here"
cmux send-key --workspace "$WS" --surface "$SURF_IMPL" Return
```

Templates live at: `~/Programming/skills/skills/cmux-workflows/templates/<role>.txt`

### 4. Monitor Workers

Poll workers for progress using `read-screen`:
```bash
cmux read-screen --workspace "$WS" --surface "$SURF_IMPL" | tail -5
```

Workers write summaries to `output/<role>.md` when done. Watch for this.

### 5. Synthesize

Orchestrator (you, current session) reads all `output/*.md` files, resolves conflicts, and produces the final result. Do not automate merges of complex code—review them.

## Role Assignments

| Role | Scope | Output |
|------|-------|--------|
| implementer | Production code changes | `output/implementer.md` |
| tester | Test files only | `output/tester.md` |
| reviewer | Read-only review of above | `output/reviewer.md` |
| researcher | External research, no code changes | `output/researcher.md` |
| summarizer | Synthesizes researcher output | `output/summarizer.md` |

## Safety Rules

1. **One writer per file.** Never assign the same file to two workers.
2. **Worktrees for isolation.** For large features, consider `git worktree add` per subagent.
3. **Summary before merge.** Each worker must write `output/<role>.md` before orchestrator synthesizes.
4. **Orchestrator synthesizes, not merges blindly.** Read all outputs, resolve conflicts manually.
5. **Close workspaces when done.** `cmux close-workspace --workspace <ref>` to clean up.

## Invoking cmux-task (full reference)

The `cmux-task` script is at `~/.local/bin/cmux-task` (symlinked from this skill's `scripts/` dir).

```
cmux-task <type> "<description>" [--cwd <path>] [--roles <r1,r2,...>] [--dry-run]

Types:
  feature    → roles: implementer, tester, reviewer
  bugfix     → roles: implementer, tester
  research   → roles: researcher, summarizer
  custom     → specify --roles explicitly

Options:
  --cwd <path>          Project root (default: $PWD)
  --roles <list>        Comma-separated roles (for custom type)
  --dry-run             Print plan, create nothing

Output: workspace ref + surface ref per role, printed to stdout.
```

After the script finishes, copy the refs into your session context and proceed with prompt injection.
