---
name: "spawn"
description: "Launch N parallel subagents in isolated git worktrees to compete on the session task. Use when the user runs /hub:spawn or asks to start the competing agents for an initialized AgentHub session."
command: /hub:spawn
---

# /hub:spawn — Launch Parallel Agents

Spawn N subagents that work on the same task in parallel, each in an isolated git worktree.

## Usage

```
/hub:spawn                                    # Spawn agents for the latest session
/hub:spawn 20260317-143022                    # Spawn agents for a specific session
/hub:spawn --template optimizer               # Use optimizer template for dispatch prompts
/hub:spawn --template refactorer              # Use refactorer template
```

## Templates

When `--template <name>` is provided, use the dispatch prompt from `../agenthub/references/agent-templates.md` instead of the default prompt below. Available templates:

| Template | Pattern | Use Case |
|----------|---------|----------|
| `optimizer` | Edit → eval → keep/discard → repeat x10 | Performance, latency, size reduction |
| `refactorer` | Restructure → test → iterate until green | Code quality, tech debt |
| `test-writer` | Write tests → measure coverage → repeat | Test coverage gaps |
| `bug-fixer` | Reproduce → diagnose → fix → verify | Bug fix with competing approaches |

When using a template, replace all `{variables}` with values from the session config. Assign each agent a **different strategy** appropriate to the template and task — diverse strategies maximize the value of parallel exploration.

## What It Does

1. Load session config from `.agenthub/sessions/{session-id}/config.yaml`
2. For each agent 1..N:
   - Write task assignment to `.agenthub/board/dispatch/`
   - Build agent prompt with task, constraints, and board write instructions
3. Launch ALL agents in a **single message** with multiple Agent tool calls:

```
Agent(
  prompt: "You are agent-{i} in hub session {session-id}.

Your task: {task}

Read your full assignment at .agenthub/board/dispatch/{seq}-agent-{i}.md

Instructions:
1. Work in your worktree — make changes, run tests, iterate
2. Commit all changes with descriptive messages
3. Write your result summary to .agenthub/board/results/agent-{i}-result.md
   Include: approach taken, files changed, metric if available, confidence level
4. Exit when done

Constraints:
- Do NOT read or modify other agents' work
- Do NOT access .agenthub/board/results/ for other agents
- Commit early and often with descriptive messages
- If you hit a dead end, commit what you have and explain in your result",
  isolation: "worktree"
)
```

4. Update session state to `running` via:
```bash
python {skill_path}/scripts/session_manager.py --update {session-id} --state running
```

## Critical Rules

- **All agents in ONE message** — spawn all Agent tool calls simultaneously for true parallelism
- **isolation: "worktree"** is mandatory — each agent needs its own filesystem
- **Never modify session config** after spawn — agents rely on stable configuration
- **Each agent gets a unique board post** — dispatch posts are numbered sequentially

## After Spawn

Tell the user:
- {N} agents launched in parallel
- Each working in an isolated worktree
- Monitor with `/hub:status`
- Evaluate when done with `/hub:eval`
