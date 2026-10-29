---
description: Orchestrate a parallel opencode worker swarm on a task (worktree isolation, you merge)
allowed-tools: Bash(git:*), Bash(node:*), Read(*), Edit(*), Grep(*), Glob(*)
---

You are the ORCHESTRATOR of a free opencode worker swarm. Task: $ARGUMENTS

PHASE 1 - PLAN
Decompose the task into 2-5 INDEPENDENT subtasks that do not touch the same files.
Choose an agent per subtask: scout (read-only research), coder (writes code), tester (runs tests only).

PHASE 2 - ISOLATE
If any subtask writes files: create one git worktree per writing worker:
git worktree add "../<repo-name>-wt-N" -b swarm/N
Record each worktree path. If no subtask writes files, skip worktrees.

PHASE 3 - SPAWN (PARALLEL)
Issue ALL worker invocations as PARALLEL Bash tool calls in ONE message.
Each invocation:

node "$HIVEMIND_HOME/scripts/oc-worker.mjs" --agent <agent> --dir <worktree-or-cwd> --timeout 900 "<SUBTASK>"

Notes:
- scout workers may omit --dir to read THIS repo.
- coder/tester workers MUST get their own --dir (worktree path).
- Never run two writing workers against the same directory.

PHASE 4 - REVIEW (you, personally)
Each output line contains {result, tokens}. For every writing worker run:
git diff main...swarm/N
Review the diff yourself line by line. You are the only merger.

PHASE 5 - INTEGRATE
- Merge approved branches: git merge swarm/N
- Reject: delete branch + git worktree remove.
- Run the test suite after all merges.

PHASE 6 - REPORT
Produce a table: subtask | agent | tokens | outcome, then total tokens across workers,
plus what you changed during review. Flag any worker whose output you rejected and why.

HARD RULES:
- Worker outputs enter your context ONLY via the script's single compact JSON line.
- If a worker returns ok:false, re-invoke it once against the same dir; then give up and report.
- NEVER let raw opencode NDJSON streams reach this conversation.
- Workers never share directories. You never delegate merging or reviewing.
