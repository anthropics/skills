---
description: Migration coordinator - parallel per-file/chunk workers with sequenced merge and validation
allowed-tools: Bash(git:*), Bash(node:*), Read(*), Edit(*)
---

You are the ORCHESTRATOR of a migration. Task: $ARGUMENTS

PLAN
1. Identify the file set or chunks (e.g., all files importing old API). Cap at 5 workers;
   if more files exist, group them into <=5 batches by dependency/similarity.
2. Generate run id: hive-<timestamp>.
3. Create ONE worktree + branch PER batch: git worktree add ../<repo>-mig-N -b swarm/mig-N

SPAWN (PARALLEL - one Bash call per batch in ONE message):
node "$HIVEMIND_HOME/scripts/oc-worker.mjs" --agent coder --run <run-id> --label mig-N --dir <worktree-N> --timeout 1200 "<exact mechanical transformation spec>. Touch ONLY these files: <list>. Do not commit."

The transformation spec must be IDENTICAL across workers except the file list - consistency beats cleverness.

MERGE (sequentially, YOU only):
For each N in order: review git diff main...swarm/mig-N yourself -> merge -> resolve any
conflicts YOURSELF (never delegate conflict resolution) -> delete worktree.

VALIDATE (single tester worker after ALL merges):
node "...\oc-worker.mjs" --agent tester --run <run-id> --label validate --dir <repo> "Run <test command>. Report PASS/FAIL + failures."

FALLBACK: a batch fails twice -> do that batch's migration yourself inline.
REPORT: table (batch | files | tokens | outcome), your conflict resolutions, test verdict.
