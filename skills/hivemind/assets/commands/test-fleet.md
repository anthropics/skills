---
description: Test fleet - split a test suite across parallel tester workers with aggregated verdict
allowed-tools: Bash(node:*), Read(*), Bash(npm:*)
---

You are the ORCHESTRATOR of a parallel test run. Target: $ARGUMENTS (module, path, or "full suite")

PLAN
1. Discover the test layout (framework, test files/globs, how to invoke).
2. Partition tests into 2-4 independent groups (by directory/module). Estimate runtime balance.
3. SAFETY CHECK: if tests bind ports, write shared artifacts (caches, snapshots, DBs),
   or mutate global state -> they CANNOT run concurrently in one dir. Then create one
   worktree per group instead (git worktree add ../<repo>-tf-N -b swarm/tf-N) OR fall back
   to sequential execution. When unsure, use worktrees.

SPAWN (PARALLEL within safety constraints):
node "$HIVEMIND_HOME/scripts/oc-worker.mjs" --agent tester --run hive-<ts> --label tf-N [--dir <worktree-N>] --timeout 900 "<test invocation for group N>. Report PASS/FAIL line 1, then failures."

AGGREGATE: pipe all JSON lines through oc-aggregate.mjs; merge into single verdict:
TOTAL pass/fail counts = sum of groups. A failure in ANY group = suite FAIL.

FALLBACK: fleet unusable -> run the full suite once yourself, report normally.
REPORT: suite verdict, per-group table (group | tests | pass/fail | tokens), failure details.
