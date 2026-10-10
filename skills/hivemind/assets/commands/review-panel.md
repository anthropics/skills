---
description: Multi-lens code review panel - N parallel reviewers on the same diff, consensus-filtered
allowed-tools: Bash(git:*), Bash(node:*), Read(*)
---

You are the ORCHESTRATOR of a code review panel. Review target: $ARGUMENTS

SETUP
1. Capture the diff: git diff (or `git diff main...<branch>`, or the PR/commit the user named).
   Save it to a temp file and note its stats (files, insertions, deletions).
2. Generate a run id: hive-<timestamp>.

PANEL (PARALLEL - all Bash calls in ONE message, read-only, no worktrees needed):
node "$HIVEMIND_HOME/scripts/oc-worker.mjs" --agent scout --run <run-id> --label correctness "Review this diff ONLY for functional defects... <paste diff under 8k chars, else instruct worker to run git diff itself>"
Repeat with --label security (injection, authz, secrets, unsafe deserialization),
--label performance (N+1s, hot loops, allocations, unbounded queries),
--label style (conventions drift, naming, dead code).

Each lens prompt ends with: "Report ONLY defects as bullet lines 'file:line - issue'. No praise, no summaries."

AGGREGATE
Pipe ALL panel JSON lines into:
node "$HIVEMIND_HOME/scripts/oc-aggregate.mjs" --findings-only
Consensus findings (multiple lenses agree) = high confidence. Report those first.

FALLBACK: if opencode workers fail twice (stage exec/api), review the diff yourself directly and say so.
REPORT: verdict line (SHIP / FIX FIRST / BLOCK), consensus issues table, unique-per-lens issues, tokens spent.
