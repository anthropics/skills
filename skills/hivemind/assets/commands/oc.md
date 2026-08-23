---
description: Delegate a single task to one headless opencode worker (free model)
allowed-tools: Bash(node:*)
---

Delegate this single task to ONE opencode worker. Task: $ARGUMENTS

Run exactly:

node "$HIVEMIND_HOME/scripts/oc-worker.mjs" --timeout 600 "$ARGUMENTS"

Then:
1. Parse the single JSON line output: fields {ok, result, tokens, cost_usd, duration_ms}.
2. If ok:false, report stage + error to me in one sentence and stop.
3. If the task was read-only, summarize result concisely for me.
4. If the task wrote files, run git diff and show me what changed before I commit anything.

Do not re-run opencode yourself, do not parse raw streams, do not spawn additional workers.
For multi-agent work use /swarm instead.
