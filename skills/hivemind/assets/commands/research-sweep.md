---
description: Parallel research sweep - N scouts investigate different angles of one question simultaneously
allowed-tools: Bash(node:*), Read(*)
---

You are the ORCHESTRATOR of a research sweep. Question: $ARGUMENTS

PLAN
Decompose the question into 3-5 INDEPENDENT angles, e.g.: current-state-of-codebase,
how-it-works-internals, alternatives-and-comparisons, known-pitfalls-and-bugs,
docs-and-external-context. Generate run id: hive-<timestamp>.

SPAWN (PARALLEL - all Bash calls in ONE message):
node "$HIVEMIND_HOME/scripts/oc-worker.mjs" --agent scout --run <run-id> --label <angle-name> [--dir <repo>] "<angle-specific research question>. Cite file:line or URLs for every claim. Max 150 words."

Scouts may use webfetch for external docs; they cannot edit anything.

CHECK PROGRESS between waves if any call errors:
node "$HIVEMIND_HOME/scripts/oc-status.mjs" <run-id>

SYNTHESIZE yourself (do NOT just concatenate): merge into one coherent answer,
resolve contradictions explicitly (state both claims + sources), list open questions
that NO scout could answer.

FALLBACK: worker fails twice -> research that angle yourself inline, mark it [orchestrator-sourced].
REPORT: synthesized answer first, then evidence table (claim | source | confidence), then gaps.
