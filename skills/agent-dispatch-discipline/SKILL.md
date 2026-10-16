---
name: agent-dispatch-discipline
description: Orchestrate subagent work without stalls, drift, or phantom results — batch sizing (2-4 tasks per dispatch, never 5+), dispatch message anatomy, on-disk evidence checks after every batch, the "Nothing was written" re-dispatch opener, fresh-session restarts at ~70% context, and result-to-file replies. Use when dispatching work to subagents, coordinating multi-agent sessions, or when a subagent returns an empty reply, claims results without files, or degrades as its context fills.
author: jordimarsal
version: "1.0"
tags:
  - agents
  - subagents
  - orchestration
  - batching
  - stalls
  - multi-agent
---

# Agent Dispatch Discipline

Subagent sessions stall, drift, and sometimes claim work they never did. A full
context window stops working **silently** — no error, just nothing written. This
skill is the dispatch protocol that keeps an orchestrating session and its
subagents productive.

## When to use

Any time you (the orchestrating session) hand work to subagents: implementing a
feature from a task list, parallel research, bulk refactoring. Pairs naturally
with the spec-driven-development skill — its `tasks.md` files are sized
exactly for this protocol — but works on any ordered task list.

## The five rules

1. **One dispatch = one batch.** Never hand a whole feature to a single
   subagent session.
   | Batch size | When |
   |---|---|
   | 2–3 tasks | default — one coherent unit: a change plus its tests |
   | 1 task | a single large task (migration + module + test suite) |
   | 4 tasks | only when the tasks are small clones (e.g. four similar adapters) |
   | 5+ tasks | never — oversized batches stall and return nothing written |

2. **Dispatch prompts are minimal.** Name the batch's task ids (e.g. `T8–T11`),
   the first file to create, and the gates to reach — nothing else. Do not
   re-explain the protocol; the worker's own instructions carry it. Never paste
   large command outputs into a dispatch prompt.

3. **Evidence lives on disk, not in chat.** After every batch, verify before
   dispatching the next one: tasks really marked `[x]` in the task list, files
   actually present, gates run **by you**. A subagent's chat claim is not
   evidence ([references/evidence-checks.md](references/evidence-checks.md)).

4. **Stalled batch → one re-dispatch, then a fresh session.** Empty reply or
   missing files means the batch stalled: re-dispatch the **same** batch
   opened with:
   ```
   Nothing was written: <missing paths>. Create <first file> now.
   ```
   Two stalls in a row → start a fresh subagent session for that batch
   ([references/stall-recovery.md](references/stall-recovery.md)).

5. **Refresh at ~70% context.** Once a subagent session approaches ~70% of its
   context window, finish the batch and continue in a fresh session. Do not
   wait for visible degradation — by then it has already been producing
   garbage.

## Worker-side mirror

Discipline is bilateral. A dispatched worker: writes files before any prose;
runs the gates after every task and only then marks it `[x]`; never claims a
result it did not execute; keeps replies to one line pointing at files
(`done T8-T11 -> progress file`); on receiving the "Nothing was written"
opener, complies immediately — first file first, no explanation.

## Orchestrator never does

- Never implement the work yourself — you decompose, dispatch, and verify.
- Never accept results delivered only in chat, without a file reference.
- Never dispatch a second feature while one is `in_progress`.
- Never let a worker pull tasks from another feature into its batch.
- Never let a worker improvise around a failing tool or invent requirements —
  the correct moves are `blocked` reports and spec-change requests.

Deep dives: [references/batching-and-dispatch.md](references/batching-and-dispatch.md) ·
[references/stall-recovery.md](references/stall-recovery.md) ·
[references/evidence-checks.md](references/evidence-checks.md)

---

Part of the [harness](https://github.com/jordimarsal/harness) SDD suite (MIT).
