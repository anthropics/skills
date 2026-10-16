# Batching and Dispatch

## Batch construction

A batch is a set of **consecutive** tasks from the feature's task list forming
one coherent unit: a change plus the tests that verify it. Consecutive matters
— batch `n+1` must be startable from the files batch `n` leaves behind.

- Default 2–3 tasks. A single large task (migration + repository + tests) is a
  batch of 1. Four only for small clones. **Never five or more** — an
  oversized or unbounded batch is exactly how a session stalls and ends having
  written nothing.
- Keep dependency chains shallow when writing the task list; if a task cannot
  start before a non-adjacent task finishes, the batching is wrong.
- Workers work **only** on their batch's tasks and leave every other task
  `[ ]`. No "keeping going" once the batch is done — stop and answer.

## Dispatch message anatomy

```
Batch T8–T11 of <feature>. First file: src/orders/refund.py.
Gates: <project's test command> green; tasks marked [x] in tasks.md.
```

Carry exactly: the batch ids, the first file to create, the gates to reach.
Nothing else. The protocol lives in the worker's instructions, not in every
dispatch — re-explaining it wastes the context the worker needs for the work.

Never paste large command outputs into dispatch prompts, and never ask for
them back in chat: workers archive outputs longer than ~20 lines under a logs
directory (e.g. `logs/<feature>/T<n>.log`); replies reference the path plus a
short excerpt. Re-running a command beats re-pasting an old log.

## Reply contract

The worker's final response is **one line**, sent only when every task of the
batch is `[x]` and the gates are green:

```
done T8-T11 -> <path to its progress/log file>
```

or, when it had to stop:

```
blocked T10 -> <path to its progress/log file>
```

Never return full diffs, test output, or summaries in chat. The orchestrator
reads disk when it needs detail. This is the anti-telephone-cord rule: results
flow through files; chat carries only references.

## Parallelism

- Only tasks with no `depends_on` between them may be dispatched to separate
  worker sessions simultaneously.
- At most **one feature** is in progress at a time, always.
- Dependent tasks wait for their dependencies to be verified on disk first.

## Effort scaling

| Complexity | Sessions |
|---|---|
| Trivial (1 file) | 1 spec pass → human gate → 1 worker |
| Medium (2–3 files) | 1 spec pass → human gate → 1 worker → 1 reviewer |
| Complex (refactor) | 2–3 explorers → 1 spec pass → human gate → 1 worker → 1 reviewer |
| Very complex | split into sub-features and re-apply this table |

A reviewer reviews the **whole feature in one pass** — batching is a
worker-side discipline, not a review-side one. Fresh context is the entire
value of a separate reviewer; when verification is subjective or critical
files changed, escalate to a real independent review instead of self-review.
