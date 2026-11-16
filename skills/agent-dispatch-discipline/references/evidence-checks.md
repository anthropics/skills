# Evidence Checks

The core rule: **a subagent's chat claim is not evidence.** After every batch,
before dispatching the next one, the orchestrator verifies on disk.

## The per-batch checklist

Run these yourself; each takes seconds:

1. **Tasks marked.** In the feature's task list, every task of the batch is
   `[x]`, and — equally important — every task *outside* the batch is still
   `[ ]`. A worker that "kept going" has broken the batch contract.
2. **Files present.** Every file the batch's tasks claim to create or modify
   exists. Check the first file of the dispatch explicitly — it is the
   canary.
3. **Gates green.** Run the project's gates yourself (test command, build,
   linters). The worker ran them too; running them again is the point — you
   are not verifying the worker's honesty, you are verifying the disk.
4. **Reference resolves.** The worker's one-line reply points at a progress or
   log file that exists and mentions this batch.

Only when all four pass do you dispatch the next batch.

## Rejecting phantom results

| Claim | Check | If it fails |
|---|---|---|
| "Tests pass" | run the tests | stall protocol |
| "Files created" | list them | stall protocol |
| "Task done" (but `[ ]` in task list) | read the task list | re-dispatch with the task named |
| Extra tasks done outside the batch | read the task list + diff | revert or review the extras; never silently accept |

## Worker duties that make evidence possible

Workers keep the disk load-bearing:

- **File before prose.** A created file is progress; reading and planning are
  not. No preamble, no recap, no questions in chat before the first file
  exists.
- **Gate per task.** Run the quality gates and the task's test after every
  task; only then mark `[x]`. Never claim a result you have not executed.
- **One line at the end.** `done <batch> -> <file>` — the file is the report.
- **Logs on disk.** Command output longer than ~20 lines goes to a log file;
  chat keeps the path and the last ~15 lines.

## What the orchestrator never does

- Never mark features done, never edit application code, never fix the
  worker's output directly — rejection and re-dispatch are the tools. Editing
  the output yourself destroys the evidence trail that the reviewer (human or
  subagent) will rely on.
- Never skip the checklist because the worker "usually gets it right". The
  checklist exists for the session that does not.
