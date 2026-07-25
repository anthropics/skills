# Loop Discovery

Use this workflow when the user asks to mine a codebase, coding-thread history,
or both for work that should become a loop.

## Inspect the evidence

1. Confirm the smallest discoverable scope from the request. Inspect the current
   repository when it is clearly in scope. Use available thread listing, search,
   and reading tools only for coding threads the user authorized. If thread
   history is unavailable, continue with codebase evidence and disclose the
   limitation.
2. In code, inspect the operational paths that reveal recurring work: scripts,
   CI and deployment configuration, maintenance commands, tests, contributor
   instructions, issue templates, runbooks, and repeated lifecycle patterns.
   Similar-looking functions alone are a refactoring signal, not proof of a
   loop.
3. In threads, identify completed actions and their outcomes. Group semantically
   equivalent work even when the wording differs. Count distinct occurrences,
   not repeated discussion of the same occurrence. Record a compact source
   handle such as a thread title or identifier and the action performed; do not
   copy secrets or unnecessary private content.
4. Corroborate thread claims against the repository or runtime when practical.
   Thread history can be stale, incomplete, or mistaken.

## Qualify and rank candidates

A repeated task is not automatically a good loop. Require the candidate to
follow the feedback-cycle and validation rules in `SKILL.md`, not merely to
appear multiple times in code or thread history.

A candidate is loop-shaped only when all of these are present or can be derived
from scoped evidence:

- a recurring event or state to observe;
- a next action that can change in response to fresh feedback;
- an observable check for whether the action helped;
- a bounded scope and a success, no-op, blocked, approval-required, or
  no-progress stop as appropriate.

Require at least two distinct occurrences before describing a thread-derived
task as repeated. A codebase pattern without run history may be reported as a
potential loop, but not as proven recurrent. Reject one-shot migrations,
straight-line checklists, vague goals, and tasks where another pass receives no
new evidence.

Rank qualified candidates by evidence of recurrence, time or failure cost,
quality of available feedback, reversibility, and safe authority. Do not invent
frequency, effort saved, owners, schedules, metrics, or permissions. Prefer the
smallest high-value loop over a broad loop that bundles unrelated work.

## Convert the best candidate

1. Search the live catalog using the candidate's outcome, trigger, action, and
   verification terms. Adapt a strong published match instead of duplicating
   it. If the catalog is unavailable, continue with an explicitly unpublished
   design and disclose that duplication could not be checked.
2. If several candidates are similarly strong or differ materially in
   authority, show a short ranked slate and ask the user which one to convert.
   Otherwise convert the strongest candidate directly.
3. Derive the trigger, fresh observation, bounded action, reproducible
   verification, record, and terminal behavior from the evidence. Apply every
   design rule in `SKILL.md`; do not weaken the standard because recurrence is
   well documented. Ask one short question only when a missing decision would
   materially change safety or success.
4. Run the mandatory crafted-loop preflight in `SKILL.md`. Repair material
   weaknesses before delivery without expanding authority or inventing missing
   details.
5. Return the compact evidence and the loop using the standard delivery format
   in `SKILL.md`. Label it as an unpublished design or adaptation. If no
   candidate qualifies, report a clean no-op and explain the missing feedback
   or recurrence evidence; do not manufacture a loop.
