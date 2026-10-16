# Log Delegation (reading big logs without burning context)

One goal: a big log must never be read end-to-end by the orchestrating
session. Reading is not judging — delegate the pattern-matching, verify the
evidence, keep your context for the verdict.

## When to dispatch

The log (test run, build, server log) is bigger than ~200 lines, or the need
is "where did it fail and why" rather than the full content. Under that,
`grep -n` / `sed -n 'A,Bp'` beats a dispatch — do it yourself.

## Dispatch

- One subagent, **read-only**: it must not edit files, run the project's
  gates, or fix anything. Its only needs are reading the log and running
  read-only commands (`grep`, `sed -n`, `wc`).
- If the runtime allows choosing a model per dispatch, pick a cheap, fast
  model — the task is pattern-matching, not judgment. If it does not,
  dispatch the default model: the protocol still pays, because the log never
  enters the dispatcher's context.
- The prompt carries three things: the log path, the question
  (e.g. "which tests failed, and the first underlying error"), and the
  evidence format below. Nothing else.

## Evidence format (what the reader must return)

For each finding, one block:

```
file: <path>
lines: <A-B>
quote: |
  <up to 3 verbatim lines>
command: <the read-only command that produced it>
```

- No summaries without quotes. No recommendations.
- The answer is not in the log → reply `not found`. Do not speculate.
- Reply in chat: evidence blocks are small by construction. If the reply is
  getting big, the protocol is being violated — narrow the question.

## Verification (dispatcher's duty, non-negotiable)

1. Re-run every `command` and re-read the cited `lines` in the original file.
2. Quotes match → adopt the evidence.
3. Any mismatch, invented path, or quote that does not appear verbatim →
   discard **all** of the reader's evidence and read the exact ranges
   yourself with `grep -n` / `sed -n`. Never salvage partial evidence — one
   fabricated quote poisons the whole batch.
