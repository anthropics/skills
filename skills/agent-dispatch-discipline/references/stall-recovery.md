# Stall Recovery

## What a stall looks like

| Symptom | Meaning |
|---|---|
| Empty reply, or reply with no file reference | nothing was written |
| Named files missing on disk | partial stall — treat like empty |
| Reply claims `done` but tasks are not `[x]` | phantom result — do not dispatch the next batch |
| Replies get slower, vaguer, or ignore instructions | context window filling up — refresh now |

A session that fills its context stops working **silently**. There is no error
to catch; the only defense is the on-disk evidence check after every batch.

## The recovery ladder

1. **Re-dispatch the same batch**, opened with:
   ```
   Nothing was written: <missing paths>. Create <first file> now.
   ```
   The worker complies immediately: first file first, no explanation. Do not
   renegotiate the batch, do not add tasks, do not apologize — the opener is
   the whole message.
2. **Two stalls in a row → fresh session.** Start a new subagent session and
   re-dispatch the same batch with the standard dispatch message. A stalled
   session rarely recovers mid-context; the state on disk is the only thing
   you trust.
3. **Fresh session stalls too → make the batch smaller.** Split the batch in
   half and dispatch one half. If even a 1-task batch stalls, the problem is
   upstream: an ambiguous task, a missing file, or a broken gate. Fix the
   input, not the worker.
4. **Escalate to independent review** when a feature accumulates stalls or
   restarts: a fresh-context reviewer pass over the whole feature is cheaper
   than trusting a session that fought its own context window.

## Context refresh (~70% rule)

Track roughly how much context an active subagent session has consumed. At
~70% of its window: let it finish the current batch, verify on disk, and
continue the next batch in a fresh session. Waiting for visible degradation is
too late — degraded sessions write plausible-looking wrong files, which cost
more to undo than a restart.

Restarting is cheap precisely because the protocol writes state to disk: a
fresh session re-reads the task list and the progress files and continues
where the disk says work stopped. If a worker's restart needs information that
lives only in the old session's chat, the previous batches violated the
file-first rule — fix that, not the restart.

## Count it

Per feature, keep a one-line retro in its progress notes:

```
retro: <n> dispatches · <s> stalls · <r> restarts
```

A stall is a "Nothing was written" re-dispatch; a restart is a re-dispatch in
a fresh session. Rising stall or restart counts are the early-warning signal
for oversized batches or underspecified tasks — react on the trend, not on
the third failure.
