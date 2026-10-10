---
name: red-green-proof
description: Turns a suspected bug into a proven one. Verify the cause against reality before claiming it, write a test that FAILS on the current code, apply the fix, watch it pass — then revert the fix and confirm the test goes red again, because a test that passes both ways proves nothing. Invoked bare after a debugging conversation, it takes the target from context rather than asking. Use when fixing a bug, investigating an incident, hardening a flaky area, or when asked to "add tests that reveal the bug". Triggers on "/red-green-proof", "prove the bug", "red-green", "make the test fail first", "is that test load-bearing", "reveal the bug with a test".
---

# Red-Green-Proof

A bug is not fixed because the tests pass. A bug is fixed when a test **fails without your fix and passes with it**, and you have watched it do both.

Most "regression tests" written after a fix never had the chance to fail. They are decoration. This skill is the discipline that separates a real test from a decorative one.

## Picking the target

**With an argument**, that is the target: `/red-green-proof the status endpoint reports finished runs as running`.

**With no argument, take the target from the conversation.** The usual case is that you have just spent a long stretch investigating something — the bug is already on screen. Do not ask what to work on. Scan back through the session and pick, in this order:

1. A defect just identified but not yet fixed.
2. A fix applied without a failing test to back it — the most valuable target, because the test still has to be proven load-bearing.
3. A test written but never verified red.
4. Something described as "still open", "not fixed yet", or "characterization only".

State your pick in one line and start:

> Target: the buffer discards events when the flush write fails (`checkpointBuffer.ts:271`). Verifying before writing the test.

Only ask the user if two or more candidates are genuinely equal in priority — then list them as a short numbered choice and stop. If several *related* defects came up, handle them one at a time through the full loop rather than batching; each needs its own red.

If nothing in the conversation qualifies, say so and ask for a target rather than inventing one.

## The loop

Run these in order. Do not skip 1, and never skip 4.

### 1. Verify the cause. Do not infer it.

Before you write a line of test code, establish what actually happened using evidence you can point at: the real record from the database or API, the real log line, the actual source of the function you are blaming.

Say which of these you have:

- **Proven** — I read the value / ran the code / pulled the record.
- **Inferred** — consistent with the evidence, but I have not confirmed it.
- **Unknown** — I cannot determine this from what is available.

State the label out loud. If the honest answer is Unknown, say so and name the one artifact that would settle it. A confident wrong cause costs more than an admitted gap, because it sends the fix to the wrong place.

Two traps worth naming:
- **A plausible mechanism is not the mechanism.** Rank candidates, then go rule them out one at a time by reading code, not by reasoning about it.
- **Check whether the "bug" was deliberate.** `git log -S '<the exact line>'` and read the commit. If a test already asserts the current behaviour, someone may have wanted it. Understand why before you invert it.

### 2. Write the test. Watch it fail.

The test must fail **against the code as it is right now**, before any fix exists.

Name it after the defect, not the function: `reveals bug: stale status shadows a terminal event`, not `test inferStatus`.

Assert the observable consequence a user or caller would see — the wrong status, the lost record, the 500 — not an internal call count. Call counts pass for the wrong reasons.

If it does not fail, you have not reproduced the bug. Go back to step 1.

### 3. Fix it.

Smallest change that makes the failing test pass. If the fix needs to be large, the test was probably too broad — narrow it and split.

### 4. Revert the fix. Confirm red. ← the whole point

Put the buggy code back, run the test, and **watch it fail**. Then restore the fix.

```bash
cp path/to/fixed.ts /tmp/fix.bak
# revert the fix (edit, patch, or git stash the single file)
<run the specific test>          # MUST fail here
cp /tmp/fix.bak path/to/fixed.ts
<run the specific test>          # green again
```

If it stayed green, **the test is fake**. Not "probably fine" — fake. Rewrite it and repeat.

This is not paranoia. It catches a specific, common failure: a test that exercises a path adjacent to the bug rather than the bug. Two real examples:

- A concurrency test modelled two writers but had no `await` between each writer's read and its write. Both ran to completion atomically, never interleaved, and the test passed with the lock removed. Fix: add latency between read and write, mirroring the real network gap.
- A fault-isolation test asserted "no 500 when the store fails", but the injected failure was a *missing* record, which the loader turns into `null` rather than throwing. The error path never ran. Fix: inject a real 500.

Both looked correct on the page. Only the revert exposed them.

### 5. Run everything.

The full suite, plus type checks. A fix that corrects one behaviour often contradicts a test that pinned the old one — which is a finding, not an annoyance. Go read that test and decide deliberately (see step 1).

## When you cannot get a true red

Sometimes the buggy code cannot be invoked: it is a closure inside a 3,000-line factory, a route handler, a private method. Do not fake a behavioural test. Pick one of these and **label it in the file header**:

| Type | Use when | Honesty requirement |
|---|---|---|
| **Extract, then test** | The logic can be moved to a module with injected dependencies | Preferred. Do this if the extraction is small. |
| **Structural test** | The call site cannot be reached, but the invariant is visible in the source | Scan the source and assert the property (e.g. "every write cycle sits inside the lock"). It will name offenders itself. Say in the header that it is structural and should be replaced when the code becomes reachable. |
| **Model test** | Testing an interaction between components you cannot both instantiate | Mirror the real code field-for-field, cite the file:line it models, and note in the header that it is a model. Extra important to run step 4 — models are where fake tests hide. |
| **Characterization test** | Documenting current behaviour you are not fixing yet | Name it as such. Do not call it a regression test. Flag that it will invert when the bug is fixed. |

## Reporting

When you present the work, include:

- What you **proved** vs **inferred** vs still do not know.
- The **revert output** — the actual failure line, not a claim that it failed.
- Which tests are behavioural, structural, model, or characterization.
- Anything you got wrong earlier in the investigation, corrected explicitly.

Do not describe a test as "revealing the bug" unless you have seen it red.

## Anti-patterns

- Writing the test after the fix and never reverting → decoration.
- Asserting a mock was called instead of the user-visible outcome → passes for the wrong reason.
- Widening a test until it passes → deleting the signal.
- Inverting a pre-existing test because it blocks you → check the history first; it may encode a decision.
- Reporting "all green" as success when nothing was ever red.

## One-line version

Red first, green second, **red again on purpose**, then green — and say which parts you actually proved.
