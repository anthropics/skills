---
name: reasoning-quality-gate
description: Three-gate quality pipeline for high-stakes deliverables — calibrate before starting, adversarially refute the draft, then verify by deliberately trying to break the result. Use when the cost of a confidently-wrong answer is high (production changes, published analyses, irreversible actions) and a plain self-review is not enough.
license: Complete terms in LICENSE.txt
---

# Reasoning Quality Gate

Run a deliverable through three sequential gates. Each gate has a falsification bias: the goal is to make the work fail, not to confirm it. A deliverable that survives all three gates ships with evidence attached; one that fails any gate goes back, and the failure itself is reported.

These gates are distilled from production multi-agent patterns: the refutation gate follows the default-refute consensus pattern used in multi-agent verification pipelines, and the verification gate follows the "break it on purpose" discipline used before declaring builds done.

## When to apply

```
Deliverable ready to ship → Is a wrong answer expensive?
    ├─ No (low stakes, easily reversible) → Skip the gates, ship
    └─ Yes → Is it a claim/analysis or an artifact (code, config, doc)?
        ├─ Claim or analysis → Gates 1 + 2 (calibrate, refute)
        └─ Artifact → All three gates (calibrate, refute, break-test)
```

Do not run the gates on trivial edits or conversational answers — the overhead must be smaller than the cost of the error it prevents.

## Gate 1: Pre-task calibration (before starting)

Before producing the deliverable, write down — briefly, in the working notes, not for the user:

1. **Success criterion**: one sentence stating what "correct" means for this task, checkable after the fact.
2. **Failure modes**: the 2–3 most likely ways this specific task goes wrong (wrong assumption, stale data, missed edge case, misread requirement).
3. **Confidence budget**: which parts of the plan rest on verified facts vs. on assumptions. Mark each assumption explicitly.
4. **Kill criterion**: what observation would mean "stop and re-plan" rather than "push through."

If step 3 shows the plan rests mostly on assumptions, verify the load-bearing ones first — reading the actual file, running the actual command — before building anything on top of them.

## Gate 2: Adversarial refutation (on the draft)

Review the finished draft with the burden of proof inverted: **the draft is presumed wrong until each key claim survives an attack.**

For each load-bearing claim or design decision in the draft:

1. State the strongest concrete counter-argument, not a token objection. If the claim is empirical, name the specific input or state that would disprove it.
2. Attempt the disproof cheaply where possible: check the source, run the command, read the referenced code. Prefer a 1-minute test over a confident memory.
3. Apply the default-refute rule: **if the claim cannot be confirmed or refuted, treat it as refuted.** Uncertain claims do not pass by default — they get removed, hedged with their actual confidence level, or verified.

When more rigor is warranted (irreversible actions, published claims), run the refutation as independent passes with distinct lenses — correctness, security, "does it reproduce" — rather than one general re-read. Diverse lenses catch failure modes that repeated identical review does not.

Output of this gate: a list of claims that survived, claims that were cut or downgraded, and why. If nothing was cut or downgraded, that is a warning sign the review was confirmatory — do one more pass targeting the claim you are most attached to.

## Gate 3: Delivery verification (on the artifact)

Never declare an artifact done based on reading it. Verify by execution, in this order:

1. **Run it live** on real inputs — not the happy-path example it was built against.
2. **Break it on purpose**: feed it empty input, a missing dependency, a wrong path, malformed data. It should fail loudly and comprehensibly, not silently succeed or silently do nothing.
3. **Check the visibility layer**: confirm there is a counter, log line, or output that *proves* the artifact did its work. "No errors" is not proof of work — silent success and silent failure look identical. If nothing observable distinguishes "it worked" from "it never ran," fix that before shipping.
4. **Re-run after any fix** — a fix invalidates prior verification.

Ship with a verdict and its evidence: ✅ (ran live, broke it, saw it fail loudly, saw proof of work), ⚠️ (works with a named, specific caveat), or ❌ (does not ship). Only ✅ or an explicitly accepted ⚠️ counts as done.

## Reporting

The gate results travel with the deliverable. Report:

- What was assumed vs. verified (Gate 1)
- What was cut, hedged, or survived attack (Gate 2)
- What was executed and what the failure behavior looked like (Gate 3)

A deliverable presented without its gate evidence should be treated as ungated.
