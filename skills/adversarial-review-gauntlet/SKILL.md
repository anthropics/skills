---
name: adversarial-review-gauntlet
description: Run a sequential adversarial review (G1-G4) over a finished feature before declaring it done — G1 mechanical correctness (spec trio complete, all tasks checked, traceability gap-free via scripts/gauntlet.sh), G2 adversarial behavior, G3 maintainability, G4 evidence with a written report. A G1 REJECT stops everything. Use after the last implementation batch, before a completion gate or final human approval, when self-reviewing a feature, or when asked to gauntlet, adversarially review, or harden a feature.
author: jordimarsal
version: "1.0"
tags:
  - review
  - testing
  - quality
  - adversarial
  - verification
  - gates
---

# Adversarial Review Gauntlet

One feature review, four passes, in order. The gauntlet runs **once per
feature**, after the last implementation batch and before the completion
gate. It does not replace human gates — it raises what reaches them.

## The four passes

| Pass | Question | Gate |
|---|---|---|
| **G1 — Correctness** | Is the mechanics green: spec trio complete, every task `[x]`, every requirement traced to a real test? | Mechanical: `scripts/gauntlet.sh --feature <name>` exit 0 |
| **G2 — Adversarial** | Malicious input, 10k concurrent, null/empty/negative, races, tests that assert nothing | Agent judgment, recorded per finding |
| **G3 — Maintainability** | Architecture respected, conventions followed, no blanket `except`, I/O at the edges | Agent judgment + project gates green |
| **G4 — Evidence** | Logs on disk, report complete, nothing claimed without a path | Report file exists with 4 PASS lines |

A G1 REJECT **stops the gauntlet** — no judgment pass runs on a feature whose
mechanics are red. Fix first, re-run from G1.

## Workflow

1. Run G1 yourself:
   ```bash
   bash scripts/gauntlet.sh --feature <name>
   ```
   Non-zero → stop, fix, re-run. Save the output to a log (e.g.
   `logs/<feature>/gauntlet-g1.log`).
2. Walk G2 and G3 against the diff **with fresh eyes**: re-read every changed
   file top to bottom instead of trusting batch memory. Log findings as you
   go. Each finding is either **fixed** or **defended** — a defense names the
   trade-off in one line and still counts as a pass.
3. Confirm the project gates are green, then write the report file
   ([references/report-format.md](references/report-format.md)). Verdict is
   `PASS` only when all four pass-lines say PASS.
4. Present the report with the completion request.

## Depth scaling

| Feature size | Depth |
|---|---|
| Trivial (1 file) | G1 + G4 only; note G2/G3 as `skipped (trivial)` with a one-line reason |
| Medium (2–3 files) | G1–G4 in one sitting, one finding round max |
| Complex | Full G1–G4 with a fix round before re-run |

## Escalate to an independent reviewer when

- the feature has more than ~12 tasks;
- critical files changed (auth, payments, migrations, infra);
- G2/G3 would be self-reviewed by the session that wrote the code and no
  mechanical gate covers the doubt.

Fresh context beats speed there — that is the entire value of a second
session.

## Never do

- Never run judgment passes on red mechanics.
- Never mark a pass without its log or its report line — a pass without
  evidence is not a pass.
- Never "fix" the code inside the review: findings go back to the implementer
  as one batch, then the gauntlet re-runs from G1.
- Never let a defended finding pass without naming its trade-off.

Pass details: [references/passes.md](references/passes.md)

---

Part of the [harness](https://github.com/jordimarsal/harness) SDD suite (MIT).
