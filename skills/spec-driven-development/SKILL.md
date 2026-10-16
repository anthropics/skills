---
name: spec-driven-development
description: Run feature work through Spec Driven Development (SDD) — EARS-formatted requirements, a design document, an ordered task list, and objective requirement-to-test traceability with human approval gates. Creates .specs/<feature>/ with requirements.md, design.md and tasks.md, then verifies every R<n> maps to a real, existing test using scripts/check_traceability.py, and records cross-feature decisions as ADRs. Use when starting or planning a new feature, when the user mentions specs, requirements, EARS, SDD, traceability, approval gates, or architecture decision records, or before declaring implementation work done.
author: jordimarsal
version: "1.0"
tags:
  - sdd
  - specs
  - requirements
  - ears
  - traceability
  - testing
---

# Spec Driven Development

Agents drift: they are sharp on one file and lost across a repo. Specs, gates and
traceability fix that — but only when they are written down and checked, not
promised. This skill imposes a small, strict process on any feature big enough
to need more than one file changed.

## When to use (and when not)

Use for any feature that will touch more than a file or two: new endpoints,
new modules, schema changes, behavior changes with edge cases.

Do not create a spec for typo fixes, comment tweaks, or one-line config
changes — say so and just fix them.

## Workflow

```
draft spec → [Spec Gate: human approval] → implement in batches → verify traceability → [Completion Gate: human approval] → done
```

1. **Draft the spec.** Create the feature directory and write the three files
   (formats in [references/spec-files.md](references/spec-files.md)):
   - `.specs/<feature-name>/requirements.md` — EARS-formatted, one `shall` per
     requirement, stable `R<n>` ids (rules in [references/ears.md](references/ears.md))
   - `.specs/<feature-name>/design.md` — files to change, public signatures,
     error cases, discarded alternatives
   - `.specs/<feature-name>/tasks.md` — ordered `T<n>` tasks, each with
     `depends_on` and `refs: R<n>`; sized for 2–4 task batches
2. **Stop at the Spec Gate.** Present the spec to the human and wait for
   explicit approval. Do not start implementing on your own approval. Revise
   in place if changes are requested. When a design decision will bind
   *future* features too (database, transport, pattern, convention), record
   it as an ADR before moving on
   ([references/adr.md](references/adr.md)).
3. **Implement in batches.** Work 2–4 consecutive tasks per pass; a task is
   only checked `[x]` when its change AND its tests exist and pass. Maintain
   the traceability table as you go
   ([references/traceability.md](references/traceability.md)).
4. **Verify objectively.** Run the checker — its verdict, not your confidence,
   decides whether the batch is done:
   ```bash
   python3 scripts/check_traceability.py --feature <feature-name>
   ```
   Exit 0 = covered; exit 1 = gaps to fix; exit 2 = wrong usage.
5. **Stop at the Completion Gate.** Show the human: all tasks `[x]`, green
   test run, checker `PASS`, no `[UNRESOLVED]` rows. Only explicit human
   approval completes the feature.

## Conventions

| Thing | Default | Override |
|---|---|---|
| Spec root | `.specs/` | any directory — keep the per-feature subdirectory shape |
| Tests root | `tests/` | `--tests-dir` on the checker |
| Requirement ids | `R1, R2, …` — never reused | — |
| Task ids | `T1, T2, …` with `refs:` back to requirements | — |

The skill adapts to the repo's language: requirements and specs are written in
the language of the repo's docs; EARS keywords (`shall`, `shall not`) stay in
English.

## Never do

- Never write requirements without testable `shall` statements — if you cannot
  name the test that would verify an R\<n\>, delete or split the requirement.
- Never start implementing before the human approves the spec.
- Never mark a task `[x]` with red or missing tests.
- Never edit the traceability table to make the checker pass — fix the code,
  the tests, or the spec.
- Never self-approve a gate. Gates exist precisely because self-review is the
  failure mode.

---

Part of the [harness](https://github.com/jordimarsal/harness) SDD suite (MIT).
