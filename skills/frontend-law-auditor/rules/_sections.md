# Frontend Law Auditor Rule Index

Use these files for deep diagnosis after running `scripts/law_audit.py`.

## P0 Critical

- `fitts-law.md`
- `hicks-law.md`
- `doherty-threshold.md`

## P1 High

- `gestalt-proximity.md`
- `gestalt-similarity.md`
- `gestalt-focal-point.md`
- `millers-law.md`
- `teslers-law.md`
- `postels-law.md`
- `peak-end-rule.md`
- `jakobs-law.md`

## P2 Medium

- `gestalt-continuity.md`
- `gestalt-closure.md`
- `gestalt-figure-ground.md`
- `gestalt-common-fate.md`
- `von-restorff-effect.md`
- `goal-gradient-hypothesis.md`
- `zeigarnik-effect.md`
- `serial-position-effect.md`
- `occams-razor.md`
- `parkinsons-law.md`

## Rule Loading Guidance

- Load only failed rule files first.
- If a rule is `unknown`, load the rule file plus `references/metrics-schema.md`.
- For cross-law conflicts, prioritize completion-critical and safety-critical flows first.
