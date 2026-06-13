# Achieve Playbook

Use this playbook when the user asks for final validation, closure, acceptance, or archival judgment after `/code`.

## Goal

`/achieve` determines whether the delivered result satisfies the frozen acceptance meaning from `90-code-handoff.md`, then records whether the case should be archived as closed evidence or left open.

## Inputs

- the validated bundle
- the latest truthful code run evidence
- the acceptance checks from the handoff
- verification evidence from tests, builds, and browser checks

## Required Output

Write `Runs/<run-id>/03-achieve.md` with:

- verdict
- archive status
- archive reason
- acceptance results
- verification summary
- residual issues
- next actions
- archive references
- evidence references

## Allowed Verdicts

- `achieved`
- `achieved_with_followups`
- `not_achieved`

## Archive Status

- `archived`
- `left_open`

## Rules

- do not weaken acceptance meaning after the fact
- do not call a run achieved if the first-load experience is visibly broken
- if the result is achieved or achieved_with_followups, archive the case as the truthful closure record
- if the result is not achieved, leave the case open and recommend the smallest truthful reopen stage or rerun action
- "archive" here means a recorded closure state inside the bundle, not moving files to a different folder
