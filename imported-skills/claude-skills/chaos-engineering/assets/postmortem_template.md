# Chaos Experiment Postmortem

## Identity

- **Experiment:** `<experiment_id>`
- **Date:** `<YYYY-MM-DD>`
- **Target:** `<service>`
- **Owner:** `<handle@team>`
- **Postmortem facilitator:** `<handle@team>`

## Hypothesis

> `<hypothesis from the plan>`

## Outcome

- [ ] **Held** — hypothesis confirmed
- [ ] **Refuted** — hypothesis disproven
- [ ] **Inconclusive** — could not tell

## Timeline

| Time | Event |
|---|---|
| T-5min | Started baseline measurement |
| T+0 | Attack injected |
| T+? | `<observation>` |
| T+? | `<observation>` |
| T+N | Attack ended (or aborted) |
| T+N+2 | Steady state recovered |

## What we learned

`<at least one concrete learning — required>`

## What surprised us

`<unexpected observations; "nothing surprised us" is a signal that you didn't push hard enough>`

## What failed

`<things that broke during the experiment that shouldn't have>`

## What held

`<things that worked as expected — confidence-building data points>`

## Root causes (if any failures)

`<technical analysis without blame>`

## Follow-up actions

| Action | Owner | Due | Status |
|---|---|---|---|
| `<concrete action>` | `<@owner>` | `<date>` | `[ ]` |
| `<concrete action>` | `<@owner>` | `<date>` | `[ ]` |

> Every experiment should produce ≥1 follow-up. If none — re-examine whether you tested anything new.

## Next experiment

`<what's the next experiment that builds on this learning?>`

## Stakeholder summary (1-2 sentences)

`<for the team channel; describe outcome and biggest learning>`
