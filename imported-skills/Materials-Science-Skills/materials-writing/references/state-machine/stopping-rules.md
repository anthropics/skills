# Stopping Rules

The writing state machine stops revision loops when continuing would hide risk,
waste review effort, or imply evidence that does not exist.

## Stop Conditions

1. `max_rounds`: maximum three full revision rounds.
2. `low_gain`: two consecutive score improvements below 0.5.
3. `missing_evidence`: missing key evidence blocks a manuscript-level claim.
4. `specialist_conflict`: unresolved specialist conflict or project constraint conflict.
5. `target_reached`: target threshold reached for the declared writing mode.

## Required Stop Report

When any stop condition is met, report:

- current score/status
- remaining risks
- why the loop stopped
- one next action

## Continue Conditions

Continue only when the next revision has a clear target, the required evidence
exists or can be marked honestly, and the expected improvement is larger than
local wording cleanup.

## Mode Notes

- `compose`: stop before prose when foundation files cannot support a
  one-sentence argument.
- `revise`: stop when requested edits require evidence or author decisions the
  draft does not contain.
- `hybrid`: stop when old draft text conflicts with the research canon.
- `qa`: stop immediately after scoring if no rewrite was requested.
