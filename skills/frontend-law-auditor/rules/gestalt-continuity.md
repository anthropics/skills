# Rule: Gestalt - Continuity

## Why this law matters
- Mechanism: eyes follow continuous paths and expected direction.
- User risk when violated: broken scan flow and hidden next steps.

## Failure signals
- list/carousel/step flow has abrupt breaks.
- users miss off-screen continuation.

## Audit checks
- progression cues exist (peek, arrow, stepper path).
- `continuity_cue == true`.

## Typical fixes
- align content edges and motion direction.
- reveal next-state hints at viewport boundaries.

## Acceptance criteria
- higher discovery of next actions/content.
- fewer dead-end pauses during scanning.

## Related metrics
- `continuity_cue`
