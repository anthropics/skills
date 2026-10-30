# Rule: Gestalt - Figure/Ground

## Why this law matters
- Mechanism: users must separate foreground task from background noise.
- User risk when violated: modal confusion and wrong-context actions.

## Failure signals
- overlays do not clearly dominate background.
- users interact with background while dialog expects focus.

## Audit checks
- foreground layer is clearly isolated.
- `figure_ground_contrast == true`.

## Typical fixes
- strengthen scrim and layer hierarchy.
- enforce focus trap and clear dismiss/confirm affordances.

## Acceptance criteria
- fewer accidental background interactions during overlays.
- reduced context-loss errors in modal flows.

## Related metrics
- `figure_ground_contrast`
