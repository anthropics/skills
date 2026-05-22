# Rule: Doherty Threshold

## Why this law matters
- Mechanism: rapid feedback preserves user cognitive flow.
- User risk when violated: duplicate taps, uncertainty, drop-off.

## Failure signals
- no immediate pressed/loading state after action.
- p95 feedback time exceeds control threshold.

## Audit checks
- `feedback_ms_p95 <= 400`.
- all async actions provide immediate visual acknowledgment.

## Typical fixes
- add instant pressed/loading state.
- use skeletons, optimistic UI, and staged rendering.

## Acceptance criteria
- p95 intent-to-feedback under threshold.
- reduced duplicate submit events.

## Related metrics
- `feedback_ms_p95`
