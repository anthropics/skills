# Rule: Fitts's Law

## Why this law matters
- Mechanism: interaction time increases with distance and decreases with target size.
- User risk when violated: slow completion, mis-taps, repeated attempts.

## Failure signals
- critical controls are small or far from task endpoint.
- users overshoot or repeatedly tap near misses.

## Audit checks
- `min_target_size_px >= 44` for critical actions.
- `critical_action_at_task_end == true` and reach in natural/stretch zones.

## Typical fixes
- increase hit area using padding/wrapper targets.
- move submit/continue to where the user naturally finishes the task.

## Acceptance criteria
- no critical target below 44px.
- measured reduction in tap errors or correction taps.

## Related metrics
- `min_target_size_px`
- `primary_action_reach`
- `critical_action_at_task_end`
