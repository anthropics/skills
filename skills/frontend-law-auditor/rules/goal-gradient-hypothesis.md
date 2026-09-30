# Rule: Goal-Gradient Hypothesis

## Why this law matters
- Mechanism: motivation increases as users approach completion.
- User risk when violated: late-stage abandonment from invisible progress.

## Failure signals
- users cannot tell how close they are to finishing.
- progress feels static even after completing steps.

## Audit checks
- visible progress exists throughout staged flows.
- `progress_visible == true`.

## Typical fixes
- add explicit step counters/percent bars.
- reinforce milestone completion with subtle success cues.

## Acceptance criteria
- higher completion in last-third of flow.
- lower abandonment after mid-flow.

## Related metrics
- `progress_visible`
