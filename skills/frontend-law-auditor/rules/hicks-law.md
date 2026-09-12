# Rule: Hick's Law

## Why this law matters
- Mechanism: decision latency grows as visible options grow.
- User risk when violated: hesitation, choice paralysis, abandonment.

## Failure signals
- high option density on single screens.
- users take too long before first meaningful action.

## Audit checks
- `screen_choice_count <= 7` for primary decision steps.
- `progressive_disclosure == true` for advanced options.

## Typical fixes
- reduce concurrent options and group related actions.
- hide advanced settings under "More" or later steps.

## Acceptance criteria
- first-action latency improves after reduction of choice load.
- abandonment rate decreases on high-friction steps.

## Related metrics
- `screen_choice_count`
- `progressive_disclosure`
