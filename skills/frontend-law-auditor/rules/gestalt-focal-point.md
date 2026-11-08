# Rule: Gestalt - Focal Point

## Why this law matters
- Mechanism: strongest contrast captures first attention.
- User risk when violated: users cannot tell what to do first.

## Failure signals
- multiple elements compete as primary action.
- primary flow action is visually diluted.

## Audit checks
- exactly one dominant focus anchor exists per screen.
- `focal_points == 1`.

## Typical fixes
- reduce competing highlights and preserve one primary CTA.
- use contrast hierarchy intentionally, not uniformly.

## Acceptance criteria
- faster first meaningful action.
- better primary CTA click concentration.

## Related metrics
- `focal_points`
- `primary_cta_count`
