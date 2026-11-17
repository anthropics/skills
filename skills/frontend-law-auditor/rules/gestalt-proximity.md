# Rule: Gestalt - Proximity

## Why this law matters
- Mechanism: nearby elements are interpreted as related.
- User risk when violated: label-field confusion and scan friction.

## Failure signals
- related elements are spaced like unrelated sections.
- users misassociate controls with wrong content blocks.

## Audit checks
- internal group spacing is clearly tighter than external spacing.
- `group_spacing_ratio >= 2.0`.

## Typical fixes
- reduce intra-group gaps and increase inter-group separation.
- use consistent spacing scale for component and section levels.

## Acceptance criteria
- faster scanning and fewer association mistakes.
- consistent spacing hierarchy across similar screens.

## Related metrics
- `group_spacing_ratio`
