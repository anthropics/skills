# Rule: Serial Position Effect

## Why this law matters
- Mechanism: first and last items are recalled better than middle items.
- User risk when violated: key actions hidden in low-recall positions.

## Failure signals
- important actions are placed in the middle of dense menus.
- users overlook required critical controls.

## Audit checks
- critical actions are placed at beginning or end of sequences.
- `critical_actions_boundary_placement == true`.

## Typical fixes
- reorder navigation/action rows by priority.
- move support/cart/logout/checkout to boundary positions as appropriate.

## Acceptance criteria
- higher discovery rate of critical actions.
- lower miss rate on key menu operations.

## Related metrics
- `critical_actions_boundary_placement`
