# Rule: Gestalt - Similarity

## Why this law matters
- Mechanism: visually similar elements are assumed functionally similar.
- User risk when violated: role confusion and misclicks.

## Failure signals
- same-role controls use conflicting visual styles.
- users hesitate when mapping control meaning.

## Audit checks
- role-level style rules are tokenized and consistent.
- `role_style_consistency == true`.

## Typical fixes
- unify color, shape, weight, and icon style by role.
- restrict ad hoc styling exceptions in core flows.

## Acceptance criteria
- users can predict function from appearance.
- reduced misuse of secondary/destructive actions.

## Related metrics
- `role_style_consistency`
