# Rule: Gestalt - Common Fate

## Why this law matters
- Mechanism: elements moving together are perceived as belonging together.
- User risk when violated: motion semantics feel random and misleading.

## Failure signals
- related items animate with mismatched direction/speed.
- users fail to understand grouped changes.

## Audit checks
- grouped transitions share consistent motion behavior.
- `motion_group_consistency == true`.

## Typical fixes
- standardize easing, duration, and direction by motion group.
- avoid unrelated animations competing with core transition.

## Acceptance criteria
- improved comprehension of grouped state changes.
- fewer misinterpretations in dynamic panels/menus.

## Related metrics
- `motion_group_consistency`
