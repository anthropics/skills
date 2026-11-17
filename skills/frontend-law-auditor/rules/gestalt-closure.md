# Rule: Gestalt - Closure

## Why this law matters
- Mechanism: users mentally complete incomplete visual structures.
- User risk when violated: ambiguous icons and unclear progress states.

## Failure signals
- partial visuals cannot be reliably interpreted.
- users ask "what does this symbol/shape mean?"

## Audit checks
- partial structures remain understandable without extra text.
- `closure_support == true`.

## Typical fixes
- simplify only when recognition remains obvious.
- add minimal context cues for ambiguous partial shapes.

## Acceptance criteria
- users interpret partial indicators correctly on first pass.
- no support tickets tied to unclear symbolic states.

## Related metrics
- `closure_support`
