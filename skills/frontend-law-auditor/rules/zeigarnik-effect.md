# Rule: Zeigarnik Effect

## Why this law matters
- Mechanism: unfinished tasks remain cognitively active.
- User risk when violated: interrupted work is forgotten and never resumed.

## Failure signals
- no visible "in progress" state after interruption.
- returning users cannot easily continue previous step.

## Audit checks
- unfinished flows expose clear resume path.
- `unfinished_resume_path == true`.

## Typical fixes
- persist draft/progress state.
- show "continue where you left off" actions.

## Acceptance criteria
- higher return-to-complete rate for interrupted tasks.
- reduced restart-from-zero behavior.

## Related metrics
- `unfinished_resume_path`
- `progress_visible`
