# Strict Mode

Strict mode is opt-in. Use it for release readiness, adversarial review, a requested proof bundle, or work large enough that a lightweight loop no longer provides reliable continuity.

## Evidence

Keep evidence under one project-local result directory chosen with the user or consistent with the repository. Include only artifacts that prove the current game:

- representative start, play, success, and failure frames when those states exist;
- a short win or fail recording only when motion or timing is material;
- rendered WAV files only for authored audio under review;
- a concise note containing controls, commands, observed values, and known limitations.

Do not invent a fixed directory convention when the repository already has one.

## Gate

Run in this order and stop when a gate fails:

1. `validate` has no errors; relevant warnings are resolved or justified.
2. A smoke `run` reaches the intended stop without crash, timeout, or unexpected stall.
3. Captured frames match the requested scenes under direct inspection.
4. Task-specific state predicates pass.
5. Success, failure, retry, and illegal-action paths are checked only when the game defines them.
6. `diff_frames` confirms change only where motion is expected.
7. Every used sound or music target required by the brief renders through `read_audio`.
8. Final behavior and presentation agree with the user's request.

Use `read_palette`, `read_image`, or `read_tilemap` only when their facts answer a gate question. Create a machine-readable report only when the user or downstream automation needs one.

## Scope

Choose proof from the game, not from a generic genre checklist. Sokoban needs a solvable route and rejected illegal pushes; an action game needs collision consequences and reachable terminal states. Neither inherits checks that do not bear on its rules.
