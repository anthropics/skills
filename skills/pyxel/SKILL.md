---
name: pyxel
description: Use when the user asks to make, modify, or verify a Pyxel game or retro/pixel-art game in Python. Do not use for non-Pyxel engines or general Python work.
license: MIT
---

# pyxel

Build Pyxel games with the smallest workflow that can honestly prove the game works. Modern models do not need a ceremony-heavy pipeline; use pyxel-mcp to observe reality, then apply game-specific judgment.

## Runtime

The host should expose the `pyxel` MCP namespace from `pyxel-mcp >= 1.0.0`. Use these tools as observation verbs, not judges:

- `validate` before the first run or after structural edits.
- `run` as the primary loop: scheduled inputs plus `state`, `screen_image`, `screen_grid`, `layout`, or `video` snapshots.
- `read_image`, `read_animation`, `read_audio`, `read_palette`, `read_tilemap`, and `diff_frames` only when the current task needs that specific observation.
- `pyxel_info` when debugging setup or finding bundled examples/resources.

If pyxel-mcp is missing or older than 1.0.0, ask the user to install/register `pyxel-mcp >= 1.0.0`, normally with `uvx pyxel-mcp install`. If installation or MCP access is blocked, use direct Pyxel headless runs only as a temporary fallback: `py_compile` or focused tests for logic plus `pyxel.init(headless=True)` and `pyxel.screenshot()`. Say verification is weaker until pyxel-mcp is available.

## Default Loop

1. Pick the smallest playable scope that satisfies the user's request. Ask only for missing constraints that materially change the game.
2. Build a complete first slice: title or start state, controls, one objective, one failure/retry path when the genre needs it.
3. Run `validate`. Fix syntax and Pyxel footguns before dynamic runs.
4. Run the game headlessly with `run`; capture at least one `state` snapshot and one `screen_image` on the path being verified.
5. Inspect the captured PNG yourself for the task-specific result, not just nonblank pixels. State values prove mechanics; pixels prove what the player actually sees.
6. Iterate on observed defects. Do not create PLAN/STRUCTURE/ASSETS/MEMORY files unless the project is large enough that they reduce confusion.
7. Hand off with controls, changed files, and exact verification commands/results.

## Minimum Verification

Every game needs:

- `validate` clean.
- A smoke `run` that reaches the intended frame count.
- At least one captured frame inspected visually.
- One task-specific predicate checked from `state` snapshots.

Add only genre-relevant checks:

- Puzzle: solvable path, invalid move rejection, reset/undo if present.
- Platformer/action: win/fail path, collision consequence, input timing tolerance where precision matters.
- Rule-heavy games: keep core rules in a small logic module with focused tests before relying on visual runs.
- Shooter/runner: spawn determinism, projectile/hazard consequence, no long static dead time.
- Asset-heavy work: `read_image`/`read_animation` plus visual inspection of sprites.
- Audio work: `read_audio(script=..., target={"sound": N}, output_path=<absolute path>)`, non-empty notes, audible peak.

## When to Escalate

Read `strict-mode.md` only when the user asks for release-quality evidence, a proof bundle, a long multi-session build, or an adversarial audit. Otherwise keep the loop light.

Read `pyxel-notes.md` when Pyxel behavior is surprising or when implementing input, drawing, sprites, audio, tilemaps, or deterministic replays.

## Boundaries

- Do not invent universal quality scores or `judge_*` behavior.
- Do not require proof bundles for small games.
- Do not keep a broken visual result because the code state passed.
- Do not use placeholder rectangles for declared sprites unless the design explicitly calls for primitive geometry.
