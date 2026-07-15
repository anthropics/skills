---
name: pyxel
description: Use when creating, modifying, debugging, or verifying a game made with Pyxel or a requested retro Python game that should use Pyxel. Do not use for other engines or general Python work.
license: MIT
---

# Pyxel

Build the smallest complete game that satisfies the request, then verify it from observed behavior. Keep the process proportional to the task.

## Runtime

Expect the `pyxel` MCP namespace from pyxel-mcp 1.2+ with Pyxel 2.9.6+ and Python 3.11+. Its eight tools are observation verbs:

- `validate` reports syntax errors and recognizable code patterns.
- `run` drives frames and captures state, screen images, screen grids, or video.
- `pyxel_info` reports versions, examples, and resource URIs.
- `read_palette`, `read_image`, `read_tilemap`, and `read_audio` inspect the corresponding Pyxel data.
- `diff_frames` compares two captured PNGs.

If pyxel-mcp is unavailable, register it with `uvx pyxel-mcp install`; if older than 1.2.0, update it with `uvx --refresh-package pyxel-mcp pyxel-mcp install`. While blocked, use focused logic tests plus direct Pyxel headless runs temporarily, and state that visual and interaction verification is weaker.

## Workflow

1. Infer the smallest playable scope. Ask only when a missing choice would materially change the game.
2. Implement a complete slice: entry state, controls, objective, and a retry or terminal state when the genre needs one.
3. Run `validate`; fix errors and review relevant warnings. Read `pyxel://validation-patterns` only when a category needs explanation.
4. Use `run` from frame 0 with deterministic input. Capture `state` for mechanics and `screen_image` for what the player sees. Prefer `until` with snapshots at `"end"` for event-driven checks.
5. Read the run result's log field (`log`) even when `ok` is true. Inspect the captured image for the task-specific result; nonblank output alone is not evidence of a correct scene.
6. Iterate only on observed defects. Add focused logic tests when rules are easier to prove outside rendering.
7. Report controls, changed files, and exact verification results.

## Minimum Evidence

- `validate` has no syntax errors; relevant warnings are resolved or explained.
- A smoke `run` reaches its intended stop.
- At least one captured frame is inspected directly.
- At least one task-specific state predicate is checked.

Add only relevant evidence: success and failure paths for action games, legal and illegal moves for puzzles, rendered WAV data for authored audio, or asset inspection when sprites and maps are part of the request.

## References

- Read [references/pyxel.md](references/pyxel.md) only when implementing or diagnosing Pyxel input, drawing, assets, tilemaps, audio, or deterministic runs.
- Read [references/strict-mode.md](references/strict-mode.md) only when the user requests release confidence, an audit, a proof bundle, or a long multi-session build.

## Boundaries

- Treat tool output as evidence, not aesthetic judgment.
- Do not require a proof bundle for ordinary edits.
- Do not accept a broken frame because state checks passed.
- Do not create planning or tracking files unless project scale makes them useful.
- Do not substitute placeholder shapes for requested sprite art unless primitive geometry is the intended style.
