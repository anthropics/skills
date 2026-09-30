---
name: pyxel
description: Build, debug, and verify games made with Pyxel, the retro game engine for Python. Use whenever a task creates, changes, tests, or reviews a Pyxel game, or asks for a retro Python game that should use Pyxel. Do not use for other engines or general Python work.
license: MIT
compatibility: Requires the pyxel-mcp MCP server 1.3.1 or newer (Python 3.11+, installs Pyxel 2.9.6+). Use `uvx --from 'pyxel-mcp>=1.3.1' pyxel-mcp` as the server command.
metadata:
  version: "1.4.2"
  pyxel-mcp: ">=1.3.1"
---

# Pyxel

Build or change only what the request needs, preserving the existing game's conventions. Verify the result from observed behavior, with effort proportional to the task.

## Runtime

pyxel-mcp provides eight observation tools. They report facts; judging them is your job.

- `validate` reports syntax errors and recognizable Pyxel code patterns without running the script.
- `run` drives headless frames with scheduled input, stops on `until`, and captures `state`, `screen_image`, `screen_grid`, or `video`. `screen_image` with `inline: true` returns an image.
- `pyxel_info` reports versions, bundled examples, and resource URIs.
- `read_palette`, `read_image`, `read_tilemap`, and `read_audio` inspect the palette, image banks, tilemaps, and rendered audio; `read_image` and `read_tilemap` take `inline=true` to return their renders as images.
- `diff_frames` compares two captured PNGs.

If tools are missing or `pyxel_info` reports a version below 1.3.1, update the plugin or set the client's MCP command to `uvx --from 'pyxel-mcp>=1.3.1' pyxel-mcp`. Append `install` for setup examples; it only prints instructions. Apply the appropriate registration with this versioned command. Avoid duplicate plugin registrations. Restart the client and recheck `pyxel_info`. While blocked, use focused logic tests plus direct headless Pyxel runs, and report weaker visual and interaction verification.

## Workflow

1. Identify the requested behavior and the existing code and assets it affects. For a new game, choose a playable scope with controls, an objective, and any retry or terminal states its rules need. Ask only when a missing choice materially changes the result.
2. Implement the change. Follow the project's asset conventions; use code-generated or file-based assets as the task requires.
3. Run `validate` on changed game code. Fix errors and resolve or explain relevant warnings. Exercise the affected behavior with `run`, using scheduled input and a `random_seed` when randomness matters. Check that it reaches the intended stop without crash, timeout, or unexpected stall; read `log` even when `ok` is true.
4. Check task-specific state predicates for mechanics and directly inspect captured frames for appearance. A new game needs both; a focused edit needs evidence for the behavior it can affect. Use `screen_image` with `inline: true` to see the frame. Check authored audio through `read_audio`, and listen before judging sound quality. Fix observed defects and repeat affected checks; use focused logic tests when they prove rules more directly.
5. Report changed files, controls when relevant, verification results, and anything unverified. Distinguish observed behavior from visual or listening judgments.

## References

- [references/pyxel.md](references/pyxel.md): input, drawing, assets, audio, and determinism. Read for related implementation or diagnosis.
- [references/design.md](references/design.md): presentation and feedback when creating or polishing games.
- [references/strict-mode.md](references/strict-mode.md): broader coverage and retained evidence for requested release checks, audits, or proof bundles.

## Boundaries

- Do not accept a broken frame because state checks passed.
- Do not require proof bundles, planning files, or tracking files for ordinary edits. Retain them only when requested or needed for continuity on larger work.
- Do not substitute placeholder shapes for requested sprite art unless primitive geometry is the intended style.
