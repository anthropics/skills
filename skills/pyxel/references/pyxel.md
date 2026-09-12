# Pyxel Reference

Read only the section relevant to the current problem.

## Runs and Input

- `pyxel.btn(KEY)` is continuous; `pyxel.btnp(KEY)` is a press edge.
- Each input `buttons` event replaces the held set and persists; schedule `buttons: []` to release it.
- Pass `random_seed` to `run` when randomness affects evidence. It covers Pyxel's RNG and the stdlib `random`, including initialization; give private `random.Random` instances an explicit seed.
- Re-run from frame 0 with the cumulative input schedule. Use `until="<expr>"` with snapshots at `"end"` when the event frame is unknown.
- Artifact arguments such as `output`, `output_pattern`, `render_path`, and `output_path` require absolute paths; screen-image outputs must end with lowercase `.png`.
- State `attrs` are attribute paths, not expressions, calls, or `self.` prefixes; expose computed evidence as App attributes.

## Drawing

- Call `pyxel.cls(color)` at the start of `draw()` unless retained pixels are deliberate.
- Use `colkey=0` on `blt()` when palette index 0 is transparent.
- Keep state changes in `update()`; make `draw()` describe the current state.
- Inspect captured pixels when HUD placement, legibility, feedback, or scene transitions matter.

## Assets and Tilemaps

- Build image and tilemap data before `pyxel.run()`, usually in `App.__init__` or a setup helper.
- Use `read_image(..., render_path=<absolute path>)` to inspect a sprite region. For animation frames, render the regions explicitly and use `diff_frames` when a pixel comparison is useful.
- `read_tilemap` reports `zero_tile_used` and `zero_tile_nonempty` separately. Decide whether tile `(0, 0)` is a problem from the game's blank-tile convention.

## Audio

- Define verifiable sounds with `pyxel.sounds[N].set(...)`; note strings include octave digits such as `C2D2E2`, and `R` is a rest.
- Use `read_audio(script=..., target={"sound": N}, output_path=<absolute path>)` or a music target. Check notes where available, duration, and peak; verify runtime cue/channel state separately. Claim sound quality only after listening—otherwise report it as not auditioned.

## Visual Truth

State can prove that a transition occurred while the captured frame reveals an unreadable or incorrect scene. Mechanics and pixels are separate evidence; check both when both matter.
