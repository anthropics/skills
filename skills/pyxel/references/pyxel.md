# Pyxel Reference

Read only the section relevant to the current problem.

## Runs and input

- `pyxel.btn(KEY)` is continuous; `pyxel.btnp(KEY)` is a press edge. To press a key while another is held, schedule `["KEY_RIGHT", "KEY_SPACE"]` on one frame and `["KEY_RIGHT"]` on the next.
- Each input `buttons` event replaces the held set and persists; schedule `buttons: []` to release everything.
- Pass `random_seed` to `run` whenever randomness affects evidence. It seeds Pyxel's RNG and the stdlib `random`, including module initialization; give private `random.Random` instances an explicit seed.
- Re-run from frame 0 with the cumulative input schedule. Use `until="<expr>"` with `"frame": "end"` snapshots when the event frame is unknown; `until_met` reports whether it held, and `null` means it was never evaluated.
- State `attrs` are attribute paths on the App instance such as `player.x` or `enemies[0].y`, not expressions, calls, or `self.` prefixes. Expose computed evidence as attributes.
- `stall_window_frames` ends a run early when per-frame `state` or `screen_grid` snapshots repeat for that many consecutive frames; use it to catch freezes without waiting for the frame budget.

## Screen images and artifacts

- `screen_image` with `inline: true` returns the PNG in the result; `scale` 2 to 4 keeps pixel art legible. The file is still written and its path reported, so `diff_frames` can compare it later.
- Explicit paths (`output`, `output_pattern`, `render_path`, `output_path`) must be absolute, and screen-image outputs end with lowercase `.png`. Omit the path only for a single inline frame or render whose file is disposable; multi-frame screen images require `output_pattern` containing literal `{frame}` without a format specifier.
- At most 12 inline images arrive per call; extra frames stay on disk and a separate text notice in the tool result says so. Read these notices as well as `log`. Prefer a few chosen frames over `frames: "all"`.
- `video` takes `start_frame` and `end_frame` and writes `.gif`; an `.mp4` output needs ffmpeg and otherwise falls back to `.gif` with a warning.

## Drawing

- Call `pyxel.cls(color)` at the start of `draw()` unless retained pixels are deliberate.
- Use `colkey=0` on `blt()` when palette index 0 is transparent.
- Keep state changes in `update()`; make `draw()` describe the current state.

## Assets and tilemaps

- Build image and tilemap data before `pyxel.run()`, usually in `App.__init__` or a setup helper.
- For code-generated sprites, `pyxel.images[0].set(x, y, ["01100110", ...])` takes one hex digit per pixel.
- Relative asset paths such as `pyxel.load("assets/game.pyxres")` resolve from the script's directory, as under `python game.py`.
- Use `read_image(..., inline=True)` to look at a sprite region. Render animation frames separately and use `diff_frames` when a pixel comparison is useful.
- `read_tilemap` reports `zero_tile_used` and `zero_tile_nonempty` separately. Decide whether tile `(0, 0)` is a problem from the game's blank-tile convention.

## Audio

- Define verifiable sounds with `pyxel.sounds[N].set(...)`; note strings include octave digits such as `C2D2E2`, and `R` is a rest.
- Use `read_audio` with a sound or music target. Check notes, duration, and peak; verify runtime cue and channel state separately. Music targets render a fixed 10-second window.

For example, call `read_audio` with the script and output paths replaced:

```json
{
  "script": "/absolute/path/game.py",
  "target": {"sound": 0},
  "output_path": "/absolute/path/sound.wav"
}
```
