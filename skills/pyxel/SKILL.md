---
name: pyxel
description: "Create retro games with Pyxel using the pyxel-mcp MCP server. TRIGGER when: user wants to make retro/pixel-art/8-bit games, mentions Pyxel game engine, or asks to create simple 2D games with chiptune audio. DO NOT TRIGGER when: user is building non-game applications, using other game engines (Pygame, Godot, Unity), or doing general Python programming."
license: MIT
---

# Pyxel Game Development

## What is Pyxel?

[Pyxel](https://github.com/kitao/pyxel) is a retro game engine for Python with deliberate limitations that spark creativity:

- **16 colors** (fixed palette)
- **256x256 px** image banks (3 banks)
- **4 audio channels** with chiptune sounds
- **Built-in editors** for sprites, tilemaps, sounds, and music
- Screen sizes typically 128x128, 160x120, or 256x256

## Setup

The pyxel-mcp MCP server must be installed for this skill to work. Add to your MCP configuration:

```json
{
  "mcpServers": {
    "pyxel": {
      "command": "uvx",
      "args": ["pyxel-mcp"]
    }
  }
}
```

Or install directly: `pip install pyxel-mcp`

## Workflow

Follow this cycle for every Pyxel project:

1. **Write code** — Create or modify the `.py` file
2. **Run and verify** — Use `run_and_capture` to screenshot the game
3. **Inspect details** — Use `inspect_sprite`, `inspect_layout`, `render_audio` as needed
4. **Fix and iterate** — Adjust based on visual/audio feedback, then re-verify

**Always verify visually.** Never assume code is correct without running `run_and_capture`. Pyxel's coordinate system, color indices, and sprite layouts often produce unexpected results that are only caught by looking at the actual output.

## Available MCP Tools

| Tool | Purpose |
|------|---------|
| `run_and_capture` | Run a script and screenshot after N frames |
| `capture_frames` | Screenshots at multiple frame points (animation) |
| `play_and_capture` | Simulate key/mouse input and capture screenshots |
| `inspect_sprite` | Read pixel data from image banks |
| `inspect_layout` | Analyze text positioning and screen balance |
| `inspect_state` | Read game object attributes for debugging |
| `inspect_palette` | Analyze color usage and contrast |
| `inspect_tilemap` | Verify tilemap content and layout |
| `inspect_bank` | Visualize full image bank contents |
| `inspect_screen` | Capture screen as compact color grid |
| `compare_frames` | Diff pixels between two frames |
| `validate_script` | Check syntax and anti-patterns before running |
| `render_audio` | Render a sound slot to WAV and analyze notes |
| `pyxel_info` | Get Pyxel install paths, API stubs, examples |

## Quick Start Pattern

```python
import pyxel

class App:
    def __init__(self):
        pyxel.init(160, 120, title="My Game")
        # Set up sprites, sounds, state here
        pyxel.run(self.update, self.draw)

    def update(self):
        if pyxel.btnp(pyxel.KEY_Q):
            pyxel.quit()
        # Game logic here

    def draw(self):
        pyxel.cls(0)
        # Draw everything here

App()
```

## Key Pyxel Conventions

- **Colors**: 0=black, 1=navy, 2=purple, 3=green, 4=brown, 5=dark_blue, 6=light_blue, 7=white, 8=red, 9=orange, 10=yellow, 11=lime, 12=cyan, 13=gray, 14=pink, 15=peach
- **Coordinates**: Origin (0,0) at top-left; X right, Y down
- **Text**: Built-in font is 4px wide, 6px tall per character
- **Transparency**: Use `colkey=0` in `blt()` to treat black as transparent
- **Input**: `btn()` for held keys, `btnp()` for press-once, `btnr()` for release
- **Trig**: `pyxel.sin()`/`cos()` use **degrees**, not radians
- **Audio**: 4 channels (ch0-3); reserve ch3 for sound effects, ch0-2 for BGM

## What Makes a Good Pyxel Game

Based on analysis of 140+ community games:

1. **Background matters most** — Never use plain solid color. Add star fields, gradients, or parallax layers
2. **Use 10+ colors** with clear hierarchy: dark background → mid-tone environment → bright interactive elements
3. **Title screen** — Include pixel art title, animated elements, controls hint, blinking "PRESS ENTER"
4. **Sound effects for every action** — Move, jump, collect, hit, game over all need distinct SE
5. **Visual feedback** — Flash (`pal()`), particles, or screen shake on player actions

## Testing Input-Dependent Logic

Use `play_and_capture` to simulate key/mouse input directly:

```python
# Simulate SPACE press at frame 30, capture at frames 29 and 31
play_and_capture("game.py",
    inputs='[{"frame":30,"keys":["KEY_SPACE"]}]',
    frames="29,31")
```

For simpler cases, replace input conditions with frame-based triggers:

```python
# Original:  if pyxel.btnp(pyxel.KEY_SPACE): jump()
# For test:  if pyxel.frame_count == 30: jump()
```

Capture the frame, verify the result, then revert to real input.

## Letting the User Play

When suggesting the user run a script directly, check for a virtual environment:

```bash
.venv/bin/python my_game.py
# or
python my_game.py
```

## Reference

For detailed API reference, call `pyxel_info` to locate the type stubs and example files. The MCP server's built-in instructions contain comprehensive documentation on drawing, audio, tilemaps, sprites, and game patterns.
