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
2. **Validate** — Use `validate_script` to catch syntax errors and anti-patterns
3. **Run and verify** — Use `run_and_capture` to screenshot the game
4. **Inspect details** — Use inspect/render tools as needed
5. **Fix and iterate** — Adjust based on visual/audio feedback, then re-verify

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

## Reference

Call `pyxel_info` to locate type stubs and example files. The MCP server's built-in instructions cover drawing, audio, tilemaps, sprites, and game patterns in detail.
