---
name: divoom-watchface-mcp
description: Use the mcp-divoom-lan MCP server to safely operate Divoom watchfaces over LAN—read/patch local dial config, switch dials, brightness, background upload, and explicit local dial creation only when requested.
---

# Divoom Watchface MCP

## When to Use This Skill

Use when the user wants to control a **Divoom pixel/watchface device on the local network** via natural language, for example:

- Change colors, fonts, layout, or other fields on the **current** dial
- Switch the active watchface (dial)
- Adjust brightness
- Replace dial background image
- Create a **new** local dial (only if they clearly ask)

## Preconditions

- An MCP client has the **`mcp-divoom-lan`** server configured and connected (stdio). The server name in config may be `divoom-lan` or another label—use whatever tools that server exposes (e.g. `watchface_get_local`).
- The device is reachable from the client machine (same LAN).
- You know the device host IP (or it is set via env like `DIVOOM_DEVICE_HOST`). If unknown, ask before writing.

## How Users Get the MCP Server

- **npm (published):** [https://www.npmjs.com/package/mcp-divoom-lan](https://www.npmjs.com/package/mcp-divoom-lan)  
  Run with: `npx -y mcp-divoom-lan` (requires Node 20+), plus env: `DIVOOM_DEVICE_HOST`, optional `DIVOOM_DEVICE_PORT` (default `9000`), `DIVOOM_TIMEOUT_MS`.
- **Source:** [https://github.com/DivoomDevelop/mcp-divoom-lan](https://github.com/DivoomDevelop/mcp-divoom-lan)

## Visual Editor (optional, v2)

For a human-in-the-loop UI (templates, preview):

- Repo: [https://github.com/DivoomDevelop/divoom-watchface-visual-editor_v2](https://github.com/DivoomDevelop/divoom-watchface-visual-editor_v2)
- Hosted: [https://divoomdevelop.github.io/divoom-watchface-visual-editor_v2/](https://divoomdevelop.github.io/divoom-watchface-visual-editor_v2/)

The skill does **not** require the editor; use MCP tools for device I/O.

## Mandatory Operating Rules

1. Use only the **Divoom LAN MCP tools** from the connected server for device actions (do not pretend to call HTTP or edit unrelated project files for device ops).
2. **Read before write:**
   - `watchface_get_local` → inspect `ItemList`
   - `watchface_patch_local` with a **minimal** patch
   - `watchface_get_local` again to verify
3. If **`ItemList` is empty**, stop patching and guide the user to select an editable dial first (e.g. `watchface_set_clock_select`), then re-read.
4. **Do not** call `watchface_create_local_clock` unless the user **explicitly** asks to create a new local dial (no implicit “fix” by creating).
5. Destructive flows (`watchface_reset_local_then_cloud`, etc.) require **explicit** user confirmation.

## Operation Hints

- **Brightness:** `watchface_get_brightness` then `watchface_set_brightness`.
- **Background:** prefer `watchface_replace_dial_bg_file` when replacing the cached background; use upload + patch only when updating config URLs is intended.
- **Dial switch:** `watchface_set_clock_select`, then read back to confirm context.

## Response Style

- State the intended action in one short sentence, then execute.
- Return salient fields (`ReturnCode`, `ClockId`, `Brightness`, or what changed).
- If blocked, say what is missing (IP, empty `ItemList`, missing confirmation) and the next step.

## References

- MCP server repo: [https://github.com/DivoomDevelop/mcp-divoom-lan](https://github.com/DivoomDevelop/mcp-divoom-lan)
- npm package: [https://www.npmjs.com/package/mcp-divoom-lan](https://www.npmjs.com/package/mcp-divoom-lan)
