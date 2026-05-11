---
name: divoom-watchface-mcp
description: Use the mcp-divoom-lan MCP server to safely operate Divoom watchface workflows, including local read/patch, dial selection, brightness control, background replacement, and explicit local dial creation.
---

# Divoom Watchface MCP

## When to Use This Skill

Use this skill when users ask to control a Divoom watchface device via natural language, such as:

- editing current watchface style or item values
- switching active dials
- adjusting brightness
- replacing dial background
- creating a new local dial

## Preconditions

- MCP server `divoom-lan` is installed and connected.
- Device is reachable on LAN.
- If target device is unclear, ask for host IP before writing.

## Mandatory Operating Rules

1. Use only `divoom-lan` MCP tools for runtime device actions (do not modify project code for operational requests).
2. Always apply **read-before-write**:
   - `watchface_get_local`
   - inspect `ItemList`
   - `watchface_patch_local` (minimal patch)
   - `watchface_get_local` (verify)
3. If `ItemList` is empty, stop patch flow and ask user to switch to an editable dial first (`watchface_set_clock_select`).
4. Do not call `watchface_create_local_clock` unless user explicitly asks to create a new dial.
5. For destructive operations (`watchface_reset_local_then_cloud`), require explicit confirmation.

## Operation-Specific Guidance

- **Brightness**
  - Read current value via `watchface_get_brightness`.
  - Apply via `watchface_set_brightness`.
- **Background replacement**
  - Use `watchface_replace_dial_bg_file` for background cache replacement.
  - Use `watchface_upload_file` + `watchface_patch_local` only when config URL update is intended.
- **Dial switch**
  - Use `watchface_set_clock_select`, then read back to confirm expected clock context.

## Response Style

- Confirm the intended action in one sentence.
- Execute one clear step at a time.
- Return key result fields (`ReturnCode`, `ClockId`, `Brightness`, or patched fields).
- If blocked, explain exactly what is missing and the next action.

## References

- MCP server repository: `https://github.com/DivoomDevelop/mcp-divoom-lan`
- Visual editor (optional): `https://github.com/DivoomDevelop/divoom-watchface-visual-editor`
