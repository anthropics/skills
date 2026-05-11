---
name: divoom-watchface-mcp
description: Operate Divoom LAN watchface devices via the mcp-divoom-lan MCP server—read/patch dial JSON, switch dials, brightness and screen on/off, multipart background upload, raw /divoom_api only when needed; always read before write and never create a dial unless the user asks.
---

# Divoom watchface MCP (LAN)

## Suggested listing title and blurb (for PRs, docs, or changelogs)

- **Title (reference):** `Add skill: Divoom LAN watchface via mcp-divoom-lan (read-before-write, npm published)`
- **Short description (reference):** Example skill that teaches Claude to drive **Divoom pixel devices on the local network** using the **`mcp-divoom-lan`** MCP server (stdio). Covers safe **read → patch → verify** flows, brightness/screen, dial selection, background multipart uploads, and **explicit-only** local dial creation—aligned with the published npm package and open-source server.

## When to use this skill

Use when the user wants to:

- Change the **current** watchface layout or item fields (text, font, color, positions, `ItemList` data).
- **Switch** which watchface/dial is active.
- **Read or set brightness**, or **turn the screen on/off**.
- **Replace** the dial background image (multipart upload to `/replace_clock_dial_bg`).
- **Upload** files via `/upload` when the product command requires it, or **create a new local dial**—**only if they clearly ask** to create one.
- Use **`watchface_protocol_quick_reference`** or fetch MCP **resources** for constraint reminders before complex edits.

**Do not** use this skill for devices that are not Divoom LAN API targets, or when no MCP server exposing these tool names is connected.

## Preconditions

1. **MCP server:** The client must run **`mcp-divoom-lan`** (stdio) so tools like `watchface_get_local` are available. The server nickname in config (e.g. `divoom-lan`) does not matter; use the tools as defined by that server.
2. **Network:** The host running the MCP client can reach the device (usually same LAN).
3. **Target device:** Either set env `DIVOOM_DEVICE_HOST` (optional `DIVOOM_DEVICE_PORT`, `DIVOOM_TIMEOUT_MS`) or pass `target.host` on each call.
4. **Unknown IP:** Ask the user for the device IP before issuing writes.

### Installing / running the server (end users)

| Source | How |
|--------|-----|
| **npm** | [npmjs.com/package/mcp-divoom-lan](https://www.npmjs.com/package/mcp-divoom-lan) — Node **≥ 20**. Example: `npx -y mcp-divoom-lan` with env `DIVOOM_DEVICE_HOST`, optional `DIVOOM_DEVICE_PORT` (default `9000`). |
| **Source** | [github.com/DivoomDevelop/mcp-divoom-lan](https://github.com/DivoomDevelop/mcp-divoom-lan) — `npm install`, `npm run build`, run `dist/index.js` via your client’s MCP config. |

### Optional visual editor (v2)

Humans can edit layouts in a browser UI; the model still uses MCP for device I/O.

- Repo: [github.com/DivoomDevelop/divoom-watchface-visual-editor_v2](https://github.com/DivoomDevelop/divoom-watchface-visual-editor_v2)
- Hosted: [divoomdevelop.github.io/divoom-watchface-visual-editor_v2/](https://divoomdevelop.github.io/divoom-watchface-visual-editor_v2/)

## Tools you can rely on (current server surface)

| Tool | Role |
|------|------|
| `watchface_get_local` | `Device/GetLocalClockInfo` — snapshot of current (or selected) dial; inspect `ItemList`. |
| `watchface_patch_local` | `Device/PatchLocalClockInfo` — apply patches; **server rejects if pre-read `ItemList` is empty**. Prefer `itemPatchList` / `itemPatchByRoleList` over replacing whole `itemList` when possible. |
| `watchface_get_fonts_local` | `Device/GetLocalFontList` |
| `watchface_get_store_market_list` | `Device/GetStoreClockMarketList` (after device has market data) |
| `watchface_set_clock_select` | `Channel/SetClockSelectId` — switch active dial by `clockId`. |
| `watchface_get_brightness` | `Sys/GetBrightness` |
| `watchface_set_brightness` | `Channel/SetBrightness` |
| `watchface_onoff_screen` | `Channel/OnOffScreen` — `onOff` 1 = on, 0 = off. |
| `watchface_replace_dial_bg_file` | Multipart `POST /replace_clock_dial_bg` — local `imagePath` (JPEG/WebP; **800×1280 recommended**). |
| `watchface_upload_file` | Multipart `POST /upload` — requires `filePath` + `metadata` JSON for the command. |
| `watchface_create_local_clock` | Multipart `POST /create_local_clock` — **explicit user intent only**; never as a “fallback” from failed patch. |
| `watchface_reset_local_then_cloud` | `Device/ResetLocalClockFromServer` — **destructive**; confirm with user first. |
| `watchface_raw_command` | Raw `POST /divoom_api` — last resort; must include `command`; **prefer named tools** when available. |
| `watchface_protocol_quick_reference` | Short operational constraints text for the session. |

### MCP resources (optional context)

If the client supports resources, you may read:

- `divoom://guide/quick-reference`
- `divoom://skill/watchface-customization`

## Mandatory operating rules

1. **Use MCP tools only** for device actions—don’t simulate HTTP or fabricate JSON responses.
2. **Read before write (default loop):** `watchface_get_local` → inspect structure and indices → **`watchface_patch_local` (minimal change)** → `watchface_get_local` again to verify.
3. **Empty `ItemList`:** If the latest `GetLocalClockInfo` has **`ItemList` length 0**, **stop patching**. Tell the user to switch to an editable dial (`watchface_set_clock_select`), then re-read. The server also blocks `watchface_patch_local` in this state.
4. **No implicit dial creation:** Call `watchface_create_local_clock` **only** when the user explicitly wants a **new** local dial.
5. **Destructive ops:** `watchface_reset_local_then_cloud` (and similar) need **clear user confirmation** before running.
6. **Background / assets:** For replacing the dial background image, prefer **`watchface_replace_dial_bg_file`**. Use `watchface_upload_file` when the protocol requires a specific upload command + metadata.
7. **Relative brightness:** If the user says “increase/decrease by X%”, combine `watchface_get_brightness` with the device’s scale (often 0–100) and clamp sensibly.
8. **`watchface_raw_command`:** Use sparingly; validate `command` and minimal `payload`; prefer specialized tools to avoid mistakes.

## Task playbooks

### A. “Change color / font / position on what’s showing”

1. `watchface_get_local` (current dial).
2. Locate items in `ItemList` (indices / roles).
3. Build **`itemPatchList`** or **`itemPatchByRoleList`** for the smallest change.
4. `watchface_patch_local` → `watchface_get_local` to confirm.

### B. “Switch watchface / dial”

1. If you need an id, list or discover clocks (device/market tools as appropriate).
2. `watchface_set_clock_select` with `clockId`.
3. `watchface_get_local` to confirm context.

### C. Brightness or screen

1. `watchface_get_brightness` (if adjusting relatively).
2. `watchface_set_brightness` **or** `watchface_onoff_screen` as requested.

### D. Replace background image

1. Ensure image meets spec (JPEG/WebP, **800×1280** recommended).
2. `watchface_replace_dial_bg_file` with `imagePath` (and clock selector fields if not using current display).

### E. New local dial (explicit only)

1. Confirm user wants a **new** dial.
2. `watchface_create_local_clock` with `imagePath` + `metadata` (`ClockName`, `ItemList`, etc., per product docs).

## Response style

- Summarize the intended action, then call tools in order.
- After writes, echo **key results** (`ReturnCode`, `ClockId`, brightness, or what was patched).
- If blocked (network, empty `ItemList`, missing file, user declined reset), **state the blocker and the next user-visible step**.

## References

- MCP repository: [github.com/DivoomDevelop/mcp-divoom-lan](https://github.com/DivoomDevelop/mcp-divoom-lan)
- npm package: [npmjs.com/package/mcp-divoom-lan](https://www.npmjs.com/package/mcp-divoom-lan)
- Registry name (verification): `io.github.DivoomDevelop/mcp-divoom-lan` (see `package.json` → `mcpName`)
