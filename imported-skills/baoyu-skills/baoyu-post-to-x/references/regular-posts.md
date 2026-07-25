# Regular Posts - Detailed Guide

Detailed documentation for posting text and images to X.

## Manual Workflow

If you prefer step-by-step control:

### Step 0: Prefer Chrome Computer Use in Codex

When running inside Codex, first detect whether Chrome Computer Use is enabled:

1. If Computer Use tools are already visible, call `get_app_state` for `Google Chrome`.
2. If not, use `tool_search` for `computer-use get_app_state click press_key drag scroll Google Chrome`, then call `get_app_state`.
3. If `get_app_state` succeeds, use the user's real Chrome with Computer Use for all X UI actions.
4. Use CDP scripts only when Computer Use is unavailable or explicitly requested.

If the user explicitly asks for Chrome Computer Use, do not use Playwright, the in-app Browser, or CDP without approval.

### Step 1: Copy Image to Clipboard

```bash
${BUN_X} {baseDir}/scripts/copy-to-clipboard.ts image /path/to/image.png
```

### Step 2: Paste from Clipboard

```bash
# Simple paste to frontmost app
${BUN_X} {baseDir}/scripts/paste-from-clipboard.ts

# Paste to Chrome with retries
${BUN_X} {baseDir}/scripts/paste-from-clipboard.ts --app "Google Chrome" --retries 5

# Quick paste with shorter delay
${BUN_X} {baseDir}/scripts/paste-from-clipboard.ts --delay 200
```

### Step 3: Use Chrome Computer Use (Preferred)

1. Use `get_app_state` for `Google Chrome`.
2. Navigate Chrome to `https://x.com/compose/post` if needed.
3. Click the composer and type the post text.
4. Copy each image to the clipboard with `copy-to-clipboard.ts image <path>`.
5. Press `super+v` on macOS or `control+v` on Windows/Linux with Computer Use.
6. Wait until X finishes media upload.
7. Ask for explicit confirmation before clicking `Post`.

## Image Support

- Formats: PNG, JPEG, GIF, WebP
- Max 4 images per post
- Images copied to system clipboard, then pasted via keyboard shortcut

## Example Session

```
User: /post-to-x "Hello from Claude!" --image ./screenshot.png

Claude:
1. Detects Chrome Computer Use
2. Opens X compose in the user's real Chrome
3. Types text into editor
4. Copies image to clipboard and pastes with Computer Use
5. Waits for upload and verifies the preview
6. Asks before clicking Post
```

## Troubleshooting

- **Chrome not found**: Set `X_BROWSER_CHROME_PATH` environment variable
- **Not logged in**: First run opens Chrome - log in manually, cookies are saved
- **Image paste fails**:
  - Verify clipboard script: `${BUN_X} {baseDir}/scripts/copy-to-clipboard.ts image <path>`
  - On macOS, grant "Accessibility" permission to Terminal/iTerm in System Settings > Privacy & Security > Accessibility
  - Keep Chrome window visible and in front during paste operations
- **osascript permission denied**: Grant Terminal accessibility permissions in System Preferences
- **Rate limited**: Wait a few minutes before retrying

## How It Works

In Chrome Computer Use mode:
1. Codex controls the user's visible Google Chrome window
2. Text is typed through the real UI
3. Images are copied to the system clipboard and pasted with real keystrokes
4. The user confirms before the final public post

The `x-browser.ts` script is the CDP fallback. It uses Chrome DevTools Protocol (CDP) to:
1. Launch real Chrome (not Playwright) with `--disable-blink-features=AutomationControlled`
2. Use persistent profile directory for saved login sessions
3. Interact with X via CDP commands (Runtime.evaluate, Input.dispatchKeyEvent)
4. **Paste images using osascript** (macOS): Sends real Cmd+V keystroke to Chrome, bypassing CDP's synthetic events that X can detect

This approach bypasses X's anti-automation detection that blocks Playwright/Puppeteer.

### Image Paste Mechanism (macOS)

CDP's `Input.dispatchKeyEvent` sends "synthetic" keyboard events that websites can detect. X ignores synthetic paste events for security. The solution:

1. Copy image to system clipboard via Swift/AppKit (`copy-to-clipboard.ts`)
2. Bring Chrome to front via `osascript`
3. Send real Cmd+V keystroke via `osascript` and System Events
4. Wait for upload to complete

This requires Terminal to have "Accessibility" permission in System Settings.
