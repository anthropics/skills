---
name: snap
description: Use this skill when the user types "snap:" at the start of their message, wants to share their screen with Claude, wants Claude to see what's on their screen, asks to take a screenshot for AI analysis, or wants to install the snap screen-sharing tool. snap gives Claude eyes — type "snap: what's wrong?" in Claude Code, alt-tab to any window, and Claude reads your screen automatically. Works in Claude Code (terminal or VS Code extension) on Windows.
license: MIT
---

# snap: — Let your AI see what you see, instantly

snap eliminates the friction of screen-sharing with AI. Instead of screenshotting → finding the file → dragging it into chat, you type `snap:` as your message, alt-tab to the window you want to show, and Claude reads it automatically.

**Three dings count down. Chimes play on capture. Claude sees your screen.**

---

## Check if snap is installed

Before using snap, check whether it's already installed:

```bash
node ~/.snap/hook.js --version 2>/dev/null || echo "not installed"
```

Or check directly:
- **Windows:** Does `~/.snap/hook.js` exist? (`Test-Path "$env:USERPROFILE\.snap\hook.js"`)

---

## Install snap (Windows only)

snap requires **Windows** and **Node.js**. It uses PowerShell built-ins — zero npm dependencies.

### Option 1: From this skill (recommended)

The `install.ps1` and `hook.js` files are bundled alongside this SKILL.md. Run the installer:

```powershell
# Right-click install.ps1 → Run with PowerShell
# OR from a terminal:
powershell -ExecutionPolicy Bypass -File "<skill-dir>/install.ps1"
```

The installer will:
1. Check for Node.js (opens nodejs.org if missing)
2. Copy `hook.js` to `~/.snap/hook.js`
3. Register the Claude Code hook in `~/.claude/settings.json`
4. Make `snap` available globally via `npm install -g`

### Option 2: Manual install

```powershell
# 1. Create ~/.snap directory
New-Item -ItemType Directory -Force "$env:USERPROFILE\.snap"

# 2. Copy hook.js to ~/.snap/hook.js
# (hook.js is bundled with this skill)

# 3. Register Claude Code hook
# Add to ~/.claude/settings.json:
# {
#   "hooks": {
#     "UserPromptSubmit": [{
#       "matcher": "",
#       "hooks": [{ "type": "command", "command": "node C:/Users/<you>/.snap/hook.js" }]
#     }]
#   }
# }

# 4. Restart Claude Code
```

---

## How to use snap

### In Claude Code (terminal or VS Code extension)

```
snap: why does this button look off?
snap: is this the right error?
snap:
```

1. Type `snap:` followed by your question (or just `snap:` alone)
2. Hit **Enter** — immediately alt-tab to the window you want to show
3. A balloon notification appears: *"Say cheese! Snapping in 3..."*
4. Three dings count down (2.25 seconds total)
5. Chimes play — screenshot is taken
6. Claude reads your screen and responds to your question

**No API key. No clipboard. No extra steps.**

### Standalone terminal (clipboard mode)

```
snap
```

Takes a screenshot with countdown → copies to clipboard → saves to `~/.snap/latest.png`.
Paste (Ctrl+V) into Claude.ai, ChatGPT, Copilot, or any AI chat.

---

## How it works

snap registers a `UserPromptSubmit` hook in Claude Code (`~/.claude/settings.json`). On every message:

1. The hook reads the prompt
2. If it starts with `snap:` → runs a PowerShell script that shows a balloon notification, counts down with ding sounds, and takes a full-screen screenshot to `~/.snap/latest.png`
3. The hook returns `additionalContext` pointing Claude to the file
4. Claude Code appends the context → Claude reads the image with its Read tool

If the message doesn't start with `snap:` → the hook exits immediately (no-op, zero overhead).

---

## Troubleshooting

**snap: not firing**
→ Restart Claude Code or VS Code. If the hook was updated while a session was open, the session can be in a stale state.

**No sounds or balloon notification**
→ Make sure you're not running Claude Code with `windowsHide:true` anywhere. The installer handles this correctly.

**"snap is not recognized" in terminal**
→ Run `install.ps1` again as Administrator.

**snap: works but Claude doesn't see the image**
→ Check that `~/.snap/latest.png` exists after snapping. If the file is there, try restarting the VS Code extension.

---

## Requirements

- **OS:** Windows (uses PowerShell + Windows Forms for screenshot/sounds/notifications)
- **Node.js:** Any recent LTS version
- **Claude Code:** CLI or VS Code extension

---

## When Claude should use snap

When the user types a message starting with `snap:`, Claude should:
1. Wait for the hook to inject the screenshot path into `additionalContext`
2. **Immediately read the image file** at the path provided before responding
3. Answer the user's question about what's in the screenshot

If snap is not installed and the user wants it, guide them through the installation steps above.
