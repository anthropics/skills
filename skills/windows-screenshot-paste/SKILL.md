---
name: windows-screenshot-paste
description: Use when a Windows user wants to paste screenshots directly into Claude Code terminal with Ctrl+V. Installs an AutoHotkey v2 script that intercepts clipboard images, saves them as PNG files, and types the file path into the terminal so Claude can read them.
---

# Windows Screenshot Paste for Claude Code

> **Author:** [sharooncs](https://github.com/sharooncs)

Enables `Ctrl+V` screenshot pasting in Claude Code on Windows. When you copy a screenshot to your clipboard and press `Ctrl+V` in the terminal, the image is saved automatically and the file path is typed in — so Claude can read it directly.

## Requirements

- Windows 10 or 11
- [AutoHotkey v2](https://www.autohotkey.com/) (installed automatically by the script)
- Windows Terminal, PowerShell, or CMD

## Installation

Run this one-time setup in your terminal:

```powershell
powershell -ExecutionPolicy Bypass -File "${CLAUDE_SKILL_DIR}\scripts\install.ps1"
```

This will:
1. Install AutoHotkey v2 via `winget` if not already present
2. Copy `ClaudeScreenshot.ahk` to your home folder
3. Register it in Windows Startup so it runs on every login
4. Launch it immediately for the current session

> See [`scripts/install.ps1`](scripts/install.ps1) for the full installation script.
> See [`scripts/ClaudeScreenshot.ahk`](scripts/ClaudeScreenshot.ahk) for the AutoHotkey script.

## Usage

1. Press `Win+Shift+S` and snip any region of your screen
2. Click back into your terminal
3. Press `Ctrl+V`

The file path is typed automatically, e.g.:
```
C:\Users\you\Pictures\Claude_Screenshots\Screenshot_20260314_163045.png
```

Claude reads the image from that path. Screenshots are saved to `%USERPROFILE%\Pictures\Claude_Screenshots\`.

## How It Works

- Only activates inside Windows Terminal, PowerShell, and CMD — no effect on other apps
- Uses Win32 `IsClipboardFormatAvailable` to detect bitmap data on the clipboard (CF_BITMAP=2, CF_DIB=8)
- Saves the image via PowerShell's `System.Windows.Forms.Clipboard.GetImage()` using a temp `.ps1` file to avoid shell quoting issues
- Types the saved file path into the terminal with `SendInput`

## Troubleshooting

| Problem | Fix |
|---------|-----|
| Nothing happens on Ctrl+V | Check system tray for green AutoHotkey icon — if missing, re-run `install.ps1` |
| "Failed to save image" popup | Make sure you copied an image (not text) before pressing Ctrl+V |
| Script not running after reboot | Check `shell:startup` folder contains `ClaudeScreenshot.ahk` |
