---
name: agent-notify
description: Cross-platform notification sound and taskbar flash for AI coding agents (Claude Code, OpenClaw, Codex, Kiro, Cursor, etc.). Plays alert sounds and visual notifications when the agent needs confirmation or completes tasks. Auto-detects the agent environment and configures hooks accordingly. Use this skill whenever the user mentions notification sounds, alert beeps, taskbar flash, completion alerts, or wants to know when the agent finishes or needs attention — even if they just say something vague like "I want a sound" or "how do I get notified". Also trigger on any mention of configuring, enabling, disabling, or customizing audio/visual alerts for any AI coding agent. Works on Windows, macOS, and Linux.
license: Complete terms in LICENSE.txt
---

# Agent Notify Skill

You are an assistant that helps users configure cross-platform notification sounds and taskbar/dock alerts for AI coding agents. When triggered, you MUST follow the instructions below precisely.

## Language Detection

Detect the user's language from their message. If they write in Chinese, respond in Chinese. If they write in English, respond in English. Match the user's language throughout the entire interaction.

## Step 1: Offer Two Modes

Present two options to the user:

**English:**
```
🔔 Agent Notify — Setup

Choose a setup mode:

1️⃣  Quick Setup (recommended) — One-click install with default settings
    • Notification on: confirmation requests + task completion
    • Default system sounds
    • Taskbar flash: 5 times

2️⃣  Custom Setup — Choose your own settings
    • Pick which events trigger notifications
    • Configure custom sound files
    • Adjust taskbar flash count

Enter 1 or 2:
```

**Chinese:**
```
🔔 Agent Notify — 配置向导

请选择配置模式：

1️⃣  一键配置（推荐）— 使用默认设置快速安装
    • 通知触发：确认请求 + 任务完成
    • 默认系统提示音
    • 任务栏闪烁：5 次

2️⃣  自定义配置 — 自由选择设置
    • 选择哪些事件触发通知
    • 配置自定义提示音文件
    • 调整任务栏闪烁次数

请输入 1 或 2：
```

## Step 2A: Quick Setup

If user chooses 1, proceed directly to **Step 3: Install**.

Use these defaults:
- Hooks: `Notification` (type: confirm), `Stop` (type: done)
- Sounds: system defaults
- Taskbar flash count: 5

## Step 2B: Custom Setup

If user chooses 2, walk through these options interactively:

### 2B-1: Select Hook Events

Present available hook events:

```
Available notification triggers:

[1] ✅ Confirmation requests (Notification hook) — when Claude asks for permission
[2] ✅ Task completion (Stop hook) — when Claude finishes responding
[3] ❌ Error alerts — when a tool call fails
[4] ❌ Pre-tool notification (PreToolUse) — before each tool execution
[5] ❌ Post-tool notification (PostToolUse) — after each tool execution

Enter numbers to toggle (e.g., 1,2,3), or press Enter to keep defaults:
```

### 2B-2: Custom Sounds

Ask if user wants custom sound files:

```
Custom sound files (leave blank for system defaults):

• Confirmation sound path: [blank = system default]
• Completion sound path: [blank = system default]
• Error sound path: [blank = system default]

Supported formats:
  Windows: .wav
  macOS: .aiff, .mp3, .wav
  Linux: .oga, .wav, .mp3
```

### 2B-3: Taskbar Flash Count

```
Taskbar flash count [default: 5]:
```

## Step 3: Install

After collecting settings (default or custom), perform the installation:

### 3.1 Detect OS and Agent Environment

Run this command to detect the operating system:
```bash
uname -s 2>/dev/null || echo "Windows"
```

- If output contains `Darwin` → macOS
- If output contains `Linux` → Linux
- If output contains `MINGW`, `MSYS`, `CYGWIN`, or `Windows` → Windows

Then detect which AI coding agent the user is running. This determines the config directory and hooks format:

```bash
# Detect agent config directory (first existing one wins)
for dir in ~/.claude ~/.codex ~/.openclaw ~/.kiro ~/.cursor; do
  if [ -d "$dir" ]; then echo "$dir"; break; fi
done
```

On Windows, also check:
```bash
for dir in "$USERPROFILE/.claude" "$USERPROFILE/.codex" "$USERPROFILE/.openclaw"; do
  if [ -d "$dir" ]; then echo "$dir"; break; fi
done
```

Set `AGENT_HOME` to the detected directory (e.g., `~/.claude`). If none found, default to `~/.claude` and create it.

The supported agents and their known config paths:
| Agent | Config Dir | Settings File | Hooks Support |
|-------|-----------|---------------|---------------|
| Claude Code | `~/.claude` | `settings.json` | ✅ Full (Notification, Stop, PreToolUse, PostToolUse) |
| OpenClaw | `~/.openclaw` | `settings.json` | ✅ Same hooks format as Claude Code |
| Codex (OpenAI) | `~/.codex` | `settings.json` | ⚠️ May differ — check docs |
| Kiro (AWS) | `~/.kiro` | `settings.json` | ⚠️ May differ — check docs |
| Cursor | `~/.cursor` | varies | ⚠️ Different hooks system |

If the detected agent is not Claude Code or OpenClaw, warn the user that hooks compatibility is not guaranteed and ask if they want to proceed. The notification scripts themselves (sound + taskbar flash) work universally — only the hooks integration is agent-specific.

### 3.2 Copy Notification Script

Find the skill directory by searching for this skill.md file:
```bash
for base in ~/.claude/skills ~/.codex/skills ~/.openclaw/skills ~/.kiro/skills ~/.cursor/skills; do
  found=$(find "$base" -name "skill.md" -path "*/agent-notify/*" 2>/dev/null | head -1)
  [ -n "$found" ] && echo "$(dirname "$found")" && break
done
```

On Windows (Git Bash / MSYS2), also try:
```bash
for base in "$USERPROFILE/.claude/skills" "$USERPROFILE/.codex/skills" "$USERPROFILE/.openclaw/skills"; do
  found=$(find "$base" -name "skill.md" -path "*/agent-notify/*" 2>/dev/null | head -1)
  [ -n "$found" ] && echo "$(dirname "$found")" && break
done
```

If the find command fails or returns nothing, ask the user where they installed the skill.

Copy the script to `$AGENT_HOME/` (not hardcoded `~/.claude/`):

**For Windows:**
```bash
cp "<skill_dir>/scripts/notify-windows.ps1" "$AGENT_HOME/notify.ps1"
```

**For macOS:**
```bash
cp "<skill_dir>/scripts/notify-macos.sh" "$AGENT_HOME/notify.sh"
chmod +x "$AGENT_HOME/notify.sh"
```

**For Linux:**
```bash
cp "<skill_dir>/scripts/notify-linux.sh" "$AGENT_HOME/notify.sh"
chmod +x "$AGENT_HOME/notify.sh"
```

### 3.3 Write Config

Write the user's configuration to `$AGENT_HOME/notify-config.json`:

Construct the config JSON from the user's chosen settings and write it. For example, with defaults:

```bash
cat > "$AGENT_HOME/notify-config.json" << 'EOF'
{
  "hooks": {
    "Notification": { "enabled": true, "type": "confirm" },
    "Stop": { "enabled": true, "type": "done" }
  },
  "sounds": {
    "confirm": "",
    "done": "",
    "error": ""
  },
  "taskbar": {
    "flashCount": 5,
    "enabled": true
  }
}
EOF
```

Substitute actual values from user's choices (sound paths, flash count, enabled hooks).

### 3.4 Update Agent Settings

Read the existing `$AGENT_HOME/settings.json` file, then merge the hooks configuration into it.

**IMPORTANT:** Do NOT overwrite existing settings. Merge the `hooks` key into the existing JSON, preserving all other fields (env, permissions, model, statusLine, etc.).

Build hook commands based on OS. Replace `$AGENT_HOME` with the actual detected path in the commands below:

**Windows hooks:**
```json
{
  "hooks": {
    "Notification": [
      {
        "matcher": "",
        "hooks": [
          {
            "type": "command",
            "command": "powershell.exe -ExecutionPolicy Bypass -File \"$AGENT_HOME/notify.ps1\" -Type confirm -ConfigPath \"$AGENT_HOME/notify-config.json\""
          }
        ]
      }
    ],
    "Stop": [
      {
        "matcher": "",
        "hooks": [
          {
            "type": "command",
            "command": "powershell.exe -ExecutionPolicy Bypass -File \"$AGENT_HOME/notify.ps1\" -Type done -ConfigPath \"$AGENT_HOME/notify-config.json\""
          }
        ]
      }
    ]
  }
}
```

**macOS/Linux hooks:**
```json
{
  "hooks": {
    "Notification": [
      {
        "matcher": "",
        "hooks": [
          {
            "type": "command",
            "command": "bash $AGENT_HOME/notify.sh confirm $AGENT_HOME/notify-config.json"
          }
        ]
      }
    ],
    "Stop": [
      {
        "matcher": "",
        "hooks": [
          {
            "type": "command",
            "command": "bash $AGENT_HOME/notify.sh done $AGENT_HOME/notify-config.json"
          }
        ]
      }
    ]
  }
}
```

If user selected additional hooks in custom mode (error, PreToolUse, PostToolUse), add those hook entries as well with the appropriate type parameter.

For agents that don't support the Claude Code hooks format, inform the user and offer to just install the notification scripts manually. They can then integrate with their agent's own hook/event system.

### 3.5 Test

Run a test notification:

**Windows:**
```bash
powershell.exe -ExecutionPolicy Bypass -File "$AGENT_HOME/notify.ps1" -Type confirm -ConfigPath "$AGENT_HOME/notify-config.json"
```

**macOS/Linux:**
```bash
bash "$AGENT_HOME/notify.sh" confirm "$AGENT_HOME/notify-config.json"
```

### 3.6 Report Success

**English:**
```
✅ Agent Notify installed successfully!

Agent: [detected agent name]
Config: $AGENT_HOME/

Configured notifications:
  • 🔔 Confirmation requests → [sound type]
  • ✅ Task completion → [sound type]

Files installed:
  • $AGENT_HOME/notify.[ps1|sh]
  • $AGENT_HOME/notify-config.json
  • $AGENT_HOME/settings.json (hooks added)

⚠️  Please restart your agent for hooks to take effect.

To uninstall, say: "disable notification" or "关闭提示音"
To reconfigure, say: "configure notify" or "配置提示音"
```

**Chinese:**
```
✅ Agent Notify 安装成功！

运行环境：[检测到的 agent 名称]
配置目录：$AGENT_HOME/

已配置的通知：
  • 🔔 确认请求 → [提示音类型]
  • ✅ 任务完成 → [提示音类型]

已安装文件：
  • $AGENT_HOME/notify.[ps1|sh]
  • $AGENT_HOME/notify-config.json
  • $AGENT_HOME/settings.json（已添加 hooks）

⚠️  请重启你的 agent 使 hooks 生效。

卸载请说："关闭提示音" 或 "disable notification"
重新配置请说："配置提示音" 或 "configure notify"
```

## Important Notes

- `$AGENT_HOME` refers to the detected agent config directory (e.g., `~/.claude`, `~/.codex`, `~/.openclaw`). Always use the actual resolved path in commands, not the variable name.
- On Windows, `$HOME` in hook commands is expanded by the shell (Git Bash/MSYS2). If the user's environment doesn't expand `$HOME`, use the full absolute path instead (e.g., `C:/Users/username/.claude/notify.ps1`).
- On macOS, the Dock bounce uses Python's `AppKit.NSApplication.requestUserAttention_()` which is available by default. If PyObjC is not available, the fallback `printf '\a'` (terminal bell) will trigger a Dock bounce in most terminal apps.
- On Linux, `notify-send` handles both the desktop notification and the visual alert. If it's not installed, only the sound will play.
- For agents other than Claude Code / OpenClaw, the hooks format may differ. If auto-configuration fails, the notification scripts can still be used standalone — just call them directly from whatever hook/event system the agent provides.

## Uninstall / Disable

When user triggers with disable-related keywords (`关闭提示音`, `disable notification`, etc.):

1. Detect `$AGENT_HOME` using the same logic as Step 3.1
2. Read `$AGENT_HOME/settings.json`
3. Remove ALL hook entries that reference `notify.ps1` or `notify.sh`
4. Write back the cleaned settings.json
5. Remove `$AGENT_HOME/notify.ps1` or `$AGENT_HOME/notify.sh`
6. Remove `$AGENT_HOME/notify-config.json`
7. Confirm:

**English:**
```
✅ Agent Notify has been uninstalled.

Removed:
  • $AGENT_HOME/notify.[ps1|sh]
  • $AGENT_HOME/notify-config.json
  • Notification hooks from $AGENT_HOME/settings.json

⚠️  Please restart your agent for changes to take effect.
```

**Chinese:**
```
✅ Agent Notify 已卸载。

已移除：
  • $AGENT_HOME/notify.[ps1|sh]
  • $AGENT_HOME/notify-config.json
  • $AGENT_HOME/settings.json 中的通知 hooks

⚠️  请重启你的 agent 使更改生效。
```
