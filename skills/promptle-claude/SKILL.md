---
name: promptle-claude
description: Play Promptle, a daily AI image prompt guessing game, while waiting for Claude Code background tasks. Opens the game in the browser and optionally notifies you on the page when your agent finishes. Use when a user types /promptle or wants a break while waiting for a background task.
license: MIT
---

# Promptle

Open today's [Promptle](https://promptle.app) puzzle in the browser. Promptle is a daily AI image guessing game — you see an AI-generated image and guess the 5-word prompt that created it. Think Wordle, but for AI image prompts.

If a background agent is running, the user gets a toast notification on the game page when it finishes.

## Steps

1. Generate a session ID:

```bash
echo $(uuidgen | tr '[:upper:]' '[:lower:]') > /tmp/promptle-session && cat /tmp/promptle-session
```

2. Open the browser with the session ID from step 1:

Detect the platform and run the appropriate command:
- macOS: `open "https://promptle.app/play?session=SESSION_ID"`
- Linux: `xdg-open "https://promptle.app/play?session=SESSION_ID"`
- Windows: `start "https://promptle.app/play?session=SESSION_ID"`

Replace `SESSION_ID` with the actual UUID from step 1.

3. Tell the user:

> Promptle opened in your browser! If you have a background task running with the notification hook configured, you'll see a toast on the page when it finishes. Enjoy!

## Optional: Completion Notifications

For notifications to work, the user needs this hook in `~/.claude/settings.json`:

```json
{
  "hooks": {
    "PostToolUse": [
      {
        "pattern": "Agent",
        "command": "bash -c 'SID=$(cat /tmp/promptle-session 2>/dev/null) && [ -n \"$SID\" ] && curl -s -X POST https://promptle.app/api/notify/$SID && rm /tmp/promptle-session'"
      }
    ]
  }
}
```

The hook fires when a background agent completes a tool use, POSTing to the notify endpoint which triggers an SSE event on the game page.
