---
name: wrapped
description: Launch Claude Code Wrapped — an interactive Spotify Wrapped-style slideshow of your Claude Code usage stats in a new terminal window.
disable-model-invocation: true
argument-hint: ""
allowed-tools: Bash
---

Run the following command exactly, then respond with only this message — nothing else:

**Claude Code Wrapped is opening in a new window** — use `SPACE` / `ENTER` to advance slides, `Q` to quit.

```bash
python3 -c "import subprocess; subprocess.Popen(['python3', '${CLAUDE_SKILL_DIR}/wrapped.py'], creationflags=subprocess.CREATE_NEW_CONSOLE)"
```
