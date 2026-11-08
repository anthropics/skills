---
name: wrapped
description: Launch Claude Code Wrapped — an interactive Spotify Wrapped-style slideshow of your Claude Code usage stats in a new terminal window.
license: MIT
disable-model-invocation: true
argument-hint: ""
allowed-tools: Bash
---

Run the following command exactly, then respond with only this message — nothing else:

**Claude Code Wrapped is opening in a new window** — use `SPACE` / `ENTER` to advance slides, `Q` to quit.

```bash
python3 -c "import os, subprocess; kwargs = {}; \
if os.name == 'nt': kwargs['creationflags'] = subprocess.CREATE_NEW_CONSOLE; \
subprocess.Popen(['python3', '${CLAUDE_SKILL_DIR}/wrapped.py'], **kwargs)"
```
