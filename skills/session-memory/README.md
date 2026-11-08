# Session Memory Skill

A Claude skill for maintaining context across chat sessions using a Load-Work-Save protocol.

## Installation

### Claude Code
```bash
# Copy to your Claude skills directory
cp -r session-memory ~/.claude/skills/
```

### Claude.ai
Upload the `SKILL.md` file or paste its contents into your project's custom instructions.

## Getting Started

After installing, type:
```
/memory-help
```

This displays all available commands.

## Commands

| Command | Description |
|---------|-------------|
| `/memory-help` | Show command list |
| `/junior` | Enable Junior Mode (explains reasoning) |
| `/senior` | Enable Senior Mode (concise, default) |
| `/save` | Manually trigger a context save |
| `/status` | Show current mode and state file locations |

## How It Works

1. **LOAD**: At session start, Claude reads your state files (`CONTEXT.md`, `TASKS.md`).
2. **WORK**: Claude works on your task, noting key decisions.
3. **SAVE**: Claude auto-saves after significant work, or when you type `/save`.

## Modes

- **Junior Mode** (`/junior`): Claude explains reasoning at each step. Great for learning.
- **Senior Mode** (`/senior`): Concise, action-focused. Default behavior.

## Example State File

Create a `CONTEXT.md` in your project:

```markdown
# Project State

## Summary
Building a REST API. Auth module complete.

## Next Steps
- [ ] Implement GET /users/:id
- [ ] Add unit tests
```

## License

Apache 2.0
