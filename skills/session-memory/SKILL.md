---
name: session-memory
description: Teaches Claude to persist context across sessions using a Load-Work-Save protocol with auto-save and configurable modes.
---

# Session Memory Skill

Maintain continuity across chat sessions by treating context like a "save game."

## Available Commands

| Command | Description |
|---------|-------------|
| `/memory-help` | Show this command list |
| `/junior` | Enable Junior Mode (explains reasoning) |
| `/senior` | Enable Senior Mode (concise, default) |
| `/save` | Manually trigger a context save |
| `/status` | Show current mode and state file locations |

## Modes

### Junior Mode
When the user types `/junior`:
- Explain the "why" behind each action.
- Include reasoning and decision context.
- Teach as you work.

### Senior Mode (Default)
When the user types `/senior` or by default:
- Be concise. Focus on outcomes.
- Skip explanations unless asked.

## The Protocol

### 1. LOAD (Session Start)
Automatically check for and read common state files (`CONTEXT.md`, `TODO.md`, `TASKS.md`) in the project root or workspace. If none exist, ask if the user wants to create one.

### 2. WORK
Proceed with tasks. Note significant decisions for the save phase.

### 3. SAVE (Auto + Manual)
- **Auto-Save**: After completing significant work (feature, bugfix, decision), proactively update the state file. Keep updates concise.
- **Manual Save**: When the user types `/save`, immediately update all state files.

### End of Session
Before ending, ensure state files include:
- Summary of what was accomplished.
- Current state of work.
- Clear "Next Steps."

## Core Principle

**Separate persistent state from ephemeral work.**

- **Persistent**: Architecture, schemas, decisions. Update on major changes only.
- **Ephemeral**: Session notes, task lists. Update frequently, clean up when done.
