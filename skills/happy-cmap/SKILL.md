----
name: simply-happy
version: 0.1.0
description: Launch a full-screen transparent fireworks effect on macOS. Triggered when the user expresses celebration, confetti, fireworks, milestones (PR merged / deployment / CI all green), festive occasions, or simply wants to "feel happy".
---

# simply-happy

Make the screen "happy" — overlay a transparent, click-through fireworks animation on the macOS desktop that automatically fades out after a few seconds.

## When to Use

Use this skill to give the user a visual celebration when the conversation contains any of the following intents:

- **Direct request**: "show me fireworks", "celebrate", "confetti", "let's party", "放个烟花", "撒花"
- **Milestone achievement**: PR merged successfully, CI all green, deployment complete, demo finished, exam/contest passed
- **Festive occasion**: Birthday, work anniversary, New Year's Eve, version milestone
- **Emotional expression**: User wants to "feel happy", "what a great day", "I'm so excited"

## How It Works

This skill includes a `fireworks.swift` script (located in the `/scripts` directory alongside this SKILL.md). When executed, it will:

1. Create a transparent, borderless, click-through window above all screens (layered above the menu bar and Dock)
2. Continuously launch and explode colorful fireworks on screen, with trails and glow effects
3. Fade out after the specified duration and automatically terminate the process, leaving no residue

### Commands

> `<SKILL_DIR>` refers to the absolute path of the directory containing this SKILL.md. The agent typically knows this path when loading the skill — replace it with the actual path before execution.

**Default 8 seconds**:

```bash
swift "<SKILL_DIR>/scripts/fireworks.swift" &
```

**Custom duration (seconds)**:

```bash
swift "<SKILL_DIR>/scripts/fireworks.swift" 15 &
```

## Agent Behavior Guidelines

- **Run in background**: Append `&` to the command to avoid blocking the current conversation flow
- **Do not poll / sleep**: The script will automatically exit after the specified duration — no need for the agent to kill it
- **Platform restriction**: Only invoke on macOS; on other systems (Linux / Windows), inform the user that "this fireworks effect is only supported on macOS"
- **Trigger sparingly**: Only run one show at a time; do not trigger at the end of every message in a normal conversation to avoid visual disturbance
- **Prefer default duration**: The default 8 seconds provides sufficient ceremony — do not add a duration parameter unless the user explicitly requests it

## Requirements

- macOS (any modern version, uses the built-in Cocoa / AppKit framework)
- `swift` command available (bundled with Xcode or Command Line Tools; install with `xcode-select --install` if missing)
- No network, disk write, or screen recording permissions required

## Implementation Details

- **Rocket**: A projectile that rises in a parabolic arc from the bottom of the screen with a fading trail, exploding upon reaching its target height
- **Particle**: Colorful particles produced by the explosion, affected by gravity and air resistance; three-layer composition of trail + glow + core using the `plusLighter` blend mode for a luminous effect
- **Window**: Pinned with `kCGMaximumWindowLevel`, click-through via `ignoresMouseEvents = true`, displayed across all Spaces with `canJoinAllSpaces + stationary`
- **Animation**: Driven by a 60 FPS Timer, fade-in 0.35s / fade-out 1s, auto-terminates via `NSApp.terminate` when time is up

## Acknowledgements

Inspired by Happy Camp (快乐大本营) — "simply happy" is an attitude.
