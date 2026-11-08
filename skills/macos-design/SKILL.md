---
name: macos-design
description: Design and build native-feeling macOS application UIs. Use this skill whenever the user asks to create a desktop app, macOS app, Mac-style interface, Apple-style UI, system utility, or anything that should look and feel like a native Mac application. Also trigger when users mention "native feel", "desktop app design", "Apple design patterns", "sidebar layout", "traffic lights", or want to build tools/utilities that feel like they belong on macOS. This skill covers layout, composition, interaction patterns, animations, light/dark mode, and all the subtle details that make an app feel like Apple built it.
---

# macOS Native App Design Skill

Build interfaces that feel like they belong on the user's computer — not websites crammed into a window.

## Core Philosophy

A native app is not a destination. It is a **system tool** that lives where the user needs it. Design every interaction around this principle: appear when needed, get out of the way immediately after.

## Before You Code

Read these references based on what you're building:

- **All macOS apps** → Read `references/layout-and-composition.md` (required)
- **Apps with keyboard shortcuts, panels, toasts, popovers** → Read `references/interaction-patterns.md`
- **Light/dark mode, color, typography** → Read `references/visual-design.md`

## Quick-Start Checklist

Use this as a pre-flight before writing any code:

1. **Layout**: Top bar for global actions, sidebar for navigation (skip if nav is minimal), center for content
2. **Traffic lights**: Integrate into the UI — top bar or sidebar, never floating awkwardly
3. **Window drag zone**: Top ~50px must be draggable, keep it uncluttered
4. **Empty states**: Show them. Progressive disclosure — only reveal UI when it's useful
5. **Keyboard shortcuts**: Every primary action needs one. Every shortcut needs visual feedback
6. **Light + Dark mode**: Design both. Do NOT directly invert colors (see visual-design reference)
7. **Search**: Always prominent and accessible. Consider floating search bar or command palette
8. **Drag and drop**: Content in AND out of the app. This is non-negotiable for native feel
9. **Micro-animations**: Every state change gets a transition. No interaction without feedback
10. **Onboarding**: Brief, modal-based, teaches shortcuts through doing (not reading)

## Implementation Notes

When building as a web artifact (React/HTML):
- Simulate the macOS window chrome (title bar, traffic light dots, rounded corners)
- Use `-apple-system, BlinkMacSystemFont, "SF Pro Display", "SF Pro Text"` font stack
- Use `backdrop-filter: blur()` for native vibrancy/translucency effects
- Rounded corners: 10px for windows, 8px for cards, 6px for buttons, 4px for inputs
- Respect `prefers-color-scheme` media query for automatic light/dark switching
- Shadows should be subtle and layered, not a single heavy drop shadow

When building with Electron, Tauri, or native frameworks:
- Use system title bar integration where possible
- Respect system accent color and appearance settings
- Use native drag-and-drop APIs, not polyfills
