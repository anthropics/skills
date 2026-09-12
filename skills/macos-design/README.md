# macOS Design Skill

> Build native-feeling macOS applications that look like Apple designed them.

![SnapVault Demo](https://img.shields.io/badge/Demo-SnapVault-blue)
![macOS](https://img.shields.io/badge/Platform-macOS-black)
![Design System](https://img.shields.io/badge/Design-Native-success)

## Overview

This skill provides a **complete design system** for creating native macOS application UIs. It captures years of Apple design knowledge distilled into actionable guidelines, exact values, and production-ready patterns.

## Features

- ✅ **Complete Layout System** - The Apple formula (traffic lights, top bar, sidebar, content)
- ✅ **Visual Design** - Colors, typography, blur/vibrancy, shadows, icons, spacing
- ✅ **Interaction Patterns** - Keyboard shortcuts, animations, search, drag-and-drop
- ✅ **Light + Dark Mode** - Proper differentiation, not naive inversion
- ✅ **Production-Ready** - Exact CSS values, code snippets, implementation details
- ✅ **Cross-Platform** - Works for web, Electron, Tauri, native frameworks

## Quick Start

### For Claude Code

```bash
# Install the skill
claude code install macos-design

# Use in your project
/macos-design Create a screenshot organizer app
```

### Manual Usage

Read the reference files based on what you're building:

- **All macOS apps** → [`layout-and-composition.md`](./layout-and-composition.md) (required)
- **Keyboard shortcuts, panels, search** → [`interaction-patterns.md`](./interaction-patterns.md)
- **Colors, typography, blur effects** → [`visual-design.md`](./visual-design.md)

## Demo: SnapVault

Included is **SnapVault**, a fully functional screenshot organizer that demonstrates every principle:

- Native window chrome with integrated traffic lights
- Translucent sidebar with backdrop blur
- Responsive grid layout with staggered animations
- Keyboard shortcuts (`⌘N`, `⌘F`, `Esc`)
- Real-time search filtering
- Drag-and-drop support
- Toast notifications with optimistic UI
- Full light/dark mode support

**[Open SnapVault Demo →](./snapvault.html)**

## What You'll Build

This skill enables you to create:

- Desktop utilities that feel native to macOS
- Screenshot managers, note-taking apps, asset browsers
- Developer tools, productivity apps, system utilities
- Anything that should integrate seamlessly with the Mac ecosystem

## Key Principles

### 1. **Don't Invert Colors**

Dark mode needs MORE differentiation between background levels, not less. Design each mode independently.

```css
/* Light: backgrounds close together */
--bg-primary: #FFFFFF;
--bg-secondary: #F5F5F7;

/* Dark: backgrounds spread out */
--bg-primary: #1C1C1E;
--bg-secondary: #2C2C2E;
```

### 2. **Vibrancy is Essential**

Use `backdrop-filter: blur()` with `saturate(180%)` for sidebars, toolbars, and panels.

### 3. **Layered Shadows**

The signature `0 0 0 0.5px` creates subtle edge definition without visible borders.

### 4. **Keyboard Shortcuts First**

Every primary action needs a shortcut. Show hints with `<kbd>` elements.

### 5. **Progressive Disclosure**

Only show UI when it's useful. Hide filters/toolbars when there's no content.

## Design System Highlights

### Typography
- **Font Stack**: `-apple-system, BlinkMacSystemFont, "SF Pro Display", "SF Pro Text"`
- **Body Size**: 13px (macOS apps use smaller type than web)
- **Weights**: Regular (400), Medium (500), Semibold (600), Bold (700)

### Spacing (8px Grid)
| Context | Value |
|---------|-------|
| Window padding | 16-20px |
| Section gap | 24px |
| Card gap | 12-16px |
| Button padding | 6px 12px |

### Corner Radii
| Element | Radius |
|---------|--------|
| Window | 10px |
| Card | 8px |
| Button | 6px |
| Input | 6px |

### Animations
```css
--ease-out: cubic-bezier(0.25, 0.46, 0.45, 0.94);
--duration-fast: 150ms;
--duration-normal: 250ms;
```

## Files

```
.
├── SKILL.md                      # Skill definition and quick-start
├── README.md                     # This file
├── layout-and-composition.md     # Layout patterns and structure
├── visual-design.md              # Colors, typography, shadows, blur
├── interaction-patterns.md       # Keyboard, animations, search, drag-drop
└── snapvault.html               # Demo app showcasing all principles
```

## Browser Compatibility

The demo uses modern CSS features:
- `backdrop-filter` (Safari, Chrome, Edge)
- CSS custom properties
- `prefers-color-scheme` media query

For production apps, consider fallbacks for older browsers.

## Credits

Design principles derived from:
- Apple Human Interface Guidelines
- macOS system apps (Finder, Notes, Reminders, Settings)
- Third-party excellence (Raycast, Paste, Bartender)

## License

MIT - Feel free to use in your own projects!

---

**Built with ❤️ for macOS designers and developers**
