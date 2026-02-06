---
name: omnidesign
description: Universal design system with 25 themes, 40+ fonts, and AI industry components
disable-model-invocation: false
---

# OmniDesign Skill

You are an expert in the OmniDesign design system. Use these guidelines when helping users build web applications.

## Design Tokens Available

### Colors (Semantic)
- `color.text.default` — Primary text
- `color.text.muted` — Secondary text
- `color.text.inverted` — Text on dark surfaces
- `color.surface.default` — Default background
- `color.surface.raised` — Cards, elevated surfaces
- `color.surface.sunken` — Inputs, depressed surfaces
- `color.interactive.primary` — Buttons, links
- `color.interactive.primary.hover` — Hover states
- `color.status.success` — Success states
- `color.status.warning` — Warning states
- `color.status.error` — Error states

### Spacing
- `spacing.4` (4px), `spacing.8` (8px), `spacing.16` (16px)
- `spacing.24` (24px), `spacing.32` (32px), `spacing.48` (48px)
- `spacing.64` (64px)

### Typography
- Font families: Geist Sans, Inter, JetBrains Mono, Space Grotesk
- Sizes: 2xs (10px) through 9xl (128px)
- Weights: thin (100) through black (900)

### Shadows
- `shadow.card` — Cards, buttons
- `shadow.dropdown` — Dropdowns, popovers
- `shadow.modal` — Modals, dialogs
- `shadow.focus` — Focus rings

## 25 Themes Available

**Professional:** corporate, navy, slate, forest, ruby, graphite
**Creative:** sunset, ocean, berry, mint, coral, lavender
**Dark:** midnight, noir, cyberpunk, obsidian, deep-space, brutalist
**Light:** daylight, paper, cream, snow, spring, solar
**Specialty:** starry-night

Apply themes via: `data-theme="theme-name"` on html element

## AI Industry Components

When building AI-powered applications, use these patterns:

### Chat Interface
- Message bubbles with markdown support
- Code blocks with syntax highlighting
- Streaming/thinking indicators
- Copy/regenerate actions

### Prompt Input
- Autocomplete suggestions
- Token counter
- Modifier chips (--ar, --v, --style)

### Agent Cards
- Status indicators (online/busy/offline)
- Capability tags
- One-click selection

## Best Practices

1. **Always use tokens** — Never hardcode colors, spacing, or fonts
2. **Test multiple themes** — Components should work across all 25 themes
3. **Follow accessibility** — WCAG 2.1 AA minimum
4. **Use Nerd Fonts for dev tools** — Icons + code in one font
5. **Match semantic tokens to context** — Use `text-muted` for secondary text

## Quick Examples

```css
/* Card component */
.card {
  background: var(--color-surface-raised);
  border-radius: var(--radii-lg);
  padding: var(--spacing-lg);
  box-shadow: var(--shadow-card);
}

/* Button */
.button {
  background: var(--color-interactive-primary);
  color: var(--color-text-inverted);
  padding: var(--spacing-sm) var(--spacing-md);
  border-radius: var(--radii-md);
  font-family: var(--font-sans);
  font-weight: var(--font-weight-medium);
}

.button:hover {
  background: var(--color-interactive-primary-hover);
}
```

## Resources

- Full docs: https://omnidesign.dev
- Quick ref: See QUICKREF.md
- Themes: Run `npm run themes:list`
- Fonts: Run `npm run fonts:list`
