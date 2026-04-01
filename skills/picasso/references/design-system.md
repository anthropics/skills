# Design System Reference

## Table of Contents
1. DESIGN.md Format
2. Theme Generation
3. Token Structure
4. Pre-Built Themes

---

## 1. DESIGN.md Format

When generating a design system document, follow this structure (derived from the Google Stitch DESIGN.md format, extended by VoltAgent):

```markdown
# DESIGN.md

## 1. Visual Theme & Atmosphere
Describe the mood, density, and design philosophy. Is this minimal or dense?
Warm or cold? Playful or serious? What existing products or aesthetics does it
reference?

## 2. Color Palette & Roles
| Token | OKLCH | Hex (fallback) | Role |
|---|---|---|---|
| surface-primary | oklch(0.985 0.005 80) | #fafaf9 | Page background |
| surface-secondary | oklch(0.97 0.008 80) | #f5f5f4 | Card/section background |
| text-primary | oklch(0.15 0.02 60) | #1c1917 | Headings and body text |
| text-secondary | oklch(0.40 0.02 60) | #57534e | Supporting text, labels |
| accent | oklch(0.55 0.25 25) | #dc2626 | CTAs, active states, links |
| accent-hover | oklch(0.48 0.25 25) | #b91c1c | Hover state for accent |
| accent-subtle | oklch(0.97 0.02 25) | #fef2f2 | Accent-tinted background |
| border | oklch(0.91 0.01 80) | #e7e5e4 | Default borders |
| success | oklch(0.55 0.18 145) | #16a34a | Success states |
| warning | oklch(0.65 0.18 70) | #d97706 | Warning states |
| error | oklch(0.55 0.22 25) | #dc2626 | Error states |

## 3. Typography Rules
| Level | Font | Size | Weight | Line Height | Letter Spacing |
|---|---|---|---|---|---|
| Display | [Display Font] | 3rem | 700 | 1.1 | -0.02em |
| H1 | [Display Font] | 2.25rem | 700 | 1.15 | -0.01em |
| H2 | [Display Font] | 1.875rem | 600 | 1.2 | -0.01em |
| H3 | [Body Font] | 1.5rem | 600 | 1.25 | 0 |
| Body | [Body Font] | 1rem | 400 | 1.6 | 0 |
| Small | [Body Font] | 0.875rem | 400 | 1.5 | 0 |
| Caption | [Body Font] | 0.75rem | 500 | 1.4 | 0.02em |
| Code | [Mono Font] | 0.875rem | 400 | 1.6 | 0 |

## 4. Component Styling
### Buttons
| Variant | Background | Text | Border | Radius | Padding |
|---|---|---|---|---|---|
| Primary | accent | white | none | 8px | 12px 24px |
| Secondary | transparent | text-primary | 1px border | 8px | 12px 24px |
| Ghost | transparent | text-secondary | none | 8px | 12px 24px |
| Destructive | error | white | none | 8px | 12px 24px |

States: hover (darken bg 5%), active (darken 10%, scale 0.98), disabled (opacity 0.5), focus (2px accent outline, 2px offset).

### Cards
Background: surface-secondary. Border: 1px border. Radius: 12px.
Padding: 24px. Shadow: 0 1px 3px rgba(0,0,0,0.05).
Hover: shadow increases to 0 4px 12px rgba(0,0,0,0.08).

### Inputs
Height: 44px. Border: 1px border. Radius: 8px. Padding: 0 12px.
Focus: 2px accent border, subtle accent glow.
Error: error border, error message below.
Disabled: opacity 0.5, cursor not-allowed.

### Navigation
Describe the navigation pattern (sidebar, top bar, tabs) with specific dimensions,
colors, and active/hover states.

## 5. Layout Principles
Spacing scale: 4, 8, 12, 16, 24, 32, 48, 64, 96.
Max content width: [value]px.
Grid: [columns] columns with [gap]px gaps.
Page margins: [value]px on desktop, [value]px on mobile.

## 6. Depth & Elevation
| Level | Shadow | Use |
|---|---|---|
| 0 | none | Flat elements, inline content |
| 1 | 0 1px 2px rgba(0,0,0,0.05) | Cards, dropdowns |
| 2 | 0 4px 12px rgba(0,0,0,0.08) | Floating elements, hover cards |
| 3 | 0 8px 24px rgba(0,0,0,0.12) | Modals, dialogs |
| 4 | 0 16px 48px rgba(0,0,0,0.16) | Popovers, overlays |

## 7. Do's and Don'ts
### Do
- [specific guidance for this design system]

### Don't
- [specific anti-patterns to avoid]

## 8. Responsive Behavior
Breakpoints: [values].
Mobile navigation: [pattern].
Column collapse strategy: [how grids simplify].
Touch target minimum: 48px.

## 9. Agent Prompt Guide
Quick reference for AI agents building with this system:
- Primary color: [hex]
- Background: [hex]
- Font family: [name]
- Border radius: [value]
- Spacing unit: [value]
```

---

## 2. Theme Generation

When creating a custom theme, follow this process:

1. **Start with the accent color.** This is usually the brand color or the primary action color.
2. **Derive surfaces.** Take the accent hue, reduce chroma to near-zero, and create a lightness scale.
3. **Build the text scale.** Tint near-black toward the accent hue for warmth.
4. **Choose fonts.** Match the emotional register (serif for editorial/luxury, sans for tech/modern, mono for developer/terminal).
5. **Set border radius.** 0px for brutalist, 4-8px for professional, 12-16px for friendly, 999px for pill-shaped.
6. **Define shadows.** Match the overall aesthetic (no shadows for flat designs, layered shadows for elevated designs).

---

## 3. Token Structure

Organize tokens by function, not by value:

```
--color-surface-{0-3}     Backgrounds, from page to elevated
--color-text-{primary,secondary,tertiary}  Text hierarchy
--color-accent             Primary action color
--color-accent-{hover,subtle}  Accent variants
--color-border             Default borders
--color-{success,warning,error,info}  Semantic states
--space-{1-24}             Spacing scale
--radius-{sm,md,lg,full}   Border radius
--shadow-{sm,md,lg,xl}     Elevation
--font-{display,body,mono} Font families
--text-{xs,sm,base,lg,xl,2xl,3xl,4xl}  Type scale
```

---

## 4. Pre-Built Themes

### Midnight Terminal
Dark background, green accent, monospace-forward. Suited for developer tools.
- Surface: oklch(0.12 0.01 150) to oklch(0.20 0.015 150)
- Accent: oklch(0.70 0.20 150) (terminal green)
- Font: JetBrains Mono + IBM Plex Sans
- Radius: 4px

### Warm Editorial
Cream background, serif headings, generous whitespace. Suited for content-heavy sites.
- Surface: oklch(0.97 0.01 60) to oklch(0.93 0.015 60)
- Accent: oklch(0.45 0.15 25) (warm red)
- Font: Instrument Serif + Source Sans 3
- Radius: 2px

### Swiss Precision
White background, strict grid, no decoration. Suited for professional tools.
- Surface: oklch(0.99 0.002 0) to oklch(0.95 0.005 0)
- Accent: oklch(0.50 0.25 250) (blue)
- Font: Outfit + DM Sans
- Radius: 0px

### Soft Pastel
Light pastel background, rounded elements, friendly. Suited for consumer apps.
- Surface: oklch(0.97 0.02 280) to oklch(0.93 0.03 280)
- Accent: oklch(0.60 0.20 280) (soft purple)
- Font: Nunito + Nunito Sans
- Radius: 16px
