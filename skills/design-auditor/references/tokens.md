# Design Tokens & Variables Health Reference

Design tokens are the single source of truth for visual decisions — colors, spacing, typography, shadows, radii. A healthy token system means changing one value updates the entire product. A broken system means hunting through hundreds of files to change a brand color.

---

## What Are Design Tokens?

Design tokens are named variables that store visual values:

```
color.primary.500 = #7c3aed
spacing.4 = 16px
font.size.body = 16px
radius.md = 8px
shadow.card = 0 4px 8px rgba(0,0,0,0.08)
```

Instead of using `#7c3aed` directly in a component, you reference `color.primary.500`. When the brand color changes, you update one token — everything updates automatically.

---

## Token Naming Systems

### Anti-Pattern: Descriptive Names
Naming tokens after their appearance breaks when values change:

```
❌ color.purple = #7c3aed   → What if purple becomes blue? The name is now wrong.
❌ color.red-500 = #ef4444  → Is this always used for danger? Or sometimes for decoration?
```

### Best Practice: Semantic Names
Name tokens by their **purpose**, not their **value**:

```
✅ color.brand.primary = #7c3aed     → The main brand color, whatever it is
✅ color.feedback.danger = #ef4444   → Used for error states everywhere
✅ color.text.secondary = #6b7280    → Secondary text color
✅ color.background.surface = #f9fafb → Card/panel backgrounds
```

### Two-Tier Token System (Industry Best Practice)

**Tier 1 — Primitive tokens** (raw values):
```
color.purple.500 = #7c3aed
color.red.500 = #ef4444
spacing.4 = 16px
```

**Tier 2 — Semantic tokens** (reference primitives):
```
color.brand.primary = color.purple.500
color.feedback.danger = color.red.500
color.interactive.default = color.purple.500
```

Components reference **semantic tokens only**. Primitives are never used directly in components. This allows you to remap semantic meaning without touching components (e.g. changing brand color from purple to blue: update one primitive reference).

---

## Token Categories

### Color Tokens

```
color.brand.primary       — Primary brand color (buttons, links, highlights)
color.brand.secondary     — Secondary brand color
color.brand.accent        — Accent/pop color

color.text.primary        — Main body text
color.text.secondary      — Supporting text, captions
color.text.disabled       — Disabled state text
color.text.inverse        — Text on dark/colored backgrounds
color.text.link           — Hyperlink color

color.background.page     — Base page/app background
color.background.surface  — Cards, panels, containers
color.background.elevated — Dropdowns, modals, tooltips
color.background.overlay  — Modal backdrop scrim

color.border.default      — Standard borders
color.border.subtle       — Dividers, faint borders
color.border.focus        — Focus ring color
color.border.danger       — Error state border

color.feedback.success    — Success states
color.feedback.warning    — Warning states
color.feedback.danger     — Error states
color.feedback.info       — Informational states
```

### Spacing Tokens
```
spacing.1  = 4px
spacing.2  = 8px
spacing.3  = 12px
spacing.4  = 16px
spacing.6  = 24px
spacing.8  = 32px
spacing.10 = 40px
spacing.12 = 48px
spacing.16 = 64px
```

### Typography Tokens
```
font.family.sans    = 'Figtree', sans-serif
font.family.mono    = 'JetBrains Mono', monospace

font.size.xs   = 11px
font.size.sm   = 13px
font.size.md   = 15px
font.size.base = 16px
font.size.lg   = 18px
font.size.xl   = 20px
font.size.2xl  = 24px
font.size.3xl  = 30px
font.size.4xl  = 36px

font.weight.regular    = 400
font.weight.medium     = 500
font.weight.semibold   = 600
font.weight.bold       = 700

line.height.tight   = 1.2
line.height.snug    = 1.35
line.height.normal  = 1.5
line.height.relaxed = 1.6
```

---

## Dark Mode Token Architecture

The most important benefit of a semantic token system is clean dark mode support.

### How It Works
Instead of creating separate dark mode components, you remap semantic token values:

```css
/* Light mode */
:root {
  --color-background-page: #ffffff;
  --color-text-primary: #111827;
  --color-background-surface: #f9fafb;
  --color-border-default: #e5e7eb;
}

/* Dark mode — same tokens, different values */
[data-theme="dark"] {
  --color-background-page: #0f172a;
  --color-text-primary: #f1f5f9;
  --color-background-surface: #1e293b;
  --color-border-default: #334155;
}
```

Components use `var(--color-background-page)` — they don't need to know which mode they're in. The theme switch happens at one level.

### Signs the Token System is Broken for Dark Mode
- Components have hardcoded hex values that don't change in dark mode
- Dark mode overrides are scattered across individual component files
- Dark mode colors are new hardcoded values, not remapped tokens
- Some components adapt to dark mode but others don't

---

## Auditing Token Health in a Codebase

### Signs of a Healthy Token System
- All colors in components reference CSS variables or JS tokens
- No hardcoded hex values (`#abc123`) in component styles
- Spacing values are multiples of the base unit (4 or 8)
- Typography uses a defined text style system
- Dark mode works by swapping a theme class, not editing components

### Signs of a Broken Token System

**Red flags in CSS/code:**
```css
/* ❌ Hardcoded values — no token */
color: #7c3aed;
margin: 13px;
font-size: 15px;
border-radius: 7px;
box-shadow: 0 3px 7px rgba(0,0,0,0.11);
```

```css
/* ✅ Tokenized */
color: var(--color-brand-primary);
margin: var(--spacing-3);
font-size: var(--font-size-md);
border-radius: var(--radius-md);
box-shadow: var(--shadow-sm);
```

**Red flags in Figma:**
- Components use local styles instead of shared library styles
- Colors show as hex values in the inspector, not style names
- "Detached" text styles (no linked text style)
- Different teams using different color values for the same UI element

### Token Coverage Audit

Run a search for hardcoded values in your codebase:
```bash
# Find hardcoded hex colors (not in token definition files)
grep -r "#[0-9a-fA-F]\{3,6\}" src/components/

# Find hardcoded pixel spacing
grep -rE "margin|padding|gap" src/components/ | grep -v "var(--"

# Find hardcoded font sizes
grep -rE "font-size:\s*[0-9]" src/components/ | grep -v "var(--"
```

Any hits in component files (not token definition files) are candidates for tokenization.

---

## Token System Maturity Levels

| Level | Description | Signs |
|---|---|---|
| **0 — No system** | All values hardcoded | Hex values everywhere, no variables |
| **1 — Basic variables** | CSS variables exist but naming is inconsistent | Mix of `--purple`, `--color-primary`, `#7c3aed` |
| **2 — Consistent naming** | Variables follow a naming convention | All components use tokens, names are meaningful |
| **3 — Semantic + primitive** | Two-tier system in place | Components only use semantic tokens |
| **4 — Multi-theme** | Token system supports light/dark/brand themes | Theme switching works by swapping one class |
| **5 — Cross-platform** | Tokens shared between web, iOS, Android | Single source of truth across platforms |

---

## Common Token Mistakes

| Mistake | Fix |
|---|---|
| Naming tokens by value (`--red`, `--purple-500`) | Name by purpose (`--color-danger`, `--color-brand-primary`) |
| Using primitive tokens directly in components | Create semantic tokens; components reference semantic only |
| Hardcoding hex values in components | Replace with token references |
| Different tokens for same concept in different parts of codebase | Audit and consolidate — one token per concept |
| Dark mode via per-component overrides | Remap semantic tokens at theme level |
| Tokens defined but not used consistently | Enforce via linting (stylelint, custom ESLint rules) |
| Spacing that doesn't follow the token scale | Replace with scale tokens, remove magic numbers |

---

## Token Health Score

Use this formula to quickly assess the health of a token system during an audit:

### How to Score

Check 5 areas, each worth 20 points:

| Area | 20pts (Full) | 10pts (Partial) | 0pts (Missing) |
|---|---|---|---|
| **Color** | All colors are tokens, semantic naming | Mix of tokens + hardcoded | Mostly hardcoded hex |
| **Spacing** | All spacing uses scale tokens | Some tokens, some arbitrary | Mostly arbitrary px values |
| **Typography** | Font size/weight/line-height tokenized | Partial tokenization | All hardcoded |
| **Dark Mode** | Single theme swap, no new hex values | Some components adapt | Per-component overrides or no dark mode |
| **Naming** | Semantic (purpose-based) naming throughout | Mix of semantic + descriptive | Descriptive or no naming convention |

### Token Health Score Bands

| Score | Health Level | What It Means |
|---|---|---|
| **90–100** | ✅ Excellent | System is production-grade, scalable, and maintainable |
| **70–89** | 🟡 Good | Minor gaps, easy to clean up |
| **50–69** | 🟠 Needs Work | Significant hardcoding, inconsistent adoption |
| **< 50** | 🔴 Broken | Tokens exist in name only — no real system |

### Quick Audit Command
Run this to get a rough hardcoded value count in a codebase:
```bash
# Count hardcoded hex colors in component files
grep -rE "#[0-9a-fA-F]{3,6}" src/components/ | grep -v "token\|variable\|\.tokens\." | wc -l

# Count hardcoded px spacing (not in token files)
grep -rE "(margin|padding|gap):\s*[0-9]+px" src/components/ | grep -v "var(--" | wc -l
```

A healthy codebase returns **0** for both. Every non-zero hit is a token debt item.
