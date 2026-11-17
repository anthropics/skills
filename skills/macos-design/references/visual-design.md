# Visual Design Reference

## Table of Contents
1. Light & Dark Mode
2. Color System
3. Typography
4. Blur, Vibrancy & Translucency
5. Shadows & Depth
6. Iconography
7. Spacing & Sizing

---

## 1. Light & Dark Mode

**Critical rule: Do NOT directly invert colors between modes.**

Direct inversion causes problems because dark mode requires colors with MORE differentiation between them. When you directly invert a dark palette to light, the contrast is too high and harsh. When you invert light to dark, everything looks muddy.

**Design each mode independently:**

Light mode:
- Backgrounds should be close together (white, off-white, very light gray)
- Colors can be more collapsed / similar — the ambient light provides differentiation
- Text: near-black (#1D1D1F) on white (#FFFFFF) or off-white (#F5F5F7)

Dark mode:
- Backgrounds need more separation between levels (e.g., #1C1C1E, #2C2C2E, #3A3A3C)
- Colors should be more spread out and vibrant — compensating for less ambient light
- Text: off-white (#F5F5F7) on dark (#1C1C1E)
- Avoid pure black (#000000) backgrounds — Apple uses dark grays

**The modes should feel different but consistent.** Same layout, same structure, same brand — but the palette is adjusted, not mirrored.

### CSS Variables Pattern

```css
:root {
  /* Light mode (default) */
  --bg-primary: #FFFFFF;
  --bg-secondary: #F5F5F7;
  --bg-tertiary: #E8E8ED;
  --bg-elevated: #FFFFFF;

  --text-primary: #1D1D1F;
  --text-secondary: #6E6E73;
  --text-tertiary: #AEAEB2;

  --border: rgba(0, 0, 0, 0.08);
  --border-strong: rgba(0, 0, 0, 0.15);

  --accent: #007AFF;       /* System blue */
  --accent-hover: #0066D6;

  --surface-hover: rgba(0, 0, 0, 0.04);
  --surface-active: rgba(0, 0, 0, 0.08);

  --shadow-sm: 0 1px 3px rgba(0,0,0,0.06);
  --shadow-md: 0 4px 12px rgba(0,0,0,0.08);
  --shadow-lg: 0 8px 30px rgba(0,0,0,0.12);
}

@media (prefers-color-scheme: dark) {
  :root {
    --bg-primary: #1C1C1E;
    --bg-secondary: #2C2C2E;
    --bg-tertiary: #3A3A3C;
    --bg-elevated: #2C2C2E;

    --text-primary: #F5F5F7;
    --text-secondary: #98989D;
    --text-tertiary: #636366;

    --border: rgba(255, 255, 255, 0.08);
    --border-strong: rgba(255, 255, 255, 0.15);

    --accent: #0A84FF;       /* Slightly brighter blue for dark */
    --accent-hover: #409CFF;

    --surface-hover: rgba(255, 255, 255, 0.06);
    --surface-active: rgba(255, 255, 255, 0.1);

    --shadow-sm: 0 1px 3px rgba(0,0,0,0.2);
    --shadow-md: 0 4px 12px rgba(0,0,0,0.3);
    --shadow-lg: 0 8px 30px rgba(0,0,0,0.4);
  }
}
```

**Apple's system accent colors** (use as needed):
| Color  | Light        | Dark         |
|--------|-------------|-------------|
| Blue   | #007AFF     | #0A84FF     |
| Green  | #34C759     | #30D158     |
| Red    | #FF3B30     | #FF453A     |
| Orange | #FF9500     | #FF9F0A     |
| Yellow | #FFCC00     | #FFD60A     |
| Purple | #AF52DE     | #BF5AF2     |
| Pink   | #FF2D55     | #FF375F     |
| Teal   | #5AC8FA     | #64D2FF     |

---

## 2. Color System

**Hierarchy through backgrounds, not borders:**
- Level 0 (base): `--bg-primary` — the window background
- Level 1 (sections): `--bg-secondary` — sidebar, panels
- Level 2 (cards/items): `--bg-tertiary` or `--bg-elevated` — content cards
- Level 3 (inputs): slightly different from their container

**Use borders sparingly.** macOS uses very thin (0.5px), low-opacity borders for subtle definition, never thick or dark ones.

**Accent color usage:**
- Primary actions (buttons, links, active states)
- Selected items in lists/grids
- Focus rings
- Toggle/switch on-state
- Progress indicators

Never use accent color for large background areas. It's for highlights and interactive elements only.

---

## 3. Typography

**Font stack:**
```css
font-family: -apple-system, BlinkMacSystemFont, "SF Pro Display", "SF Pro Text",
             "Helvetica Neue", Helvetica, Arial, sans-serif;
```

**SF Pro Display** for larger text (20px+), **SF Pro Text** for body (under 20px). The `-apple-system` stack handles this automatically on macOS.

**Type scale (Apple's system):**
| Role           | Size   | Weight   | Line Height |
|----------------|--------|----------|-------------|
| Large Title    | 26px   | Bold     | 32px        |
| Title 1        | 22px   | Regular  | 28px        |
| Title 2        | 17px   | Regular  | 22px        |
| Title 3        | 15px   | Semibold | 20px        |
| Body           | 13px   | Regular  | 18px        |
| Callout        | 12px   | Regular  | 16px        |
| Footnote       | 12px   | Regular  | 16px        |
| Caption        | 11px   | Regular  | 14px        |
| Mini           | 9px    | Medium   | 12px        |

**Notes:**
- macOS apps use smaller type than web or mobile. 13px body is standard.
- Letter spacing is tight — Apple uses -0.01 to -0.03em for headlines
- Weight range: Regular (400) for body, Medium (500) for emphasis, Semibold (600) for headings, Bold (700) for large titles
- Use opacity or `--text-secondary` color for de-emphasized text, not lighter font weight

**Monospace (for code, shortcuts, technical):**
```css
font-family: "SF Mono", "Menlo", "Monaco", "Courier New", monospace;
```

---

## 4. Blur, Vibrancy & Translucency

The defining visual feature of macOS. Sidebars, toolbars, and popovers use translucent backgrounds with blur.

**CSS implementation:**
```css
/* Sidebar vibrancy */
.sidebar {
  background: rgba(246, 246, 246, 0.72);
  backdrop-filter: saturate(180%) blur(20px);
  -webkit-backdrop-filter: saturate(180%) blur(20px);
}

/* Dark mode sidebar */
@media (prefers-color-scheme: dark) {
  .sidebar {
    background: rgba(30, 30, 30, 0.72);
  }
}

/* Quick-save panel / popover */
.floating-panel {
  background: rgba(255, 255, 255, 0.78);
  backdrop-filter: saturate(180%) blur(20px);
  -webkit-backdrop-filter: saturate(180%) blur(20px);
  border: 0.5px solid rgba(0, 0, 0, 0.1);
  border-radius: 10px;
  box-shadow: 0 8px 32px rgba(0, 0, 0, 0.12);
}
```

**Where to use blur/vibrancy:**
- Sidebars
- Top bars / toolbars
- Floating panels and popovers
- Quick-access windows (Spotlight-style)
- Toast notifications
- Floating action bars

**Where NOT to use blur:**
- Main content area (this should be solid/opaque for readability)
- Modal backgrounds (use a semi-transparent dark overlay instead)
- Body text containers

**Saturation boost:** Apple's vibrancy includes `saturate(180%)` to keep colors from looking washed out behind the blur. Always include this.

---

## 5. Shadows & Depth

macOS uses **layered shadows** — multiple stacked shadow values for realistic depth.

**Levels:**
```css
/* Subtle — cards, buttons */
box-shadow:
  0 0 0 0.5px rgba(0,0,0,0.05),
  0 1px 2px rgba(0,0,0,0.06);

/* Medium — dropdowns, popovers */
box-shadow:
  0 0 0 0.5px rgba(0,0,0,0.06),
  0 4px 16px rgba(0,0,0,0.1);

/* Heavy — floating windows, modals */
box-shadow:
  0 0 0 0.5px rgba(0,0,0,0.1),
  0 2px 8px rgba(0,0,0,0.08),
  0 8px 30px rgba(0,0,0,0.14),
  0 24px 60px rgba(0,0,0,0.08);

/* Window shadow (the main app window) */
box-shadow:
  0 0 0 0.5px rgba(0,0,0,0.1),
  0 12px 40px rgba(0,0,0,0.15),
  0 40px 80px rgba(0,0,0,0.1);
```

**Key detail:** The `0 0 0 0.5px` border-shadow is essential. It gives subtle definition to edges without using a visible border. This is THE macOS look.

**Dark mode shadows:** Increase opacity by ~2x since shadows are less visible against dark backgrounds.

---

## 6. Iconography

Follow **SF Symbols** design language:
- Monoline stroke style (1.5-2px stroke width)
- Simple, geometric shapes
- 16px default, 20px for prominent actions, 12px for inline hints
- Use `currentColor` so icons inherit text color
- Slight rounded corners on strokes

**Common macOS icons to implement:**
- Search: magnifying glass
- Settings: gear
- Share: square with up-arrow
- Add: plus
- Close: × (not a filled circle)
- Back: left arrow
- Sidebar: rectangle split vertically
- Grid/List: grid dots / horizontal lines
- Trash: trash can outline

---

## 7. Spacing & Sizing

macOS uses an **8px base grid** for most spacing.

**Common spacings:**
| Context                    | Value    |
|---------------------------|----------|
| Window padding             | 16-20px  |
| Section gap                | 24px     |
| Card gap (grid)            | 12-16px  |
| Element gap (buttons, etc) | 8px      |
| Inner padding (cards)      | 12px     |
| Inner padding (buttons)    | 6px 12px |
| Inner padding (inputs)     | 8px 12px |
| Icon-to-label gap          | 6px      |
| Divider margin             | 8px 0    |

**Interactive element sizes:**
| Element           | Height  |
|-------------------|---------|
| Top bar           | 48-52px |
| Button (default)  | 28px    |
| Button (large)    | 34px    |
| Input field       | 28px    |
| Sidebar row       | 28-32px |
| List row          | 36-44px |
| Toolbar icon btn  | 28×28px |

**Corner radii:**
| Element           | Radius  |
|-------------------|---------|
| Window            | 10px    |
| Modal / Panel     | 12px    |
| Card              | 8px     |
| Button            | 6px     |
| Input             | 6px     |
| Tag / Badge       | 4px     |
| Toggle            | 14px (pill) |
| Tooltip           | 4px     |
| Image thumbnail   | 6-8px   |
