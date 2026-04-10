# Elevation & Shadows Reference

Shadows communicate depth — how high above the page surface an element sits. A consistent elevation system makes a UI feel physically grounded and helps users understand which elements are layered above others.

---

## The Elevation Hierarchy

Think of your UI as having physical layers, like sheets of paper stacked on a table:

| Level | Elements | Shadow Strength |
|---|---|---|
| **0 — Surface** | Page background, table rows | No shadow |
| **1 — Raised** | Cards, panels, input fields | Very subtle |
| **2 — Floating** | Sticky headers, FABs, sidebars | Soft, visible |
| **3 — Overlay** | Dropdowns, popovers, tooltips | Medium |
| **4 — Modal** | Dialogs, drawers, side sheets | Strong |
| **5 — Maximum** | Notifications, critical alerts | Strongest |

Higher = more prominent = stronger shadow. Elements at the same level should have the same shadow.

---

## Shadow Scale

Define shadows as a scale, not per-element:

```css
:root {
  --shadow-sm:   0 1px 2px rgba(0, 0, 0, 0.06);
  --shadow-md:   0 4px 8px rgba(0, 0, 0, 0.08), 0 1px 3px rgba(0, 0, 0, 0.05);
  --shadow-lg:   0 8px 24px rgba(0, 0, 0, 0.10), 0 2px 6px rgba(0, 0, 0, 0.06);
  --shadow-xl:   0 16px 48px rgba(0, 0, 0, 0.12), 0 4px 12px rgba(0, 0, 0, 0.08);
  --shadow-2xl:  0 24px 64px rgba(0, 0, 0, 0.14), 0 8px 20px rgba(0, 0, 0, 0.08);
}
```

### Mapping to Elevation Levels

| Level | Token |
|---|---|
| Cards | `--shadow-sm` |
| Sticky header / FAB | `--shadow-md` |
| Dropdowns / popovers | `--shadow-lg` |
| Modals | `--shadow-xl` |
| Critical overlays | `--shadow-2xl` |

---

## Shadow Anatomy

A box shadow has four values: `offset-x offset-y blur spread color`

```css
box-shadow: 0 4px 8px rgba(0, 0, 0, 0.08);
/*          ↑ ↑   ↑    ↑
            | |   |    color (opacity = strength)
            | |   blur radius
            | offset-y (vertical — positive = shadow below)
            offset-x (horizontal — 0 = centered light source)
```

### The Ratio Rule
For a grounded, realistic shadow: **blur ≈ 2× offset-y**

```
offset-y: 4px → blur: 8px  ✅ grounded
offset-y: 4px → blur: 40px ❌ looks like a glow, not a shadow
offset-y: 4px → blur: 4px  ❌ looks harsh and pixelated
```

### Layered Shadows
Professional shadows often combine two layers — one for ambient light, one for direct light:

```css
/* Ambient (wide, soft) + Direct (tight, stronger) */
box-shadow:
  0 8px 24px rgba(0, 0, 0, 0.08),   /* ambient */
  0 2px 6px  rgba(0, 0, 0, 0.06);   /* direct */
```

This creates more realistic, nuanced depth than a single shadow.

---

## Shadow Color

**Never use pure black** (`rgba(0,0,0,1)`) for shadows. Real shadows are:
- Semi-transparent (typically 5–15% opacity)
- Slightly warm or cool depending on the light source
- Tinted by the surface color beneath

### For Light Mode
```css
/* Standard: neutral dark */
rgba(0, 0, 0, 0.08)

/* Warmer feel */
rgba(15, 10, 5, 0.10)

/* Brand-tinted shadow (subtle) */
rgba(124, 58, 237, 0.12) /* purple tint for purple brand */
```

### For Dark Mode
Shadows don't work on dark backgrounds — a dark shadow on a dark surface is invisible.

**Instead, use surface color elevation:**
```css
/* Dark mode elevation via lightness, not shadow */
--surface-0: #121212;   /* base */
--surface-1: #1e1e1e;   /* cards (+elevation 1) */
--surface-2: #242424;   /* dropdowns (+elevation 2) */
--surface-3: #2c2c2c;   /* modals (+elevation 3) */
```

Each elevated layer is slightly lighter. No shadows needed.

---

## Common Shadow Mistakes

| Mistake | Why It's Wrong | Fix |
|---|---|---|
| Same shadow on all elements | Destroys elevation hierarchy — cards and modals look the same depth | Use different shadow levels per elevation |
| Pure black shadow at 100% opacity | Looks harsh and fake | Use rgba with 5–15% opacity |
| Very large blur with tiny offset | Looks like a glow, not a shadow | Match blur to ~2× offset-y |
| Shadows in dark mode | Invisible — dark shadow on dark background does nothing | Use lighter surface colors instead |
| Directional shadows inconsistency | Some elements shadow down, some shadow right — looks like multiple light sources | Always use offset-x: 0, offset-y: positive (light from above) |
| Decorative shadow on flat elements | Shadows mean elevation — using them decoratively confuses the hierarchy | Only shadow actually elevated elements |
| Shadow + border on same card | Double-defining the card boundary — usually one or the other is enough | Pick shadow OR subtle border, not both (unless intentional) |

---

## Interaction Shadows

Shadows can also communicate interactive state changes:

```css
/* Button: resting → hovered → pressed */
.button {
  box-shadow: var(--shadow-sm);        /* resting */
  transition: box-shadow 0.15s ease, transform 0.15s ease;
}

.button:hover {
  box-shadow: var(--shadow-md);        /* rises on hover */
  transform: translateY(-1px);         /* slight lift */
}

.button:active {
  box-shadow: none;                    /* pressed flat */
  transform: translateY(0);            /* back down */
}
```

This creates a tactile, physical feel — the button lifts on hover and presses down on click.

---

## Figma Elevation Checklist

When auditing a Figma file:
- [ ] Are shadows applied via shared styles/variables? (not individual custom values)
- [ ] Do cards all use the same shadow? Modals all use the same shadow?
- [ ] Is there a defined shadow scale in the design system?
- [ ] Are dark mode frames using surface colors instead of shadows?
- [ ] Do interactive elements change shadow on hover/active?
