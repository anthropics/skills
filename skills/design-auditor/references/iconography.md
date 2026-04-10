# Iconography Rules Reference

Icons are a universal UI language — but only when used consistently and correctly. Inconsistent iconography is one of the most noticeable signs of an unpolished UI.

---

## Choosing an Icon Library

### The One Library Rule
Use exactly **one icon library** throughout the product. Mixing libraries creates visual inconsistency because each library has its own optical proportions, stroke weights, and corner rounding.

### Popular Libraries & Their Character

| Library | Style | Best For |
|---|---|---|
| **Lucide** | Clean outline, 2px stroke | Modern SaaS, developer tools |
| **Phosphor** | Multi-weight, very versatile | Any product, highly flexible |
| **Heroicons** | Outline + solid variants | Tailwind-based projects |
| **Material Symbols** | Google's system | Android-adjacent, data-heavy UIs |
| **Feather** | Minimal outline | Clean, minimal interfaces |
| **Tabler Icons** | Outline, very complete | Enterprise tools |
| **Radix Icons** | Compact, precise | UI components, design systems |

### Picking a Style
Each library usually offers multiple styles. Pick **one** and don't mix:
- **Outline** — light, airy, modern
- **Filled / Solid** — heavier, more assertive, better at small sizes
- **Duotone** — two-tone, decorative, good for empty states and illustrations
- **Bold / Thick** — accessible, high-contrast, punchy

---

## Icon Sizing

### The Optical Grid
Icons look best at sizes that align to the 4-point grid AND are optical grid-friendly:

| Size | Use Case |
|---|---|
| 12px | Tiny inline indicators (status dots with label) |
| 16px | Dense UI, inline with small text (12–13px) |
| 20px | Default inline with body text (14–16px) |
| 24px | Standard icon button, nav item, list row |
| 32px | Feature icons, section headings |
| 40px | Empty state icons, card decorations |
| 48px | Large empty states, onboarding |
| 64–96px | Hero illustrations (use SVG illustrations, not icons) |

**Avoid:** 18px, 22px, 26px, 28px, 36px — these fall between optical grid lines and look slightly off.

### Matching Icon Size to Text Size

| Text Size | Paired Icon Size |
|---|---|
| 12px | 12–14px |
| 14px | 16px |
| 16px | 20px |
| 18–20px | 24px |
| 24px+ | 28–32px |

---

## Stroke Weight Consistency

Outline icons have a stroke weight. Mixing stroke weights in the same UI feels inconsistent.

| Context | Stroke Weight |
|---|---|
| Dense UI, small icons (16px) | 1.5px |
| Standard UI (20–24px) | 2px |
| Bold/accessible UI | 2.5px |
| Large decorative icons (32px+) | 1.5–2px (lighter at large sizes) |

**Rule:** If your icon library uses 2px strokes and you manually scale an icon up, the stroke doesn't scale — it stays 2px. At 48px, a 2px stroke looks too thin. Either use a bolder variant or adjust stroke weight.

---

## Optical Alignment

Icons are not the same as text — they don't sit on the baseline. Aligning them to text requires care.

### The Bounding Box Problem
Most icons have invisible padding baked into their bounding box. The actual visual weight sits in the center, but the bounding box is square (24×24px). This means:

```
❌ Bad: align icon bounding box to text baseline → icon looks high
✅ Good: align icon to optical center of adjacent text
```

In CSS, use `vertical-align: middle` or flexbox with `align-items: center`:

```css
.icon-with-label {
  display: flex;
  align-items: center;
  gap: 8px;
}
```

For inline icons inside text, `vertical-align: -0.125em` (shifting slightly below baseline) often gives the best optical result.

### Optical Centering in Buttons
When an icon is inside a button with a label, the icon + label combination should feel optically centered — not mathematically centered. Sometimes this means adding 1–2px more padding on one side.

---

## Touch Target Padding

A 24px icon used as an interactive button is too small to tap comfortably. You need padding.

```
Icon size + padding = touch target

24px icon + 10px padding each side = 44px touch target ✅
16px icon + 14px padding each side = 44px touch target ✅
```

In CSS:
```css
.icon-button {
  width: 44px;
  height: 44px;
  display: flex;
  align-items: center;
  justify-content: center;
  /* The icon inside is 20–24px; padding provides the rest */
}
```

---

## Icon Meaning & Consistency

### Universal Icons (No label needed)
These are understood cross-culturally and don't need a visible label (but a tooltip is still good practice):
- ✕ or × — Close
- ☰ — Menu / hamburger
- ⌕ / 🔍 — Search
- ⬆ ⬇ ← → — Directional arrows
- + — Add
- ✓ — Confirm / checked

### Ambiguous Icons (Always need a label)
These mean different things in different contexts and should always have a visible label:
- ★ — Could mean favourite, rating, or featured
- 🔔 — Could mean notifications, alerts, or reminders
- ⚙ — Could mean settings, configuration, or preferences
- 📁 — Could mean files, projects, or categories
- 🏠 — Could mean home page, dashboard, or main menu

### The Meaning Consistency Rule
Once an icon has a meaning in your product, that meaning must be consistent everywhere.

❌ Bad: Using ★ for "favourite" on the home page and ★ for "rating" in the review section  
✅ Good: Using ★ for "favourite" everywhere, and a separate ⭐ filled style for ratings

---

## Icon + Label Patterns

### When to Show Labels
| Context | Label Required? |
|---|---|
| Primary navigation (desktop) | Recommended |
| Primary navigation (mobile bottom bar) | Required |
| Toolbar / action bar | Tooltip minimum, label preferred |
| Inline with text | No (context is enough) |
| Icon-only button | Tooltip required (`aria-label` always required) |
| Empty state illustrations | Yes — with heading + body text |

### Accessibility: aria-label
Every icon used as a button or interactive element MUST have an `aria-label` even if it has a visual label:

```html
<!-- Icon-only button -->
<button aria-label="Close dialog">
  <XIcon size={20} />
</button>

<!-- Icon + visible label (aria-label still recommended) -->
<button aria-label="Add new task">
  <PlusIcon size={16} />
  Add task
</button>
```

---

## Common Iconography Mistakes

| Mistake | Fix |
|---|---|
| Mixing outline and filled icons in same UI | Pick one style and stick to it |
| Using icons from 2+ different libraries | Pick one library |
| Scaling icons to non-grid sizes (18px, 22px) | Use 16, 20, 24, 32px |
| Using icon bounding box for alignment | Use optical/flex center alignment |
| No label on ambiguous icons | Add visible label or tooltip |
| No `aria-label` on icon buttons | Always add `aria-label` |
| Icon touch target too small (under 44px) | Add padding to reach 44×44px |
| Same icon, different meanings in same product | Pick one meaning per icon, use different icons for different meanings |
| Decreasing icon size on mobile | Icons need to be the same or larger on mobile for touch |
