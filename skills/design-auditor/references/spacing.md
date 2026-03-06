# Spacing & Layout Rules Reference

## The 8-Point Grid System

The most widely-used spacing system in professional UI design. Every spacing and sizing value should be a **multiple of 8**.

### The Scale
4, 8, 12, 16, 24, 32, 40, 48, 64, 80, 96, 128px

### Why 8?
- Screens are divisible by 8 (common screen widths: 320, 360, 375, 390, 414, 768, 1024, 1280, 1440...)
- 8px is small enough for fine-grained control, large enough to be meaningful
- Values always divide cleanly across pixel densities (1×, 2×, 3×)

### 4-Point Variant
Some teams use a 4-point base instead. This gives you: 4, 8, 12, 16, 20, 24, 32, 40, 48, 64...
Fine for dense/compact UIs. Still keep values as multiples of 4.

### What to Put on the Grid
- Spacing between components
- Padding inside components
- Component sizes (widths, heights)
- Icon sizes (16, 20, 24, 32, 40, 48px)

### Common Off-Grid Values (Red Flags)
- 3px, 5px, 7px, 9px, 11px, 13px, 17px, 22px, 27px...
If you see these, ask "why?" — they're usually accidental.

---

## Spacing Vocabulary

| Term | Meaning |
|---|---|
| **Padding** | Space *inside* a container (between content and its border) |
| **Margin** | Space *outside* a component (between it and adjacent things) |
| **Gap** | Space between items in a flex or grid container |
| **Gutter** | Space between columns in a grid layout |
| **Inset** | Uniform padding on all sides |

---

## Content Margins (Page-Level)

The space between the screen edge and the content:

| Screen Size | Common Margin |
|---|---|
| Mobile (< 768px) | 16px or 20px |
| Tablet (768–1024px) | 24px or 32px |
| Desktop (1024–1440px) | 48px, 64px, or 80px |
| Wide desktop (1440px+) | Content max-width + auto margins |

**Max Content Width**: Most readable body content caps at **680–800px wide**. Full-width containers can go to 1200–1440px for dashboards/data-heavy layouts.

---

## Component Padding

### Buttons

| Size | Vertical Padding | Horizontal Padding |
|---|---|---|
| Small | 6–8px | 12–16px |
| Medium (default) | 10–12px | 20–24px |
| Large | 14–16px | 28–32px |

**Touch target rule**: The entire button hit area should be at least **44×44px** (iOS) or **48×48dp** (Android/Material).

### Cards & Panels

| Size | Padding |
|---|---|
| Compact (dense dashboards) | 12–16px |
| Default | 16–24px |
| Spacious | 24–32px |

Padding should be consistent on all four sides, or use a pattern like more top/bottom than left/right intentionally.

### Form Inputs

- **Height**: 36–40px (small), 44–48px (default), 52–56px (large)
- **Horizontal padding**: 12–16px
- **Vertical padding**: enough to center text within the height above
- **Gap between fields**: 16–24px
- **Label-to-input gap**: 4–8px

---

## The Law of Proximity

**"Things that are related should be close together. Things that are unrelated should be far apart."**

This is the most important spacing rule to internalize:

✅ Good: A form label is 4–8px above its input. The next form field is 24px below.  
❌ Bad: Equal spacing between the label and its input, and the label and the previous field.

### Applying Proximity

- Section title → content below: **8–12px gap**
- Section → next section: **32–64px gap**
- Card title → card body: **8–12px**
- Unrelated elements: **32px+**

If two groups of content have the same amount of space between them as within them, add more space between the groups.

---

## Alignment

### Types of Alignment

| Type | When to Use |
|---|---|
| **Left edge** | Most common. Body text, list items, form fields |
| **Right edge** | Numbers in tables, secondary actions (right-side of nav) |
| **Center** | Short headlines, icons, button labels, hero content |
| **Baseline** | Text that sits next to each other in a line |

### Grid Alignment
Elements should align to a shared invisible grid. Things that aren't aligned to something look accidental.

**Check by drawing invisible lines**: Do your left edges line up? Do your top edges line up? If not, it should be intentional, not accidental.

---

## White Space

White space (negative space) is **not empty space** — it's an active design element.

### Why White Space Matters
- Makes content easier to scan
- Creates focus on what matters
- Communicates quality and confidence
- Reduces cognitive load

### Signs of Insufficient White Space
- Text runs edge-to-edge in containers
- Elements feel cramped or cluttered
- Nothing has visual breathing room
- Too many elements compete for attention

### Signs of Too Much White Space
- Content feels lost or disconnected
- Scroll depth becomes excessive for simple content
- Relationships between elements are unclear

**Rule of thumb**: When in doubt, add more space than you think you need.

---

## Layout Patterns

### The Column Grid

Most layouts use a **12-column grid** (desktop). This divides evenly into 1, 2, 3, 4, 6, and 12 columns.

Common desktop layouts:
- **Full width**: 12 columns
- **Wide content**: 10 columns, 1-column offset each side
- **Article**: 8 columns (centered)
- **Sidebar + Content**: 3 + 9 columns, or 4 + 8 columns

Mobile: Usually **1 column** (stacked), or **2 columns** for grids.

### Common Layout Patterns

| Pattern | Use Case |
|---|---|
| **Holy Grail** | Header + sidebar + content + sidebar + footer |
| **Card Grid** | Products, blog posts, gallery items |
| **Dashboard** | Stats + charts + tables |
| **Single Column** | Mobile, articles, forms |
| **Split / Two-Pane** | Settings, email clients, sidebars |

---

## Z-Index & Layering

When elements overlap, they need a clear layer hierarchy:

| Layer | Z-index Range | Examples |
|---|---|---|
| Base content | 0–9 | Page content, images |
| Floating elements | 10–99 | Sticky headers, floating buttons |
| Dropdowns / tooltips | 100–199 | Dropdown menus, tooltips |
| Modals / overlays | 200–299 | Modal dialogs, drawers |
| Notifications / toasts | 300–399 | Toast messages, alerts |
| Debug / dev tools | 9999+ | Dev tools, onboarding overlays |

**Don't use arbitrary z-index values** like 9999 for normal components. It creates escalation wars.

---

## Common Spacing Mistakes

1. **Inconsistent padding inside cards** — 12px on left, 16px on top. Pick one value and use it everywhere.
2. **Elements touching the edge** — Content with no margin from the screen or container edge.
3. **Equal spacing between unrelated items** — Everything looks like one undifferentiated blob.
4. **Random spacing values** — 13px, 22px, 7px. Use the 8-point grid.
5. **Overloaded screen density** — Too many things on screen at once. Consider splitting content across multiple screens or using progressive disclosure.
6. **Missing whitespace in forms** — Fields jammed together with no breathing room between sections.
7. **Ignoring mobile margins** — Desktop designs often use generous margins that collapse to nothing on mobile.

---

## When to Intentionally Break the 8-Point Grid

The 8-point grid is a rule, not a law. There are legitimate cases where breaking it is the right call — but they should always be **intentional and documented**, never accidental.

### Acceptable Reasons to Break the Grid

**1. Optical correction**
Sometimes mathematically correct spacing looks visually wrong. A common example: icons with built-in padding that makes them look off-center even when mathematically centered. Adjust by 1–2px to fix what the eye sees, not what the ruler says.

**2. Border compensation**
A 1px border adds to the total height/width of an element. If a button needs a 44px touch target and has a 1px border, the padding should be `(44 - 2) / 2 = 21px` — off-grid, but correct.

**3. Dense data UIs**
Tables, spreadsheets, and data grids sometimes need tighter vertical spacing (e.g. 6px or 10px row padding) to show more rows without scrolling. Acceptable when information density is the primary goal.

**4. Line-height alignment**
When aligning multi-line text with single-line text or icons, tiny spacing adjustments (1–3px) may be needed for optical baseline alignment.

**5. External constraints**
Third-party components, native platform guidelines (iOS HIG, Material Design), or specific browser rendering may impose constraints that conflict with your grid.

### How to Handle Intentional Breaks
- **Document it** — Add a comment in code: `/* 6px: optical correction for icon padding */`
- **Keep it local** — Don't make a "6px" token. The break is specific to this context.
- **Review it** — Off-grid values should be questioned in design reviews. If it doesn't have a reason, it's accidental.

### The Key Test
> "Can I explain why this value isn't on the grid?"

If yes → intentional, acceptable.  
If no → accidental, fix it.
