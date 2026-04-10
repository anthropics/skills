# Color Rules Reference

## The Basics: Palette Structure

Every good UI color palette has these roles:

| Role | Purpose | Count |
|---|---|---|
| **Primary** | Main brand color, primary actions (buttons, links) | 1 color + shades |
| **Secondary / Accent** | Highlights, secondary CTAs, decorative | 1 color |
| **Neutral** | Backgrounds, text, borders, surfaces | 1 grayscale ramp (5–9 shades) |
| **Semantic: Success** | Confirmations, completed states | 1 green |
| **Semantic: Warning** | Caution states | 1 yellow/orange |
| **Semantic: Error** | Errors, destructive actions | 1 red |
| **Semantic: Info** | Informational alerts | 1 blue |

**Total**: Usually 3–5 distinct hues, with shades of each.

### The Palette Size Problem
- **Too few colors**: Flat, boring, hard to create hierarchy
- **Too many colors**: Chaotic, inconsistent, unprofessional
- **Sweet spot**: 2–3 brand colors + neutral ramp + semantic colors

---

## WCAG Contrast Ratios

This is the most important thing to check. Failing contrast = failing accessibility.

### Minimum Requirements (WCAG AA)

| Situation | Minimum Contrast |
|---|---|
| Normal body text (< 18px or < 14px bold) | **4.5:1** |
| Large text (≥ 18px or ≥ 14px bold) | **3:1** |
| UI Components (buttons, inputs, icons) | **3:1** |
| Decorative/disabled elements | None required |

### Enhanced Requirements (WCAG AAA — aspirational)
- Normal text: 7:1
- Large text: 4.5:1

### How Contrast Ratio Works
- White on white = 1:1 (invisible)
- Black on white = 21:1 (maximum)
- The higher the number, the more readable

### Common Contrast Failures
| Combo | Approximate Ratio | Status |
|---|---|---|
| #999 gray on white | ~2.8:1 | ❌ Fails AA |
| #767676 on white | 4.54:1 | ✅ Barely passes AA |
| #555 on white | ~7:1 | ✅ Passes AAA |
| Light blue on white | Often fails | ❌ Check carefully |
| Yellow on white | ~1.07:1 | ❌ Completely invisible |
| White on mid-blue (#4A90E2) | ~3.3:1 | ❌ Fails for small text |
| White on dark blue (#1E5BB5) | ~6.2:1 | ✅ Passes |

**Check tool**: https://webaim.org/resources/contrastchecker/ or Figma's built-in accessibility panel.

---

## Color Meaning & Semantics

### Universal Associations
- **Red** → Error, danger, delete, stop
- **Green** → Success, confirmed, proceed, positive
- **Yellow/Orange** → Warning, caution, pending
- **Blue** → Information, links, interactive, trust
- **Gray** → Disabled, secondary, neutral

**Rule**: Be consistent. If blue means "clickable" on one screen, it must mean "clickable" everywhere. Never use blue for decorative non-interactive elements.

### The Color-Only Problem
**Never rely on color alone** to communicate meaning. Approximately 8% of men have color blindness.

❌ Bad: A red border on an error input (with no other indicator)  
✅ Good: A red border + ⚠ icon + error message text

❌ Bad: A green dot = online, red dot = offline (for colorblind users, they look the same)  
✅ Good: Green dot labeled "Online" + Red dot labeled "Offline"

---

## Color Harmony

### Monochromatic
One hue, many shades. Safe, cohesive, professional.
Example: Light blue background, medium blue accent, dark blue text.

### Complementary
Two colors opposite on the color wheel. High contrast, energetic.
Example: Blue + Orange, Purple + Yellow, Red + Teal.
**Caution**: Can feel aggressive if both are saturated. Usually tone one down.

### Analogous
Colors adjacent on the wheel. Harmonious, natural.
Example: Blue + Teal + Purple.

### Triadic
Three colors equally spaced on the wheel. Vibrant but tricky.
Example: Red + Blue + Yellow. Usually keep one dominant, others as accents.

---

## Color in Dark Mode

Dark mode ≠ just inverting colors. Rules change:

- **Don't use pure black** (#000000) backgrounds — it creates harsh contrast. Use dark grays (#121212, #1A1A1A, #0F172A).
- **Don't use pure white** (#FFFFFF) text on dark — slightly off-white (#E0E0E0, #F1F1F1) reduces eye strain.
- **Reduce saturation** of brand colors slightly — very saturated colors on dark feel garish.
- **Elevation uses lighter shades** (not shadows) — higher cards use slightly lighter dark gray.
- **Semantic colors shift**: Greens and reds often need to be desaturated or their lighter variants to maintain contrast on dark backgrounds.

---

## Common Color Mistakes

1. **Purple gradient on white** — The most clichéd "AI-generated" aesthetic. Avoid.
2. **Too many accent colors** — Pick one accent, use it consistently.
3. **Saturated background colors** — Very saturated colored backgrounds (not neutrals) make text hard to read and cause eye fatigue.
4. **Inconsistent primary color usage** — If your primary is blue, don't put random blue decorative shapes that aren't interactive.
5. **Low-contrast placeholders** — Placeholder text is often styled #999 or lighter. Check the contrast.
6. **Brand color for body text** — Usually looks odd and reduces readability. Use it for headings and interactive elements, not long-form text.
7. **White text on bright colors** — White on bright yellow, cyan, or light green almost always fails contrast.

---

## The 60-30-10 Rule

A classic color proportion rule for balanced UI design:

| Role | % of UI | What to Use |
|---|---|---|
| **60% — Dominant** | Background, large surfaces, whitespace | Neutral (white, light gray, dark gray) |
| **30% — Secondary** | Cards, sidebars, nav, secondary elements | Slightly different neutral or soft brand tone |
| **10% — Accent** | Buttons, links, highlights, CTAs | Primary brand color |

### Why It Works
- The 60% keeps the UI calm and readable
- The 30% creates depth and separation
- The 10% draws attention exactly where you want it — interactive elements

### Common Violations
- **Too much accent** (30%+): UI feels loud, overwhelming — everything is competing for attention
- **Accent used decoratively**: Brand color on non-interactive elements trains users to ignore it
- **No clear dominant neutral**: Multiple competing background colors create visual chaos

### Example Application
```
60%: #F9FAFB (off-white page background)
30%: #FFFFFF (white cards) + #E5E7EB (subtle borders)
10%: #7C3AED (purple CTAs, active nav, links)
```

### Dark Mode Version
```
60%: #0F172A (dark navy background)
30%: #1E293B (slightly lighter cards/panels)
10%: #818CF8 (lighter purple — adjusted for dark bg contrast)
```

The accent color almost always needs adjusting for dark mode — the light-mode version is often too dark to pass contrast on dark backgrounds.

---

## Quick Reference: Accessible Dark Text on Colored Backgrounds

These text colors have been checked against common background colors:

| Background | Min text color for 4.5:1 | Notes |
|---|---|---|
| White #FFFFFF | #767676 | Medium gray threshold |
| Light gray #F5F5F5 | #727272 | Slightly darker |
| Light blue #E3F2FD | #5C6F7A | Teal-gray |
| Brand blue #4A90E2 | White works, but check | ~4.0:1 — borderline for small text |
| Dark blue #1E3A5F | White #FFFFFF | Clearly passes |

**When in doubt, use a contrast checker tool.** Don't eyeball it.
