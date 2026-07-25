# WCAG Accessibility Floor

**Why this exists:** Every converter renders text on backgrounds, links on backgrounds, and accent UI on backgrounds. WCAG 2.2 sets minimum contrast ratios that, if violated, make the document unreadable for users with low vision. This skill enforces those ratios as hard refusals during onboarding — not as warnings — because no user expects an onboarding wizard to ship them an inaccessible default.

## The floor

WCAG 2.2 AA Level (Section 1.4.3):

| Foreground / Background | Minimum contrast |
|---|---|
| Body text (< 18pt regular or < 14pt bold) | **4.5 : 1** |
| Large text (≥ 18pt regular or ≥ 14pt bold) | 3 : 1 |
| Non-text UI (focus rings, button borders, icons) | 3 : 1 |
| Links (treated as body text) | **4.5 : 1** |

`brand_palette_validator.py` enforces all four during onboarding. Failures on body-text or link contrast → refuse (exit code 4). Failures on non-text UI → warn but proceed (the user might be using accent for a backdrop that doesn't carry semantic meaning).

## Sources

### 1. WCAG 2.2 — *Understanding Success Criterion 1.4.3: Contrast (Minimum)* (w3.org/WAI/WCAG22)
The text and the formula. We implement `relative_luminance()` per the spec's sRGB-linearization rule and `contrast_ratio()` per `(L1 + 0.05) / (L2 + 0.05)`. No deviation.

### 2. WCAG 2.2 — *Understanding Success Criterion 1.4.11: Non-text Contrast* (w3.org/WAI/WCAG22)
Establishes the 3:1 floor for UI components. Used for `wcag-accent-on-bg` check.

### 3. WCAG 2.2 — *Understanding Success Criterion 1.4.4: Resize Text* (w3.org/WAI/WCAG22)
Mandates that text can be resized to 200% without loss of content. The converters use `rem` units for type scale (driven by `typography.scale_ratio`) so browser zoom respects user preference.

### 4. WebAIM — *Contrast Checker* (webaim.org/resources/contrastchecker)
The de-facto reference implementation. Cross-checked against our `contrast_ratio()` — identical results to 2 decimal places.

### 5. Sara Soueidan — *Color Tokens for Accessible Color Systems* (sarasoueidan.com, 2022)
Articulates the iterative-contrast-walk strategy: when a brand color fails on the link role, lighten or darken until it passes, then snap. The `_ensure_link_contrast()` helper is the direct implementation.

### 6. Léonie Watson — *Accessibility is a Process* (talks across 2018-2024)
Reinforces that contrast is the lowest-cost-highest-impact accessibility win. Most other a11y improvements take design effort; contrast can be enforced algorithmically.

### 7. CSS `prefers-color-scheme` (MDN)
The browser primitive for dark/light mode detection. `code_theme: "auto"` in the design-system config maps to a CSS media query, so syntax-highlighting follows OS preference automatically without forcing a re-onboard.

## What this skill does NOT enforce

- **WCAG 2.2 AAA (7:1)** — out of scope. AA is the realistic floor for design systems shipping to broad audiences; AAA is reserved for medical/legal/government content.
- **Focus order, ARIA, keyboard nav** — out of scope here (the converters handle these in their own renderers). md-review enforces `aria-label` on severity badges, md-slides enforces keyboard nav per WCAG 2.1.1, md-document enforces `aria-current="location"` on TOC scrollspy.
- **Reduced motion** — out of scope here. Converters emit `@media (prefers-reduced-motion: reduce) { * { animation: none; } }` independently.
- **Screen-reader semantic correctness** — out of scope. Beyond ensuring `<h1>...<h6>` hierarchy is preserved and `<table>` has `<thead>`, deeper SR audit needs a tool like pa11y / axe-core.

## Why hard refusal, not warning

A warning that ships an inaccessible default is the worst outcome of an onboarding wizard. The user trusted the wizard to set them up right. WCAG AA on body text is the one thing we can verify deterministically — so we do.

If the user genuinely wants to override (rare: a brand-mandated low-contrast scheme for a graphic design portfolio, say), they can:
1. Set `MARKDOWN_HTML_NO_CONFIG=1` and run with built-in defaults
2. Manually edit `~/.config/markdown-html/design-system.json` (the saved file)
3. Add a `<style>` override block in the converted HTML directly

These are all explicit, deliberate acts. The wizard's job is to ship an accessible default; the user can break that contract knowingly.
