# Accessibility Reference

## Table of Contents
1. Semantic HTML
2. ARIA Patterns
3. Keyboard Navigation
4. Screen Reader Testing
5. Color and Contrast
6. Motion and Vestibular
7. Forms
8. Images and Media
9. Testing Tools
10. Common Mistakes

---

## 1. Semantic HTML

Use the correct HTML element for its purpose. A `<button>` is always better than a `<div onClick>`. Semantic elements provide free behavior: focus, activation, role announcement, and keyboard interaction.

### Landmark Regions
Every page needs landmarks (`<header>`, `<nav>`, `<main>`, `<aside>`, `<footer>`). Screen readers let users jump between them. Label multiples: `<nav aria-label="Primary">`.

### Document Outline
Heading levels (`h1`-`h6`) in order. Never skip levels. One `h1` per page.

### Element Selection
- Action: `<button>`. Navigation: `<a href>`. Lists: `<ul>`/`<ol>`. Data: `<table>` with `<th>`.
- Toggle: `<button aria-pressed>` or `<input type="checkbox">`. Expandable: `<details>`/`<summary>`.

---

## 2. ARIA Patterns

Do not use ARIA if native HTML achieves the same result. ARIA adds semantics but not behavior.

### Common Widgets
**Tabs**: `role="tablist"` container with `role="tab"` buttons. Arrow keys move between tabs, Tab moves into `role="tabpanel"`. Manage `aria-selected` and `hidden`.

**Dialog**: `role="dialog"` with `aria-modal="true"` and `aria-labelledby` pointing to the heading. Trap focus, close on Escape.

### Live Regions
Inject content into these containers; do not add the role after content exists.
```html
<div aria-live="polite" aria-atomic="true">3 items in cart</div>
<div role="alert">Payment failed.</div>   <!-- assertive, interrupts -->
<div role="status">File uploaded.</div>    <!-- polite, waits -->
```

---

## 3. Keyboard Navigation

### Focus Indicators
Never remove outlines without replacement. Use `:focus-visible` for keyboard-only rings:
```css
:focus-visible { outline: 2px solid var(--accent); outline-offset: 2px; }
```

### Tab Order
DOM order determines tab order. Never use positive `tabindex`. Use `tabindex="-1"` for programmatic focus only.

### Roving Tabindex
For composite widgets (toolbars, tab lists), one item is in the tab order at a time. Arrow keys move focus. Set `tabindex="0"` on the active item, `tabindex="-1"` on siblings, and call `.focus()` on arrow key press.

### Focus Trapping for Modals
On open: focus first focusable element. Tab/Shift+Tab cycles within. Escape closes. On close: return focus to trigger. Use `inert` on background content to prevent interaction outside the modal.

---

## 4. Screen Reader Testing

### VoiceOver (macOS)
Toggle: Cmd+F5. Navigate: VO (Ctrl+Option) + arrows. Rotor: VO+U. Test with Safari.

### NVDA (Windows)
Toggle: Ctrl+Alt+N. Elements list: NVDA+F7. Read all: NVDA+Down. Test with Firefox.

### Methodology
1. Navigate with SR only. Verify elements announce role, name, state.
2. Verify dynamic changes (toasts, errors) are announced via live regions.
3. Verify modals trap focus and announce title. Verify custom widget keyboard patterns.

### Gotchas
- `aria-hidden="true"` on a parent hides all children regardless of child attributes.
- Dynamic content is not announced unless in a live region or focus is moved to it.

---

## 5. Color and Contrast

### WCAG 2.2 Requirements
Normal text: 4.5:1 AA, 7:1 AAA. Large text (>=24px / >=18.66px bold): 3:1 AA, 4.5:1 AAA. UI components and focus indicators: 3:1 AA. APCA provides a more perceptually accurate model and is expected in WCAG 3.0.

### Color Blindness
8% of men have color vision deficiency. Never rely on color alone. Pair red/green with icons. Use patterns in charts alongside color. See `color-and-contrast.md` for deeper guidance.

---

## 6. Motion and Vestibular

### prefers-reduced-motion
Remove translation, rotation, and scaling. Opacity fades remain acceptable.
```css
@media (prefers-reduced-motion: reduce) {
  *, *::before, *::after {
    animation-duration: 0.01ms !important;
    transition-duration: 0.01ms !important;
    scroll-behavior: auto !important;
  }
}
```

### prefers-contrast
For `(prefers-contrast: more)`: bolder borders (2px+), higher text contrast, remove translucent/glass surfaces.

### What to Avoid
- Flashing faster than 3/second (WCAG 2.3.1), auto-playing large animations
- Parallax without reduced-motion fallback, infinite animations without pause

---

## 7. Forms

Every input needs a programmatic `<label>`. Placeholders are not labels. Mark required fields with `required` and `aria-required="true"`.

For errors, use `aria-invalid="true"` and `aria-describedby` pointing to the error message:
```html
<input id="email" aria-invalid="true" aria-describedby="email-err" />
<p id="email-err" role="alert">Enter a valid email address.</p>
```
Validate on blur, not on keystroke. For multiple errors, move focus to an error summary with links to each invalid field.

---

## 8. Images and Media

### Alt Text
- **Informative**: Describe content and purpose. **Decorative**: `alt=""` (empty, not absent).
- **Functional** (in buttons/links): Describe the action, not the image. **Complex**: Short alt + `aria-describedby` or `<figcaption>`.

### Video and Audio
Captions for all video (WCAG 1.2.2). Audio descriptions for visual-only content (WCAG 1.2.5). Never auto-play audio. Media players must be keyboard-operable.

---

## 9. Testing Tools

### Automated
- **axe-core**: Industry standard. Browser extension, CLI, or CI via `@axe-core/playwright`. Catches ~30-40% of issues.
- **Lighthouse**: Chrome DevTools, uses axe-core. **pa11y**: CLI for CI, supports WCAG 2.2 AA/AAA.

### Manual Checklist
1. Tab through entire page. Logical order, every control reachable.
2. Activate controls with Enter and Space.
3. Modals: focus trapped, Escape closes, focus returns.
4. 400% zoom: no horizontal scroll (WCAG 1.4.10).
5. Screen reader: correct roles, names, and states.
6. Images have appropriate alt text. Forms have labels and announced errors.

---

## 10. Common Mistakes

- `<div>`/`<span>` for clickable elements instead of `<button>`/`<a>` (loses keyboard and semantics)
- `outline: none` without a visible replacement focus indicator
- Positive `tabindex` values (chaotic tab ordering)
- `aria-hidden="true"` on focusable elements (reachable but invisible to AT)
- `role="button"` on a `<div>` without `tabindex="0"` and Enter/Space handlers
- Missing `lang` attribute on `<html>` (screen readers guess language wrong)
- `aria-live` on a region updating every second (overwhelms SR users)
- Wrapping entire cards in `<a>` (SR reads all card text as the link name)
