# Keyboard Navigation Patterns

**Why this exists:** Every presenter expects ← / → to advance slides, Space to advance, and Esc to exit presenter mode. These conventions are 20 years old. This document records what `md-slides` honors and why each binding is wired the way it is.

## The keymap

| Key | Action | Source |
|---|---|---|
| **→ / Space / PgDn** | Next slide | reveal.js, Big, Spectacle, Keynote, PowerPoint — universal |
| **← / PgUp** | Previous slide | universal |
| **Home** | First slide | reveal.js / Big convention |
| **End** | Last slide | reveal.js / Big convention |
| **P** | Toggle presenter mode | reveal.js convention |
| **Esc** | Exit presenter mode (if active) | universal accessibility expectation |
| **Ctrl/Cmd + P** | Print to PDF (browser-native) | browser default; we don't intercept |

We deliberately do NOT bind:
- **Number keys (1-9)** for slide jump — too easy to hit accidentally during typing
- **F11** for fullscreen — browser default; we don't override
- **Touch gestures** — out of scope; click-to-advance is sufficient for the click-to-advance case
- **Vim keys (h/j/k/l)** — niche; the arrow keys are the universal expectation

## Implementation discipline

```js
document.addEventListener("keydown", function (e) {
    if (e.metaKey || e.ctrlKey || e.altKey) return;  // Don't fight browser shortcuts
    switch (e.key) {
        case "ArrowRight":
        case "PageDown":
        case " ":
            e.preventDefault(); next(); break;
        // ...
    }
});
```

- **Modifier-aware**: we check `metaKey/ctrlKey/altKey` and bail. This means `Cmd+R` reloads (browser default), `Ctrl+P` prints (browser default), and we don't fight them.
- **`preventDefault()` on every match**: Space normally scrolls; we replace that with advance-slide.
- **`replaceState` for URL hash**: each slide change updates `#N` in the URL so deep links work + back button moves through slides naturally.

## URL hash deep linking

Every slide has `id="slide-N"`. The initial render reads `location.hash` and jumps to that slide on load. Sharing `deck.html#3` puts the reader directly on slide 3. Browser back/forward buttons walk slide history.

This works because we use `history.replaceState` (not `pushState`) for arrow-key navigation — otherwise every arrow click would push a new entry and back-button behavior would feel wrong.

## Accessibility

- **`@media (prefers-reduced-motion: reduce)`** — transitions and animations are suppressed when the user prefers reduced motion. The deck still works; it just doesn't animate.
- **Presenter panel uses `<aside aria-label="Presenter view (toggle with P)">`** — screen readers announce its purpose.
- **Slide counter is plain text** — `<span id="counter">1 / 5</span>` is announced by screen readers as the slide changes (we update the text content).
- **No focus traps** — keyboard users can Tab out of any interactive element naturally.
- **No JS-required content** — the slides are static `<section>` elements; JS just controls visibility. With JS off, the first slide renders correctly and the user can scroll through all of them.

## Sources

### 1. reveal.js — *Keyboard Bindings* (revealjs.com)
The convention-setter for web-based decks. Established: ← / → / Space / PgUp / PgDn / Home / End / Esc / F. We honor the subset our scope requires.

### 2. Tom MacWright — *Big* (github.com/tmcw/big)
Single-file deck tool. Validates the minimum viable keybinding set (arrow / space) and the URL-hash navigation pattern.

### 3. Spectacle (github.com/FormidableLabs/spectacle)
React-based deck framework. Same keymap conventions. Reinforces the arrow + space pairing.

### 4. WCAG 2.2 §2.1.1 *Keyboard* (w3.org/WAI/WCAG22)
All functionality must be operable through a keyboard interface. Our nav, presenter toggle, and Esc-to-exit all satisfy this.

### 5. WCAG 2.2 §2.4.3 *Focus Order* (w3.org/WAI/WCAG22)
Focus order must preserve meaning. We don't trap focus or jump focus across slide changes; default tab order applies.

### 6. NN/g — *Keyboard Accessibility* (Jakob Nielsen, 2024 update)
Best practices for keyboard-only navigation: don't fight modifier shortcuts, always provide a visible escape from modal states (P toggles back, Esc also works).

### 7. MDN — *KeyboardEvent.key* (developer.mozilla.org)
The standardized key value strings we match against ("ArrowRight" not "Right"; " " for space; "PageDown" not "PgDn"). Cross-browser-stable since 2018.

## Applied to `md-slides`

The JS payload in `deck_html_renderer.py` wires all of the above, in ~80 lines of vanilla JS, no framework. The presenter panel and progress bar update reactively as the user presses keys.
