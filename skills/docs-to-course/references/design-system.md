# Design System Reference

Complete CSS design tokens for the course. Copy this entire `:root` block into the course HTML and adapt the accent color to suit the project's personality.

## Table of Contents
1. [Accessibility (WCAG 2.1 AA)](#accessibility-wcag-21-aa)
2. [Color Palette](#color-palette)
3. [Typography](#typography)
4. [Spacing & Layout](#spacing--layout)
5. [Shadows & Depth](#shadows--depth)
6. [Animations & Transitions](#animations--transitions)
7. [Navigation & Progress](#navigation--progress)
8. [Module Structure](#module-structure)
9. [Responsive Breakpoints](#responsive-breakpoints)
10. [Scrollbar & Background](#scrollbar--background)

---

## Accessibility (WCAG 2.1 AA)

All courses must meet WCAG 2.1 AA. Apply these rules before writing any interactive element.

### Contrast ratios (non-negotiable)

The default token values meet AA. If you change any color token, verify it still passes:

| Context | Required ratio | Token pairs that meet it |
|---|---|---|
| Body text (< 18px) | 4.5 : 1 | `--color-text` on `--color-bg` = ~12:1 ✓ |
| Large text (≥ 18px or bold ≥ 14px) | 3 : 1 | `--color-accent` on `--color-bg` = ~4.5:1 ✓ |
| UI components & states | 3 : 1 | Focus ring, button borders |

**Check tool:** use the browser DevTools accessibility panel or [contrast-ratio.com](https://contrast-ratio.com) on any custom color.

**Never use color as the only signal.** Always pair color with a text label, icon, or pattern. Quiz correct/incorrect states use color + checkmark/✕ icon + text feedback. Error states use `--color-error` + `aria-invalid` + visible message.

### Focus states

Never write `outline: none` without a replacement. The default browser outline is ugly but functional — if you override it, replace it with something equally visible:

```css
:focus-visible {
  outline: 2px solid var(--color-accent);
  outline-offset: 3px;
  border-radius: 2px;
}
/* Remove for mouse users only — preserve for keyboard */
:focus:not(:focus-visible) {
  outline: none;
}
```

Apply `:focus-visible` to all interactive elements: buttons, links, quiz options, drag chips, tooltip terms, nav dots.

### Keyboard operability

Every interactive element must be fully operable with keyboard alone:

| Element | Required keyboard behavior |
|---|---|
| Quiz options | Tab to focus, Space/Enter to select |
| Drag-and-drop | Tab to chip, Space to pick up, Arrow keys to move, Space/Enter to drop; fallback click-to-select |
| Tooltips | Focusable terms, Enter/Space to show, Escape to dismiss |
| Chat/flow animations | Buttons for next/play/reset; all focusable |
| Decision tree | All choice buttons focusable and activatable with Enter |
| Nav dots | Tab between dots, Enter to navigate |
| Scroll | Arrow keys (up/down) navigate modules |

### ARIA requirements

```html
<!-- Progress bar -->
<div class="progress-bar" role="progressbar"
     aria-valuenow="0" aria-valuemin="0" aria-valuemax="100"
     aria-label="Course progress"></div>

<!-- Quiz group -->
<div class="quiz-container" role="group" aria-labelledby="quiz-heading">

<!-- Quiz radio options -->
<button class="quiz-option" role="radio" aria-checked="false"
        aria-describedby="q1-feedback">

<!-- Interactive diagram -->
<div class="arch-diagram" role="region" aria-label="System architecture diagram">

<!-- Decision tree -->
<div class="decision-tree" role="region" aria-label="[Descriptive name] decision tree">

<!-- Live feedback regions -->
<div class="quiz-feedback" aria-live="polite">
<div class="check-feedback" aria-live="polite">
<div class="sm-info" aria-live="polite">

<!-- Diagram descriptions (when SVG/canvas not feasible) -->
<div class="flow-animation" role="img"
     aria-label="Step-by-step diagram showing [describe the flow]">
```

### Alt text for all visual-only content

Every diagram, animation, and flow visualization that conveys information visually must have a text alternative:

```html
<!-- Option 1: aria-label on the container -->
<div class="arch-diagram" role="img"
     aria-label="Architecture diagram showing three components: Client, Resolver, and Authoritative Server. Client queries Resolver; Resolver either serves from cache or queries Authoritative Server; Authoritative Server returns the authoritative answer.">

<!-- Option 2: visually-hidden description -->
<div class="flow-animation">
  <!-- ...visual content... -->
  <p class="visually-hidden">
    This animation shows five steps: (1) Client sends query to resolver...
  </p>
</div>
```

```css
.visually-hidden {
  position: absolute;
  width: 1px; height: 1px;
  margin: -1px; padding: 0;
  overflow: hidden;
  clip: rect(0, 0, 0, 0);
  white-space: nowrap;
  border: 0;
}
```

### Drag-and-drop keyboard fallback

The HTML5 drag API does not work reliably on keyboard or mobile assistive technology. All drag-and-drop elements must have a click-based fallback:

```javascript
// Click-to-select, click-to-place fallback
let selectedChip = null;

chips.forEach(chip => {
  chip.addEventListener('click', () => {
    if (selectedChip === chip) {
      // Deselect
      chip.classList.remove('selected');
      chip.setAttribute('aria-pressed', 'false');
      selectedChip = null;
    } else {
      // Select this chip
      chips.forEach(c => { c.classList.remove('selected'); c.setAttribute('aria-pressed', 'false'); });
      chip.classList.add('selected');
      chip.setAttribute('aria-pressed', 'true');
      selectedChip = chip;
    }
  });
});

zones.forEach(zone => {
  zone.addEventListener('click', () => {
    if (!selectedChip) return;
    const target = zone.querySelector('.dnd-zone-target');
    target.textContent = selectedChip.textContent;
    target.dataset.placed = selectedChip.dataset.answer;
    selectedChip.classList.add('placed');
    selectedChip.setAttribute('aria-pressed', 'false');
    selectedChip = null;
  });
});
```

### Reduced motion

Respect the user's motion preference. All animations should degrade gracefully:

```css
@media (prefers-reduced-motion: reduce) {
  *,
  *::before,
  *::after {
    animation-duration: 0.01ms !important;
    animation-iteration-count: 1 !important;
    transition-duration: 0.01ms !important;
    scroll-behavior: auto !important;
  }
  .animate-in {
    opacity: 1 !important;
    transform: none !important;
  }
}
```

---

## Color Palette

```css
:root {
  /* --- BACKGROUNDS --- */
  --color-bg:             #FAF7F2;       /* warm off-white, like aged paper */
  --color-bg-warm:        #F5F0E8;       /* slightly warmer for alternating modules */
  --color-bg-code:        #1E1E2E;       /* deep indigo-charcoal for code blocks */
  --color-text:           #2C2A28;       /* dark charcoal, easy on eyes */
  --color-text-secondary: #6B6560;       /* warm gray for secondary text */
  --color-text-muted:     #9E9790;       /* muted for timestamps, labels */
  --color-border:         #E5DFD6;       /* subtle warm border */
  --color-border-light:   #EEEBE5;       /* even lighter border */
  --color-surface:        #FFFFFF;       /* card surfaces */
  --color-surface-warm:   #FDF9F3;       /* warm card surface */

  /* --- ACCENT (adapt per project — pick ONE bold color) ---
     Default: vermillion. Alternatives: coral (#E06B56), teal (#2A7B9B),
     amber (#D4A843), forest (#2D8B55). Avoid purple gradients. */
  --color-accent:         #D94F30;
  --color-accent-hover:   #C4432A;
  --color-accent-light:   #FDEEE9;
  --color-accent-muted:   #E8836C;

  /* --- SEMANTIC --- */
  --color-success:        #2D8B55;
  --color-success-light:  #E8F5EE;
  --color-error:          #C93B3B;
  --color-error-light:    #FDE8E8;
  --color-info:           #2A7B9B;
  --color-info-light:     #E4F2F7;

  /* --- ACTOR COLORS (assign to main components) ---
     Each major "character" in the codebase gets a distinct color
     for chat bubbles, diagrams, and highlights */
  --color-actor-1:        #D94F30;       /* vermillion */
  --color-actor-2:        #2A7B9B;       /* teal */
  --color-actor-3:        #7B6DAA;       /* muted plum */
  --color-actor-4:        #D4A843;       /* golden */
  --color-actor-5:        #2D8B55;       /* forest */
}
```

**Rules:**
- Even-numbered modules use `--color-bg`, odd-numbered use `--color-bg-warm` (alternating backgrounds create visual rhythm)
- Actor colors should be visually distinct from each other and from the accent
- Code blocks always use `--color-bg-code` with light text

---

## Typography

```css
:root {
  /* --- FONTS ---
     Display: bold, geometric, personality-driven. NOT Inter/Roboto/Arial.
     Body: readable with character. NOT system fonts.
     Mono: developer-friendly with clear character distinction. */
  --font-display:  'Bricolage Grotesque', Georgia, serif;
  --font-body:     'DM Sans', -apple-system, sans-serif;
  --font-mono:     'JetBrains Mono', 'Fira Code', 'Consolas', monospace;

  /* --- TYPE SCALE (1.25 ratio) --- */
  --text-xs:   0.75rem;    /* 12px — labels, badges */
  --text-sm:   0.875rem;   /* 14px — secondary text, code */
  --text-base: 1rem;       /* 16px — body text */
  --text-lg:   1.125rem;   /* 18px — lead paragraphs */
  --text-xl:   1.25rem;    /* 20px — screen headings */
  --text-2xl:  1.5rem;     /* 24px — sub-module titles */
  --text-3xl:  1.875rem;   /* 30px — module subtitles */
  --text-4xl:  2.25rem;    /* 36px — module titles */
  --text-5xl:  3rem;       /* 48px — hero text */
  --text-6xl:  3.75rem;    /* 60px — module numbers */

  /* --- LINE HEIGHTS --- */
  --leading-tight:  1.15;  /* headings */
  --leading-snug:   1.3;   /* subheadings */
  --leading-normal: 1.6;   /* body text */
  --leading-loose:  1.8;   /* relaxed reading */
}
```

**Google Fonts link (put in `<head>`):**
```html
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Bricolage+Grotesque:opsz,wght@12..96,400;12..96,600;12..96,700;12..96,800&family=DM+Sans:ital,opsz,wght@0,9..40,300;0,9..40,400;0,9..40,500;0,9..40,600;0,9..40,700;1,9..40,400;1,9..40,500&family=JetBrains+Mono:wght@400;500;600&display=swap" rel="stylesheet">
```

**Rules:**
- Module numbers: `--text-6xl`, font-display, weight 800, `--color-accent` with 15% opacity
- Module titles: `--text-4xl`, font-display, weight 700
- Screen headings: `--text-xl` or `--text-2xl`, font-display, weight 600
- Body text: `--text-base` or `--text-lg`, font-body, `--leading-normal`
- Code: `--text-sm`, font-mono
- Labels/badges: `--text-xs`, font-mono, uppercase, letter-spacing 0.05em

---

## Spacing & Layout

```css
:root {
  --space-1:  0.25rem;   /* 4px */
  --space-2:  0.5rem;    /* 8px */
  --space-3:  0.75rem;   /* 12px */
  --space-4:  1rem;      /* 16px */
  --space-5:  1.25rem;   /* 20px */
  --space-6:  1.5rem;    /* 24px */
  --space-8:  2rem;      /* 32px */
  --space-10: 2.5rem;    /* 40px */
  --space-12: 3rem;      /* 48px */
  --space-16: 4rem;      /* 64px */
  --space-20: 5rem;      /* 80px */
  --space-24: 6rem;      /* 96px */

  --content-width:     800px;   /* standard reading width */
  --content-width-wide: 1000px; /* for side-by-side layouts */
  --nav-height:        50px;
  --radius-sm:  8px;
  --radius-md:  12px;
  --radius-lg:  16px;
  --radius-full: 9999px;
}
```

**Module layout:**
```css
.module {
  min-height: 100dvh;       /* fallback: 100vh */
  scroll-snap-align: start;
  padding: var(--space-16) var(--space-6);
  padding-top: calc(var(--nav-height) + var(--space-12));
}
.module-content {
  max-width: var(--content-width);
  margin: 0 auto;
}
```

---

## Shadows & Depth

```css
:root {
  --shadow-sm:  0 1px 2px rgba(44, 42, 40, 0.05);
  --shadow-md:  0 4px 12px rgba(44, 42, 40, 0.08);
  --shadow-lg:  0 8px 24px rgba(44, 42, 40, 0.1);
  --shadow-xl:  0 16px 48px rgba(44, 42, 40, 0.12);
}
```

Use warm-tinted RGBA (44, 42, 40) — never pure black shadows.

---

## Animations & Transitions

```css
:root {
  --ease-out:    cubic-bezier(0.16, 1, 0.3, 1);
  --ease-in-out: cubic-bezier(0.65, 0, 0.35, 1);
  --duration-fast:   150ms;
  --duration-normal: 300ms;
  --duration-slow:   500ms;
  --stagger-delay:   120ms;
}
```

**Scroll-triggered reveal pattern:**
```css
.animate-in {
  opacity: 0;
  transform: translateY(20px);
  transition: opacity var(--duration-slow) var(--ease-out),
              transform var(--duration-slow) var(--ease-out);
}
.animate-in.visible {
  opacity: 1;
  transform: translateY(0);
}

/* Stagger children */
.stagger-children > .animate-in {
  transition-delay: calc(var(--stagger-index, 0) * var(--stagger-delay));
}
```

**JS setup for stagger:**
```javascript
document.querySelectorAll('.stagger-children').forEach(parent => {
  Array.from(parent.children).forEach((child, i) => {
    child.style.setProperty('--stagger-index', i);
  });
});
```

**Intersection Observer (trigger reveals):**
```javascript
const observer = new IntersectionObserver((entries) => {
  entries.forEach(entry => {
    if (entry.isIntersecting) {
      entry.target.classList.add('visible');
      observer.unobserve(entry.target); // animate only once
    }
  });
}, { rootMargin: '0px 0px -10% 0px', threshold: 0.1 });

document.querySelectorAll('.animate-in').forEach(el => observer.observe(el));
```

---

## Navigation & Progress

**HTML structure:**
```html
<nav class="nav">
  <div class="progress-bar" role="progressbar" aria-valuenow="0"></div>
  <div class="nav-inner">
    <span class="nav-title">Course Title</span>
    <div class="nav-dots">
      <button class="nav-dot" data-target="module-1" data-tooltip="Module 1 Name"
              role="tab" aria-label="Module 1"></button>
      <!-- one per module -->
    </div>
  </div>
</nav>
```

**Progress bar (CSS-only where possible, JS fallback):**
```javascript
function updateProgressBar() {
  const scrollTop = window.scrollY;
  const scrollHeight = document.documentElement.scrollHeight - window.innerHeight;
  const progress = (scrollTop / scrollHeight) * 100;
  progressBar.style.width = progress + '%';
}
window.addEventListener('scroll', () => {
  requestAnimationFrame(updateProgressBar);
}, { passive: true });
```

**Nav dot states:**
- Default: `border: 2px solid var(--color-text-muted)`, empty center
- Current: `border-color: var(--color-accent)`, filled center, subtle glow shadow
- Visited: `background: var(--color-accent)`, filled solid

**Keyboard navigation:**
```javascript
document.addEventListener('keydown', (e) => {
  if (['INPUT', 'TEXTAREA'].includes(e.target.tagName)) return;
  if (e.key === 'ArrowDown' || e.key === 'ArrowRight') { nextModule(); e.preventDefault(); }
  if (e.key === 'ArrowUp' || e.key === 'ArrowLeft') { prevModule(); e.preventDefault(); }
});
```

---

## Module Structure

**HTML template for each module:**
```html
<section class="module" id="module-N" style="background: var(--color-bg or --color-bg-warm)">
  <div class="module-content">
    <header class="module-header animate-in">
      <span class="module-number">0N</span>
      <h1 class="module-title">Module Title</h1>
      <p class="module-subtitle">One-line description of what this module teaches</p>
    </header>

    <div class="module-body">
      <section class="screen animate-in">
        <h2 class="screen-heading">Screen Title</h2>
        <p>Content...</p>
        <!-- Interactive elements, code translations, etc. -->
      </section>

      <section class="screen animate-in">
        <!-- Next screen -->
      </section>
    </div>
  </div>
</section>
```

---

## Responsive Breakpoints

```css
/* Tablet */
@media (max-width: 768px) {
  :root {
    --text-4xl: 1.875rem;
    --text-5xl: 2.25rem;
    --text-6xl: 3rem;
  }
  .translation-block { grid-template-columns: 1fr; } /* stack code/english */
  .pattern-cards { grid-template-columns: 1fr 1fr; }
}

/* Mobile */
@media (max-width: 480px) {
  :root {
    --text-4xl: 1.5rem;
    --text-5xl: 1.875rem;
    --text-6xl: 2.25rem;
  }
  .module { padding: var(--space-8) var(--space-4); }
  .pattern-cards { grid-template-columns: 1fr; }
  .flow-steps { flex-direction: column; }
  .flow-arrow { transform: rotate(90deg); }
}
```

---

## Scrollbar & Background

```css
/* Custom scrollbar */
::-webkit-scrollbar { width: 6px; }
::-webkit-scrollbar-track { background: transparent; }
::-webkit-scrollbar-thumb {
  background: var(--color-border);
  border-radius: var(--radius-full);
}

/* Subtle atmospheric background */
body {
  background: var(--color-bg);
  background-image: radial-gradient(
    ellipse at 20% 50%,
    rgba(217, 79, 48, 0.03) 0%,
    transparent 50%
  );
}

/* Page scroll setup */
html {
  scroll-snap-type: y proximity;
  scroll-behavior: smooth;
}
```

---

## Code Block Globals

All code blocks in the course — whether inside translation blocks, standalone snippets, or quiz challenges — must wrap text and never show a horizontal scrollbar. This is a teaching tool, not an IDE.

```css
pre, code {
  white-space: pre-wrap;       /* wrap long lines */
  word-break: break-word;      /* break mid-word if absolutely needed */
  overflow-x: hidden;          /* no horizontal scrollbar — ever */
}
/* Hide scrollbars on code containers */
.translation-code::-webkit-scrollbar,
pre::-webkit-scrollbar {
  display: none;
}
```

Code snippets must be **exact copies** from the real codebase — never modified, trimmed, or simplified. Instead, choose naturally short (5-10 line) sections from the code that illustrate the concept well. If a longer block is needed, show it all — the wrapping CSS will handle readability.

---

## Syntax Highlighting (Catppuccin-inspired)

For code blocks on the dark `--color-bg-code` background:

```css
.code-keyword  { color: #CBA6F7; }  /* purple — if, else, return, function */
.code-string   { color: #A6E3A1; }  /* green — "strings" */
.code-function { color: #89B4FA; }  /* blue — function names */
.code-comment  { color: #6C7086; }  /* muted gray — // comments */
.code-number   { color: #FAB387; }  /* peach — numbers */
.code-property { color: #F9E2AF; }  /* yellow — object keys */
.code-operator { color: #94E2D5; }  /* teal — =, =>, +, etc. */
.code-tag      { color: #F38BA8; }  /* pink — HTML tags */
.code-attr     { color: #F9E2AF; }  /* yellow — HTML attributes */
.code-value    { color: #A6E3A1; }  /* green — attribute values */
```

---

## Brand Skin Layer (optional)

When a course is generated with corporate branding (see SKILL.md Phase 2C), a thin override layer adjusts the accent and adds a logo. The layer is opt-in and skin-only — it does not replace the design system.

### Skinnable tokens

| Token | Override source | Notes |
|---|---|---|
| `--color-accent` | Brand primary hex | Must pass 3:1 contrast on `#FAF7F2` |
| `--color-accent-hover` | Derived: brand primary, ~10% darker | Auto-computed |
| `--color-accent-light` | Derived: brand primary mixed ~10% with `--color-bg` | Auto-computed |
| `--color-accent-muted` | Derived: brand primary at reduced saturation | Auto-computed |
| Body radial-gradient tint | Derived: brand primary at ~3% alpha | Replaces the default vermillion tint in [Scrollbar & Background](#scrollbar--background) |
| `--color-actor-1..5` | Brand secondary colors | Wholesale replacement if 5 provided; otherwise mix with defaults |

### Tokens that are NOT skinnable

- All `--color-bg*` (warm off-white is structural to the aesthetic)
- All `--font-*` (typography is the skill's identity)
- All `--space-*`, `--radius-*`, `--shadow-*`
- Semantic colors (`--color-success`, `--color-error`, `--color-info`) — functional, not branding
- Dark code background (`--color-bg-code`) and syntax highlighting

### `.brand.json` schema

```json
{
  "name": "Acme Corp",
  "primary": "#1A4FBA",
  "logo": "./assets/logo.svg",
  "secondary": ["#FF6B35", "#2D8B55", "#7B6DAA", "#D4A843"],
  "tagline": "Engineering Excellence"
}
```

All fields except `name` and `primary` are optional. Place `.brand.json` in the working directory and the skill auto-detects it on the next run.

### Override pattern

The generated HTML emits two `:root` blocks in `<style>`. The default block (from this file) stays unchanged; the override block appears immediately after and contains only the brand-driven tokens. CSS cascade resolves the conflict to the brand values:

```css
:root {
  /* default tokens — copied verbatim from this file */
  --color-accent: #D94F30;
  /* ...etc */
}

:root {
  /* brand skin overrides — emitted only when a brand spec is supplied */
  --color-accent:        #1A4FBA;
  --color-accent-hover:  /* ~10% darker */;
  --color-accent-light:  /* mixed with --color-bg */;
  --color-accent-muted:  /* reduced saturation */;
}

body {
  background-image: radial-gradient(
    ellipse at 20% 50%,
    rgba(26, 79, 186, 0.03) 0%,  /* derived from brand primary */
    transparent 50%
  );
}
```

### Logo embedding

The course HTML must remain self-contained. Logos are inlined:

- **SVG** — paste markup directly into the nav; strip external `<image>`, `<use href>`, or web-font references
- **PNG/JPG** — base64 data URI
- **URL** — fetched once at build time, embedded as a data URI

Render at 24–32px height in the nav (nav-height is 50px). Logo only appears in the nav — never in module headers, synthesis cards, or elsewhere.

### Contrast validation

Before applying the override, compute the contrast ratio of the brand primary against `#FAF7F2`:

| Ratio | Use |
|---|---|
| ≥ 4.5:1 | Any use, including body text accents |
| 3:1 – 4.5:1 | Large text only (module numbers, titles) |
| < 3:1 | Fails WCAG AA — ask the user for a darker brand variant; do not silently mutate |
