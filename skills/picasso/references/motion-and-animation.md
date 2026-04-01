# Motion and Animation Reference

## Table of Contents
1. Principles
2. Easing Functions
3. Duration Guidelines
4. Staggered Reveals
5. Scroll-Triggered Animation
6. Text Morphing
7. Micro-Interactions
8. Reduced Motion
9. Common Mistakes

---

## 1. Principles

Motion serves three purposes: feedback (confirming an action), orientation (showing where something went), and delight (making the interface feel alive). If an animation does not serve one of these, remove it.

### Priority of Animation Investment
1. Page load choreography (highest impact, seen by everyone)
2. State transitions (tabs, modals, accordions)
3. Hover/focus states
4. Scroll-triggered reveals
5. Loading states and skeletons
6. Micro-interactions (button press effects, toggle animations)

Invest time in this order. A well-choreographed page load does more than fifty micro-interactions.

---

## 2. Easing Functions

### Use These
```css
/* Standard ease-out: elements arriving */
--ease-out: cubic-bezier(0.16, 1, 0.3, 1);

/* Standard ease-in: elements departing */
--ease-in: cubic-bezier(0.55, 0.085, 0.68, 0.53);

/* Standard ease-in-out: elements transforming in place */
--ease-in-out: cubic-bezier(0.65, 0, 0.35, 1);

/* Spring-like (subtle): natural deceleration */
--ease-spring: cubic-bezier(0.34, 1.56, 0.64, 1);
```

### Never Use
- `linear` for UI animations (looks mechanical)
- `ease` (the CSS default is mediocre)
- `bounce` / elastic easing with visible oscillation (looks dated and gimmicky). Subtle single-pass overshoot (like `--ease-spring` above) is acceptable.
- Spring animations with multiple bounces (too playful for most UIs)

---

## 3. Duration Guidelines

| Type | Duration | Why |
|---|---|---|
| Hover state change | 100-150ms | Must feel instant |
| Button press | 80-120ms | Tactile response |
| Tooltip appear | 150-200ms | Quick but not jarring |
| Fade in/out | 150-250ms | Smooth perception |
| Slide/expand | 200-350ms | Visible movement |
| Page transition | 300-500ms | Substantial change |
| Complex choreography | 400-800ms total | Entrance sequence |

Rule of thumb: if the user is waiting for it, it should be fast (under 200ms). If the user is watching it, it can be slower (200-500ms).

---

## 4. Staggered Reveals

The most impactful animation pattern. Elements enter one after another with increasing delay.

### CSS-Only Pattern
```css
.reveal-item {
  opacity: 0;
  transform: translateY(12px);
  animation: reveal 0.5s var(--ease-out) forwards;
}

@keyframes reveal {
  to {
    opacity: 1;
    transform: translateY(0);
  }
}

.reveal-item:nth-child(1) { animation-delay: 0ms; }
.reveal-item:nth-child(2) { animation-delay: 60ms; }
.reveal-item:nth-child(3) { animation-delay: 120ms; }
.reveal-item:nth-child(4) { animation-delay: 180ms; }
.reveal-item:nth-child(5) { animation-delay: 240ms; }
```

### Key Parameters
- **Stagger interval**: 40-80ms between items (shorter for many items, longer for few)
- **Translate distance**: 8-16px (subtle is better)
- **Do not stagger more than 6-8 items**. After that, group them.

### React with Motion Library
```jsx
import { motion } from "framer-motion";

const container = {
  hidden: {},
  show: { transition: { staggerChildren: 0.06 } }
};

const item = {
  hidden: { opacity: 0, y: 12 },
  show: { opacity: 1, y: 0, transition: { duration: 0.5, ease: [0.16, 1, 0.3, 1] } }
};
```

---

## 5. Scroll-Triggered Animation

### CSS-Only with Scroll-Driven Animations
```css
@keyframes fade-in {
  from { opacity: 0; transform: translateY(20px); }
  to { opacity: 1; transform: translateY(0); }
}

.scroll-reveal {
  animation: fade-in linear both;
  animation-timeline: view();
  animation-range: entry 0% entry 30%;
}
```

### Intersection Observer Pattern
```js
const observer = new IntersectionObserver(
  (entries) => {
    entries.forEach(entry => {
      if (entry.isIntersecting) {
        entry.target.classList.add('visible');
        observer.unobserve(entry.target);
      }
    });
  },
  { threshold: 0.15, rootMargin: '0px 0px -50px 0px' }
);

document.querySelectorAll('.animate-on-scroll').forEach(el => observer.observe(el));
```

---

## 6. Text Morphing

For animated text transitions (changing labels, counters, status updates), use **Torph** (dependency-free).

### Installation
```
npm i torph
```

### Usage
```jsx
import { TextMorph } from 'torph/react';

// Automatically animates between text values
<TextMorph>{status}</TextMorph>

// Works with any dynamic text
<button>
  <TextMorph>{isLoading ? "Processing..." : `Buy for $${price}`}</TextMorph>
</button>
```

Torph morphs individual characters with smooth enter/exit animations. It works with React, Vue, Svelte, and vanilla TypeScript.

### When to Use
- Tab labels that change on selection
- Button text that updates (Add to Cart -> Added!)
- Counter values that increment
- Status indicators that cycle through states
- Any text that changes in response to user action

---

## 7. Micro-Interactions

### Button Press
```css
button:active {
  transform: scale(0.97);
  transition: transform 80ms var(--ease-in);
}
```

### Toggle Switch
Animate the knob position and background color simultaneously. The knob should arrive slightly before the color finishes changing.

### Checkbox
Scale the checkmark from 0 to 1 with a slight overshoot:
```css
.checkbox-mark {
  transform: scale(0);
  transition: transform 200ms cubic-bezier(0.34, 1.56, 0.64, 1);
}
.checkbox:checked .checkbox-mark {
  transform: scale(1);
}
```

### Skeleton Loading
Shimmer from left to right using a gradient animation:
```css
.skeleton {
  background: linear-gradient(90deg,
    var(--surface-2) 25%,
    var(--surface-3) 50%,
    var(--surface-2) 75%
  );
  background-size: 200% 100%;
  animation: shimmer 1.5s infinite;
}
@keyframes shimmer {
  0% { background-position: 200% 0; }
  100% { background-position: -200% 0; }
}
```

---

## 8. Reduced Motion

Always respect the user's motion preference:
```css
@media (prefers-reduced-motion: reduce) {
  *, *::before, *::after {
    animation-duration: 0.01ms !important;
    animation-iteration-count: 1 !important;
    transition-duration: 0.01ms !important;
    scroll-behavior: auto !important;
  }
}
```

This does not mean removing all visual feedback. Opacity changes (fades) are still acceptable. Remove translation, scaling, and rotation animations.

---

## 9. Common Mistakes

- Animating everything on the page (creates visual noise, reduces perceived performance)
- Using `animation-duration: 0` for reduced motion (some browsers behave unexpectedly; use 0.01ms)
- Bounce/elastic easing on UI elements (acceptable only in game-like or toy-like contexts)
- Animating layout properties (width, height, top, left) instead of transforms (causes layout thrashing)
- Forgetting `will-change` on frequently animated elements (or overusing it on everything)
- Staggering 20+ items with visible delays (group them or animate the container)
- Using `transition: all 0.3s` (animates properties you did not intend; be explicit about which properties to transition)
