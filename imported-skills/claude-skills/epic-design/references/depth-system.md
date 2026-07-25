# Depth System Reference

The 2.5D illusion is built entirely on a **6-level depth model**. Every element on the page belongs to exactly one depth level. Depth controls four automatic properties: parallax speed, blur, scale, and shadow intensity. Together these four signals trick the human visual system into perceiving genuine spatial depth from flat assets.

---

## The 6-Level Depth Table

| Level | Name              | Parallax | Blur  | Scale | Shadow  | Z-Index |
|-------|-------------------|----------|-------|-------|---------|---------|
| 0     | Far Background    | 0.10x    | 8px   | 0.70  | 0.05    | 0       |
| 1     | Glow / Atmosphere | 0.25x    | 4px   | 0.85  | 0.10    | 1       |
| 2     | Mid Decorations   | 0.50x    | 0px   | 1.00  | 0.20    | 2       |
| 3     | Main Objects      | 0.80x    | 0px   | 1.05  | 0.35    | 3       |
| 4     | UI / Text         | 1.00x    | 0px   | 1.00  | 0.00    | 4       |
| 5     | Foreground FX     | 1.20x    | 0px   | 1.10  | 0.50    | 5       |

**Parallax formula:**
```
element_translateY = scroll_position * depth_factor * -1
```
A depth-0 element at scroll position 500px moves only -50px (barely moves — feels far away).
A depth-5 element at 500px moves -600px (moves fast — feels close).

---

## CSS Implementation

### CSS Custom Properties Foundation
```css
:root {
  /* Depth parallax factors */
  --depth-0-factor: 0.10;
  --depth-1-factor: 0.25;
  --depth-2-factor: 0.50;
  --depth-3-factor: 0.80;
  --depth-4-factor: 1.00;
  --depth-5-factor: 1.20;

  /* Depth blur values */
  --depth-0-blur: 8px;
  --depth-1-blur: 4px;
  --depth-2-blur: 0px;
  --depth-3-blur: 0px;
  --depth-4-blur: 0px;
  --depth-5-blur: 0px;

  /* Depth scale values */
  --depth-0-scale: 0.70;
  --depth-1-scale: 0.85;
  --depth-2-scale: 1.00;
  --depth-3-scale: 1.05;
  --depth-4-scale: 1.00;
  --depth-5-scale: 1.10;

  /* Live scroll value (updated by JS) */
  --scroll-y: 0;
}

/* Base layer class */
.layer {
  position: absolute;
  inset: 0;
  will-change: transform;
  transform-origin: center center;
}

/* Depth-specific classes */
.depth-0 {
  filter: blur(var(--depth-0-blur));
  transform: scale(var(--depth-0-scale))
             translateY(calc(var(--scroll-y) * var(--depth-0-factor) * -1px));
  z-index: 0;
}
.depth-1 {
  filter: blur(var(--depth-1-blur));
  transform: scale(var(--depth-1-scale))
             translateY(calc(var(--scroll-y) * var(--depth-1-factor) * -1px));
  z-index: 1;
  mix-blend-mode: screen; /* glow layers blend additively */
}
.depth-2 {
  transform: scale(var(--depth-2-scale))
             translateY(calc(var(--scroll-y) * var(--depth-2-factor) * -1px));
  z-index: 2;
}
.depth-3 {
  transform: scale(var(--depth-3-scale))
             translateY(calc(var(--scroll-y) * var(--depth-3-factor) * -1px));
  z-index: 3;
  filter: drop-shadow(0 20px 40px rgba(0,0,0,0.35));
}
.depth-4 {
  transform: translateY(calc(var(--scroll-y) * var(--depth-4-factor) * -1px));
  z-index: 4;
}
.depth-5 {
  transform: scale(var(--depth-5-scale))
             translateY(calc(var(--scroll-y) * var(--depth-5-factor) * -1px));
  z-index: 5;
}
```

### JavaScript — Scroll Driver
```javascript
// Throttled scroll listener using requestAnimationFrame
let ticking = false;
let lastScrollY = 0;

function updateDepthLayers() {
  const scrollY = window.scrollY;
  document.documentElement.style.setProperty('--scroll-y', scrollY);
  ticking = false;
}

window.addEventListener('scroll', () => {
  lastScrollY = window.scrollY;
  if (!ticking) {
    requestAnimationFrame(updateDepthLayers);
    ticking = true;
  }
}, { passive: true });
```

---

## Asset Assignment Rules

### What Goes in Each Depth Level

**Depth 0 — Far Background**
- Full-width background images (sky, gradient, texture)
- Very large PNGs (1920×1080+), file size 80–150KB max
- Heavily blurred by CSS — low detail is fine and preferred
- Examples: skyscape, abstract color wash, noise texture

**Depth 1 — Glow / Atmosphere**
- Radial gradient blobs, lens flare PNGs, soft light overlays
- Size: 600–1000px, file size: 30–60KB max
- Always use `mix-blend-mode: screen` or `mix-blend-mode: lighten`
- Always `filter: blur(40px–100px)` applied on top of CSS blur
- Examples: orange glow blob behind product, atmospheric haze

**Depth 2 — Mid Decorations**
- Abstract shapes, geometric patterns, floating decorative elements
- Size: 200–400px, file size: 20–50KB max
- Moderate shadow, no blur
- Examples: floating geometric shapes, brand pattern elements

**Depth 3 — Main Objects (The Star)**
- Hero product images, characters, featured illustrations
- Size: 800–1200px, file size: 50–120KB max
- High detail, clean cutout (transparent PNG background)
- Strong drop shadow: `filter: drop-shadow(0 30px 60px rgba(0,0,0,0.4))`
- This is the element users look at — give it the most visual weight
- Examples: juice bottle, product shot, hero character

**Depth 4 — UI / Text**
- Headlines, body copy, buttons, cards, navigation
- Always crisp, never blurred
- Text elements get animation data attributes (see text-animations.md)
- Examples: `<h1>`, `<p>`, `<button>`, card components

**Depth 5 — Foreground Particles / FX**
- Sparkles, floating dots, light particles, decorative splashes
- Small (32–128px), file size: 2–10KB
- High contrast, sharp edges
- Multiple instances scattered with different animation delays
- Examples: star sparkles, liquid splash dots, highlight flares

---

## Compositional Hierarchy — Size Relationships Between Assets

The most common mistake in 2.5D design is treating all assets as the same size.
Real cinematic depth requires deliberate, intentional size contrast.

### The Rule of One Hero

Every scene has exactly ONE dominant asset. Everything else serves it.

| Role | Display Size | Depth |
|---|---|---|
| Hero / star element | 50–85vw | depth-3 |
| Primary companion | 8–15vw | depth-2 |
| Secondary companion | 5–10vw | depth-2 |
| Accent / particle | 1–4vw | depth-5 |
| Background fill | 100vw | depth-0 |

### Positioning Companions Close to the Hero

Never scatter companions in random corners. Position them relative to the hero's edge:

```css
/*
  Hero width: clamp(600px, 70vw, 1000px)
  Hero half-width: clamp(300px, 35vw, 500px)
*/
.companion-right {
  position: absolute;
  right: calc(50% - clamp(300px, 35vw, 500px) - 20px);
  /* negative gap value = slightly overlaps the hero */
}
.companion-left {
  position: absolute;
  left: calc(50% - clamp(300px, 35vw, 500px) - 20px);
}
```

Vertical placement:
- Upper shoulder: `top: 35%; transform: translateY(-50%)`
- Mid waist: `top: 55%; transform: translateY(-50%)`
- Lower base: `top: 72%; transform: translateY(-50%)`

### Scatter Rule on Hero Scroll-Out

When the hero grows or exits, companions scatter outward — not just fade.
This reinforces they were "held in orbit" by the hero.

```javascript
heroScrollTimeline
  .to('.companion-right', { x: 80,  y: -50, scale: 1.3  }, scrollPos)
  .to('.companion-left',  { x: -70, y:  40, scale: 1.25 }, scrollPos)
  .to('.companion-lower', { x:  30, y:  80, scale: 1.1  }, scrollPos)
```

### Pre-Build Size Checklist

Before assigning sizes, answer these for every asset:
1. Is this the hero? → make it large enough to command the viewport
2. Is this a companion? → it should be 15–25% of the hero's display size
3. Would this read better bigger or smaller than my first instinct?
4. Is there enough size contrast between depth layers to read as real depth?
5. Does the composition feel balanced, or does everything look the same size?

---

## Floating Loop Animation

Every element at depth 2–5 should have a floating animation. Nothing should be perfectly static — it kills the 3D illusion.

```css
/* Float variants — apply different ones to different elements */
@keyframes float-y {
  0%, 100% { transform: translateY(0px); }
  50%       { transform: translateY(-18px); }
}
@keyframes float-rotate {
  0%, 100% { transform: translateY(0px) rotate(0deg); }
  33%       { transform: translateY(-12px) rotate(2deg); }
  66%       { transform: translateY(-6px) rotate(-1deg); }
}
@keyframes float-breathe {
  0%, 100% { transform: scale(1); }
  50%       { transform: scale(1.04); }
}
@keyframes float-orbit {
  0%   { transform: translate(0, 0) rotate(0deg); }
  25%  { transform: translate(8px, -12px) rotate(2deg); }
  50%  { transform: translate(0, -20px) rotate(0deg); }
  75%  { transform: translate(-8px, -12px) rotate(-2deg); }
  100% { transform: translate(0, 0) rotate(0deg); }
}

/* Depth-appropriate durations */
.depth-2 .float-loop { animation: float-y 10s ease-in-out infinite; }
.depth-3 .float-loop { animation: float-orbit 8s ease-in-out infinite; }
.depth-5 .float-loop { animation: float-rotate 6s ease-in-out infinite; }

/* Stagger delays for multiple elements at same depth */
.float-loop:nth-child(2) { animation-delay: -2s; }
.float-loop:nth-child(3) { animation-delay: -4s; }
.float-loop:nth-child(4) { animation-delay: -1.5s; }
```

---

## Shadow Depth Enhancement

Stronger shadows on closer elements amplify depth perception:

```css
/* Depth shadow system */
.depth-2 img { filter: drop-shadow(0 10px 20px rgba(0,0,0,0.20)); }
.depth-3 img { filter: drop-shadow(0 25px 50px rgba(0,0,0,0.35)); }
.depth-5 img { filter: drop-shadow(0 5px 15px rgba(0,0,0,0.50)); }
```

## Glow Layer Pattern (Depth 1)

The glow layer is critical for the "product floating in light" premium feel:

```css
/* Glow blob behind the main product */
.glow-blob {
  position: absolute;
  width: 600px;
  height: 600px;
  border-radius: 50%;
  background: radial-gradient(circle, var(--brand-color) 0%, transparent 70%);
  filter: blur(80px);
  opacity: 0.45;
  mix-blend-mode: screen;
  /* Position behind depth-3 product */
  z-index: 1;
  /* Slow drift */
  animation: float-breathe 12s ease-in-out infinite;
}
```

---

## HTML Scaffold Template

```html
<section class="scene" data-scene="[name]">
  <div class="scene-inner">

    <!-- DEPTH 0: Far background -->
    <div class="layer depth-0" aria-hidden="true">
      <div class="bg-gradient"></div>
      <!-- OR: <img src="bg-texture.png" alt=""> -->
    </div>

    <!-- DEPTH 1: Glow atmosphere -->
    <div class="layer depth-1" aria-hidden="true">
      <div class="glow-blob glow-primary"></div>
      <div class="glow-blob glow-secondary"></div>
    </div>

    <!-- DEPTH 2: Mid decorations -->
    <div class="layer depth-2" aria-hidden="true">
      <img class="deco float-loop" src="shape-1.png" alt="">
      <img class="deco float-loop" src="shape-2.png" alt="">
    </div>

    <!-- DEPTH 3: Main product/hero -->
    <div class="layer depth-3">
      <img class="product-hero float-loop" src="product.png"
           alt="[Meaningful description of product]" />
    </div>

    <!-- DEPTH 4: Text & UI -->
    <div class="layer depth-4">
      <h1 class="hero-title split-text" data-animate="converge">
        Your Headline
      </h1>
      <p class="hero-sub" data-animate="fade-up">Supporting copy here</p>
      <a class="cta-btn" href="#" data-animate="scale-in">Get Started</a>
    </div>

    <!-- DEPTH 5: Foreground particles -->
    <div class="layer depth-5" aria-hidden="true">
      <img class="particle float-loop" src="sparkle.png" alt="">
      <img class="particle float-loop" src="sparkle.png" alt="">
      <img class="particle float-loop" src="sparkle.png" alt="">
    </div>

  </div>
</section>
```
