# Performance Reference

## The Golden Rule

**Only animate properties that the browser can handle on the GPU compositor thread:**

```
✅ SAFE (GPU composited):    transform, opacity, filter, clip-path, will-change
❌ AVOID (triggers layout):  width, height, top, left, right, bottom, margin, padding,
                              font-size, border-width, background-size (avoid)
```

Animating layout properties causes the browser to recalculate the entire page layout on every frame — this is called "layout thrash" and causes jank.

---

## requestAnimationFrame Pattern

Never put animation logic directly in event listeners. Always batch through rAF:

```javascript
let rafId = null;
let pendingScrollY = 0;

function onScroll() {
  pendingScrollY = window.scrollY;
  if (!rafId) {
    rafId = requestAnimationFrame(processScroll);
  }
}

function processScroll() {
  rafId = null;
  document.documentElement.style.setProperty('--scroll-y', pendingScrollY);
  // update other values...
}

window.addEventListener('scroll', onScroll, { passive: true });
// passive: true is CRITICAL — tells browser scroll handler won't preventDefault
// allows browser to scroll on a separate thread
```

---

## will-change Usage Rules

`will-change` promotes an element to its own GPU layer. Powerful but dangerous if overused.

```css
/* DO: Only apply when animation is about to start */
.element-about-to-animate {
  will-change: transform, opacity;
}

/* DO: Remove after animation completes */
element.addEventListener('animationend', () => {
  element.style.willChange = 'auto';
});

/* DON'T: Apply globally */
* { will-change: transform; } /* WRONG — massive GPU memory usage */

/* DON'T: Apply statically on all animated elements */
.animated-thing { will-change: transform; } /* Wrong if there are many of these */
```

### GSAP handles this automatically
GSAP applies `will-change` during animations and removes it after. If using GSAP, you generally don't need to manage `will-change` yourself.

---

## IntersectionObserver Pattern

Never animate all elements all the time. Only animate what's currently visible.

```javascript
class AnimationManager {
  constructor() {
    this.activeAnimations = new Set();
    this.observer = new IntersectionObserver(
      this.handleIntersection.bind(this),
      { threshold: 0.1, rootMargin: '50px 0px' }
    );
  }

  observe(el) {
    this.observer.observe(el);
  }

  handleIntersection(entries) {
    entries.forEach(entry => {
      if (entry.isIntersecting) {
        this.activateElement(entry.target);
      } else {
        this.deactivateElement(entry.target);
      }
    });
  }

  activateElement(el) {
    // Start GSAP animation / add floating class
    el.classList.add('animate-active');
    this.activeAnimations.add(el);
  }

  deactivateElement(el) {
    // Pause or stop animation
    el.classList.remove('animate-active');
    this.activeAnimations.delete(el);
  }
}

const animManager = new AnimationManager();
document.querySelectorAll('.animated-layer').forEach(el => animManager.observe(el));
```

---

## content-visibility: auto

For pages with many off-screen sections, this dramatically improves initial load and scroll performance:

```css
/* Apply to every major section except the first (which is immediately visible) */
.scene:not(:first-child) {
  content-visibility: auto;
  /* Tells browser: don't render this until it's near the viewport */
  contain-intrinsic-size: 0 100vh;
  /* Gives browser an estimated height so scrollbar is correct */
}
```

**Note:** Don't apply to the first section — it causes a flash of invisible content.

---

## Asset Optimization Rules

### PNG File Size Targets (Maximum)

| Depth Level | Element Type         | Max File Size | Max Dimensions |
|-------------|---------------------|---------------|----------------|
| Depth 0     | Background          | 150KB         | 1920×1080      |
| Depth 1     | Glow layer          | 60KB          | 1000×1000      |
| Depth 2     | Decorations         | 50KB          | 400×400        |
| Depth 3     | Main product/hero   | 120KB         | 1200×1200      |
| Depth 4     | UI components       | 40KB          | 800×800        |
| Depth 5     | Particles           | 10KB          | 128×128        |

**Total page weight target: Under 2MB for all assets combined.**

### Image Loading Strategy

```html
<!-- Hero image: preload immediately -->
<link rel="preload" as="image" href="hero-product.png">

<!-- Above-fold images: eager loading -->
<img src="hero-bg.png" loading="eager" fetchpriority="high" alt="">

<!-- Below-fold images: lazy loading -->
<img src="section-2-bg.png" loading="lazy" alt="">

<!-- Use srcset for responsive images -->
<img 
  src="product-800.png"
  srcset="product-400.png 400w, product-800.png 800w, product-1200.png 1200w"
  sizes="(max-width: 768px) 100vw, 50vw"
  alt="Product description"
  loading="eager"
>
```

---

## Mobile Performance

Touch devices have less GPU power. Always detect and reduce effects:

```javascript
const isTouchDevice = window.matchMedia('(pointer: coarse)').matches;
const prefersReduced = window.matchMedia('(prefers-reduced-motion: reduce)').matches;
const isLowPower = navigator.hardwareConcurrency <= 4; // heuristic for low-end devices

const performanceMode = (isTouchDevice || prefersReduced || isLowPower) ? 'lite' : 'full';

function initForPerformanceMode() {
  if (performanceMode === 'lite') {
    // Disable: mouse tracking, floating loops, particles, perspective zoom
    document.documentElement.classList.add('perf-lite');
    // Keep: basic scroll fade-ins, curtain reveals (CSS only)
  } else {
    // Full experience
    initParallaxLayers();
    initFloatingLoops();
    initParticles();
    initMouseTracking();
  }
}
```

```css
/* Disable GPU-heavy effects in lite mode */
.perf-lite .depth-0,
.perf-lite .depth-1,
.perf-lite .depth-5 {
  transform: none !important;
  will-change: auto !important;
}
.perf-lite .float-loop {
  animation: none !important;
}
.perf-lite .glow-blob {
  display: none;
}
```

---

## Chrome DevTools Performance Checklist

Before shipping, verify:

1. **Layers panel**: Check `chrome://settings` → DevTools → "Show Composited Layer Borders" — should not show excessive layer count (target: under 20 promoted layers)
2. **Performance tab**: Record scroll at 60fps. Look for long frames (>16ms)
3. **Memory tab**: Heap snapshot — should not grow during scroll (no leaks)
4. **Coverage tab**: Check unused CSS/JS — strip unused animation classes

---

## GSAP Performance Tips

```javascript
// BAD: Creates new tween every scroll event
window.addEventListener('scroll', () => {
  gsap.to(element, { y: window.scrollY * 0.5 }); // creates new tween each frame!
});

// GOOD: Use scrub — GSAP manages timing internally
gsap.to(element, {
  y: 200,
  ease: 'none',
  scrollTrigger: {
    scrub: true, // GSAP handles this efficiently
  }
});

// GOOD: Kill ScrollTriggers when not needed
const trigger = ScrollTrigger.create({ ... });
// Later:
trigger.kill();

// GOOD: Use gsap.set() for instant placement (no tween overhead)
gsap.set('.element', { x: 0, opacity: 1 });

// GOOD: Batch DOM reads/writes
gsap.utils.toArray('.elements').forEach(el => {
  // GSAP batches these reads automatically
  gsap.from(el, { ... });
});
```
