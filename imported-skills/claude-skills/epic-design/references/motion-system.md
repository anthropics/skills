# Motion System Reference

## Table of Contents
1. [GSAP Setup & CDN](#gsap-setup)
2. [Pattern 1: Multi-Layer Parallax](#pattern-1)
3. [Pattern 2: Pinned Sticky Sections](#pattern-2)
4. [Pattern 3: Cascading Card Stack](#pattern-3)
5. [Pattern 4: Scrub Timeline](#pattern-4)
6. [Pattern 5: Clip-Path Wipe Reveals](#pattern-5)
7. [Pattern 6: Horizontal Scroll Conversion](#pattern-6)
8. [Pattern 7: Perspective Zoom Fly-Through](#pattern-7)
9. [Pattern 8: Snap-to-Section](#pattern-8)
10. [Lenis Smooth Scroll](#lenis)
11. [IntersectionObserver Activation](#intersection-observer)

---

## GSAP Setup & CDN {#gsap-setup}

Always load from jsDelivr CDN:

```html
<!-- Core GSAP -->
<script src="https://cdn.jsdelivr.net/npm/gsap@3.12.5/dist/gsap.min.js"></script>
<!-- ScrollTrigger plugin — required for all scroll patterns -->
<script src="https://cdn.jsdelivr.net/npm/gsap@3.12.5/dist/ScrollTrigger.min.js"></script>
<!-- ScrollSmoother — optional, pairs with ScrollTrigger -->
<script src="https://cdn.jsdelivr.net/npm/gsap@3.12.5/dist/ScrollSmoother.min.js"></script>
<!-- Flip plugin — for cross-section element morphing -->
<script src="https://cdn.jsdelivr.net/npm/gsap@3.12.5/dist/Flip.min.js"></script>
<!-- MotionPathPlugin — for curved element paths -->
<script src="https://cdn.jsdelivr.net/npm/gsap@3.12.5/dist/MotionPathPlugin.min.js"></script>

<script>
  // Always register plugins immediately
  gsap.registerPlugin(ScrollTrigger, Flip, MotionPathPlugin);

  // Respect prefers-reduced-motion
  const prefersReduced = window.matchMedia('(prefers-reduced-motion: reduce)').matches;
  if (prefersReduced) {
    gsap.globalTimeline.timeScale(0); // Freeze all animations
  }
</script>
```

---

## Pattern 1: Multi-Layer Parallax {#pattern-1}

The foundation of all 2.5D depth. Different layers scroll at different speeds.

```javascript
function initParallax() {
  const layers = document.querySelectorAll('[data-depth]');

  const depthFactors = {
    '0': 0.10, '1': 0.25, '2': 0.50,
    '3': 0.80, '4': 1.00, '5': 1.20
  };

  layers.forEach(layer => {
    const depth = layer.dataset.depth;
    const factor = depthFactors[depth] || 1.0;

    gsap.to(layer, {
      yPercent: -15 * factor,  // adjust multiplier for desired effect intensity
      ease: 'none',
      scrollTrigger: {
        trigger: layer.closest('.scene'),
        start: 'top bottom',
        end: 'bottom top',
        scrub: true, // 1:1 scroll-to-animation
      }
    });
  });
}
```

**When to use:** Every project. This is always on.

---

## Pattern 2: Pinned Sticky Sections {#pattern-2}

A section stays fixed while its content animates. Other sections slide over/under it. The "window over window" effect.

```javascript
function initPinnedSection(sceneEl) {
  // The section stays pinned for `duration` scroll pixels
  // while inner content animates on a scrubbed timeline
  const tl = gsap.timeline({
    scrollTrigger: {
      trigger: sceneEl,
      start: 'top top',
      end: '+=150%',        // stay pinned for 1.5x viewport of scroll
      pin: true,            // THIS is what pins the section
      scrub: 1,             // 1 second smoothing
      anticipatePin: 1,     // prevents jump on pin
    }
  });

  // Inner content animations while pinned
  // These play out over the scroll distance
  tl.from('.pinned-title', { opacity: 0, y: 60, duration: 0.3 })
    .from('.pinned-image', { scale: 0.8, opacity: 0, duration: 0.4 })
    .to('.pinned-bg', { backgroundColor: '#1a0a2e', duration: 0.3 })
    .from('.pinned-sub', { opacity: 0, x: -40, duration: 0.3 });

  return tl;
}
```

**Visual result:** Section feels like a chapter — the page "lives inside it" for a while, then moves on.

---

## Pattern 3: Cascading Card Stack {#pattern-3}

New sections slide over previous ones. Each buried section scales down and darkens, feeling like it's receding.

```css
/* CSS Setup */
.card-stack-section {
  position: sticky;
  top: 0;
  height: 100vh;
  /* Each subsequent section has higher z-index */
}
.card-stack-section:nth-child(1) { z-index: 1; }
.card-stack-section:nth-child(2) { z-index: 2; }
.card-stack-section:nth-child(3) { z-index: 3; }
.card-stack-section:nth-child(4) { z-index: 4; }
```

```javascript
function initCardStack() {
  const cards = gsap.utils.toArray('.card-stack-section');

  cards.forEach((card, i) => {
    // Each card (except last) gets buried as next one enters
    if (i < cards.length - 1) {
      gsap.to(card, {
        scale: 0.88,
        filter: 'brightness(0.5) blur(3px)',
        borderRadius: '20px',
        ease: 'none',
        scrollTrigger: {
          trigger: cards[i + 1],  // fires when NEXT card enters
          start: 'top bottom',
          end: 'top top',
          scrub: true,
        }
      });
    }
  });
}
```

---

## Pattern 4: Scrub Timeline {#pattern-4}

The most powerful pattern. Elements transform EXACTLY in sync with scroll position. One pixel of scroll = one frame of animation.

```javascript
function initScrubTimeline(sceneEl) {
  const tl = gsap.timeline({
    scrollTrigger: {
      trigger: sceneEl,
      start: 'top top',
      end: '+=200%',
      pin: true,
      scrub: 1.5,  // 1.5s lag for smooth, dreamy feel (use 0 for precise 1:1)
    }
  });

  // Sequences play out as user scrolls
  // 0.0 to 0.25 → first 25% of scroll
  tl.fromTo('.hero-product',
    { scale: 0.6, opacity: 0, y: 100 },
    { scale: 1, opacity: 1, y: 0, duration: 0.25 }
  )
  // 0.25 to 0.5 → second quarter
  .to('.hero-title span:first-child', {
    x: '-30vw', opacity: 0, duration: 0.25
  }, 0.25)
  .to('.hero-title span:last-child', {
    x: '30vw', opacity: 0, duration: 0.25
  }, 0.25)
  // 0.5 to 0.75 → third quarter
  .to('.hero-product', {
    scale: 1.3, y: -50, duration: 0.25
  }, 0.5)
  .fromTo('.next-section-content',
    { opacity: 0, y: 80 },
    { opacity: 1, y: 0, duration: 0.25 },
    0.5
  )
  // 0.75 to 1.0 → final quarter
  .to('.hero-product', {
    opacity: 0, scale: 1.6, duration: 0.25
  }, 0.75);

  return tl;
}
```

---

## Pattern 5: Clip-Path Wipe Reveals {#pattern-5}

Content is hidden behind a clip-path mask that animates away to reveal the content beneath. GPU-accelerated, buttery smooth.

```javascript
// Left-to-right horizontal wipe
function initHorizontalWipe(el) {
  gsap.fromTo(el,
    { clipPath: 'inset(0 100% 0 0)' },
    {
      clipPath: 'inset(0 0% 0 0)',
      duration: 1.2,
      ease: 'power3.out',
      scrollTrigger: { trigger: el, start: 'top 80%' }
    }
  );
}

// Top-to-bottom drop reveal
function initTopDropReveal(el) {
  gsap.fromTo(el,
    { clipPath: 'inset(0 0 100% 0)' },
    {
      clipPath: 'inset(0 0 0% 0)',
      duration: 1.0,
      ease: 'power2.out',
      scrollTrigger: { trigger: el, start: 'top 75%' }
    }
  );
}

// Circle iris expand
function initCircleIris(el) {
  gsap.fromTo(el,
    { clipPath: 'circle(0% at 50% 50%)' },
    {
      clipPath: 'circle(75% at 50% 50%)',
      duration: 1.4,
      ease: 'power2.inOut',
      scrollTrigger: { trigger: el, start: 'top 60%' }
    }
  );
}

// Window pane iris (tiny box expands to full)
function initWindowPaneIris(sceneEl) {
  gsap.fromTo(sceneEl,
    { clipPath: 'inset(45% 30% 45% 30% round 8px)' },
    {
      clipPath: 'inset(0% 0% 0% 0% round 0px)',
      ease: 'none',
      scrollTrigger: {
        trigger: sceneEl,
        start: 'top 80%',
        end: 'top 20%',
        scrub: 1,
      }
    }
  );
}
```

---

## Pattern 6: Horizontal Scroll Conversion {#pattern-6}

Vertical scrolling drives horizontal movement through panels. Classic premium technique.

```javascript
function initHorizontalScroll(containerEl) {
  const panels = gsap.utils.toArray('.h-panel', containerEl);

  gsap.to(panels, {
    xPercent: -100 * (panels.length - 1),
    ease: 'none',
    scrollTrigger: {
      trigger: containerEl,
      pin: true,
      scrub: 1,
      end: () => `+=${containerEl.offsetWidth * (panels.length - 1)}`,
      snap: 1 / (panels.length - 1),  // auto-snap to each panel
    }
  });
}
```

```css
.h-scroll-container {
  display: flex;
  width: calc(300vw); /* 3 panels × 100vw */
  height: 100vh;
  overflow: hidden;
}
.h-panel {
  width: 100vw;
  height: 100vh;
  flex-shrink: 0;
}
```

---

## Pattern 7: Perspective Zoom Fly-Through {#pattern-7}

User appears to fly toward content. Combines scale, Z-axis, and opacity on a scrubbed pin.

```javascript
function initPerspectiveZoom(sceneEl) {
  const tl = gsap.timeline({
    scrollTrigger: {
      trigger: sceneEl,
      start: 'top top',
      end: '+=300%',
      pin: true,
      scrub: 2,
    }
  });

  // Background "rushes toward" viewer
  tl.fromTo('.zoom-bg',
    { scale: 0.4, filter: 'blur(20px)', opacity: 0.3 },
    { scale: 1.2, filter: 'blur(0px)', opacity: 1, duration: 0.6 }
  )
  // Product appears from far
  .fromTo('.zoom-product',
    { scale: 0.1, z: -2000, opacity: 0 },
    { scale: 1, z: 0, opacity: 1, duration: 0.5, ease: 'power2.out' },
    0.2
  )
  // Text fades in after product arrives
  .fromTo('.zoom-title',
    { opacity: 0, letterSpacing: '2em' },
    { opacity: 1, letterSpacing: '0.05em', duration: 0.3 },
    0.55
  );
}
```

```css
.zoom-scene {
  perspective: 1200px;
  perspective-origin: 50% 50%;
  transform-style: preserve-3d;
  overflow: hidden;
}
```

---

## Pattern 8: Snap-to-Section {#pattern-8}

Full-page scroll snapping between sections — creates a chapter-like book feeling.

```javascript
// Using GSAP Observer for smooth snapping
function initSectionSnap() {
  // Register Observer plugin
  gsap.registerPlugin(Observer);

  const sections = gsap.utils.toArray('.snap-section');
  let currentIndex = 0;
  let animating = false;

  function goTo(index) {
    if (animating || index === currentIndex) return;
    animating = true;

    const direction = index > currentIndex ? 1 : -1;
    const current = sections[currentIndex];
    const next = sections[index];

    const tl = gsap.timeline({
      onComplete: () => {
        currentIndex = index;
        animating = false;
      }
    });

    // Current section exits upward
    tl.to(current, {
      yPercent: -100 * direction,
      opacity: 0,
      duration: 0.8,
      ease: 'power2.inOut'
    })
    // Next section enters from below/above
    .fromTo(next,
      { yPercent: 100 * direction, opacity: 0 },
      { yPercent: 0, opacity: 1, duration: 0.8, ease: 'power2.inOut' },
      0
    );
  }

  Observer.create({
    type: 'wheel,touch',
    onDown: () => goTo(Math.min(currentIndex + 1, sections.length - 1)),
    onUp: () => goTo(Math.max(currentIndex - 1, 0)),
    tolerance: 100,
    preventDefault: true,
  });
}
```

---

## Lenis Smooth Scroll {#lenis}

Lenis replaces native browser scroll with silky-smooth physics-based scrolling. Always pair with GSAP ScrollTrigger.

```html
<script src="https://cdn.jsdelivr.net/npm/@studio-freight/lenis@1.0.45/dist/lenis.min.js"></script>
```

```javascript
function initLenis() {
  const lenis = new Lenis({
    duration: 1.2,
    easing: (t) => Math.min(1, 1.001 - Math.pow(2, -10 * t)),
    orientation: 'vertical',
    smoothWheel: true,
  });

  // CRITICAL: Connect Lenis to GSAP ticker
  lenis.on('scroll', ScrollTrigger.update);
  gsap.ticker.add((time) => lenis.raf(time * 1000));
  gsap.ticker.lagSmoothing(0);

  return lenis;
}
```

---

## IntersectionObserver Activation {#intersection-observer}

Only animate elements that are currently visible. Critical for performance.

```javascript
function initRevealObserver() {
  const observer = new IntersectionObserver((entries) => {
    entries.forEach(entry => {
      if (entry.isIntersecting) {
        entry.target.classList.add('is-visible');
        // Trigger GSAP animation
        const animType = entry.target.dataset.animate;
        if (animType) triggerAnimation(entry.target, animType);
        // Stop observing after first trigger
        observer.unobserve(entry.target);
      }
    });
  }, {
    threshold: 0.15,
    rootMargin: '0px 0px -50px 0px'
  });

  document.querySelectorAll('[data-animate]').forEach(el => observer.observe(el));
}

function triggerAnimation(el, type) {
  const animations = {
    'fade-up':    () => gsap.from(el, { y: 60, opacity: 0, duration: 0.8, ease: 'power3.out' }),
    'fade-in':    () => gsap.from(el, { opacity: 0, duration: 1.0, ease: 'power2.out' }),
    'scale-in':   () => gsap.from(el, { scale: 0.8, opacity: 0, duration: 0.7, ease: 'back.out(1.7)' }),
    'slide-left': () => gsap.from(el, { x: -80, opacity: 0, duration: 0.8, ease: 'power3.out' }),
    'slide-right':() => gsap.from(el, { x: 80, opacity: 0, duration: 0.8, ease: 'power3.out' }),
    'converge':   () => animateSplitConverge(el), // See text-animations.md
  };
  animations[type]?.();
}
```

---

## Pattern 9: Elastic Drop with Impact Shake {#elastic-drop}

An element falls from above with an elastic overshoot, then a rapid
micro-rotation shake fires on landing — simulating physical weight and impact.

```javascript
function initElasticDrop(productEl, wrapperEl) {
  const tl = gsap.timeline({ delay: 0.3 });

  // Phase 1: element drops with elastic bounce
  tl.from(productEl, {
    y: -180,
    opacity: 0,
    scale: 1.1,
    duration: 1.3,
    ease: 'elastic.out(1, 0.65)',
  })

  // Phase 2: shake fires just as the elastic settles
  // Apply to the WRAPPER not the element — avoids transform conflicts
  .to(wrapperEl, {
    keyframes: [
      { rotation: -2,   duration: 0.08 },
      { rotation:  2,   duration: 0.08 },
      { rotation: -1.5, duration: 0.07 },
      { rotation:  1,   duration: 0.07 },
      { rotation:  0,   duration: 0.10 },
    ],
    ease: 'power1.inOut',
  }, '-=0.35');

  return tl;
}
```

```html
<!-- Wrapper and product must be separate elements -->
<div class="drop-wrapper" id="dropWrapper">
  <img class="drop-product" id="dropProduct" src="product.png" alt="..." />
</div>
```

Ease variants:
- `elastic.out(1, 0.65)` — standard product, moderate bounce
- `elastic.out(1.2, 0.5)` — heavier object, more overshoot
- `elastic.out(0.8, 0.8)` — lighter, quicker settle
- `back.out(2.5)` — no oscillation, one clean overshoot

Do NOT use for: gentle floaters, airy elements (flowers, feathers) — use `power3.out` instead.
