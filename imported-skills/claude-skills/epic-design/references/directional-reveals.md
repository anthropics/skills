# Directional Reveals Reference

Elements and sections don't always enter from the bottom. Premium sites use **directional births** — sections that drop from the top, iris open from center, peel away like wallpaper, or unfold diagonally. This file covers all 8 directional reveal patterns.

## Table of Contents
1. [Top-Down Clip Birth](#top-down)
2. [Window Pane Iris Open](#iris-open)
3. [Curtain Panel Roll-Up](#curtain-rollup)
4. [SVG Morph Border](#svg-morph)
5. [Diagonal Wipe Birth](#diagonal-wipe)
6. [Circle Iris Expand](#circle-iris)
7. [Multi-Directional Stagger Grid](#multi-direction)
8. [Loading Screen Curtain Lift](#loading-screen)

---

## Pattern 1: Top-Down Clip Birth {#top-down}

The section is born from the top edge and grows **downward**. Instead of rising from below, it drops and unfolds from above. This is the opposite of the conventional bottom-up reveal and creates a striking "curtain drop" feeling.

```css
/* Starting state — section is fully clipped (invisible) */
.top-drop-section {
  /* Section exists in DOM but is invisible */
  clip-path: inset(0 0 100% 0);
  /* 
    inset(top right bottom left):
    - top: 0 → clip starts at top edge
    - bottom: 100% → clips 100% from bottom = nothing visible
  */
}

/* Revealed state */
.top-drop-section.revealed {
  clip-path: inset(0 0 0% 0);
  transition: clip-path 1.2s cubic-bezier(0.16, 1, 0.3, 1);
}
```

```javascript
// GSAP scroll-driven version with scrub
function initTopDownBirth(sectionEl) {
  gsap.fromTo(sectionEl,
    { clipPath: 'inset(0 0 100% 0)' },
    {
      clipPath: 'inset(0 0 0% 0)',
      ease: 'power2.out',
      scrollTrigger: {
        trigger: sectionEl.previousElementSibling, // previous section is the trigger
        start: 'bottom 80%',
        end: 'bottom 20%',
        scrub: 1.5,
      }
    }
  );
}

// Exit: section retracts back upward (born from top, dies back up)
function addTopRetractExit(sectionEl) {
  gsap.to(sectionEl, {
    clipPath: 'inset(100% 0 0% 0)', // now clips from TOP — retracts upward
    ease: 'power2.in',
    scrollTrigger: {
      trigger: sectionEl,
      start: 'bottom 20%',
      end: 'bottom top',
      scrub: 1,
    }
  });
}
```

**Key insight:** Enter = `inset(0 0 100% 0)` → `inset(0 0 0% 0)` (bottom clips away downward).
Exit = `inset(0)` → `inset(100% 0 0 0)` (top clips away upward = retracts back where it came from).

---

## Pattern 2: Window Pane Iris Open {#iris-open}

An entire section starts as a tiny centered rectangle — like a keyhole or portal — and expands outward to fill the viewport. Creates a cinematic "opening shot" feeling.

```javascript
function initWindowPaneIris(sectionEl) {
  // The section starts as a small centered window
  gsap.fromTo(sectionEl,
    {
      clipPath: 'inset(42% 35% 42% 35% round 12px)',
      // 42% from top AND bottom = only 16% of height visible
      // 35% from left AND right = only 30% of width visible
      // Centered rectangle peek
    },
    {
      clipPath: 'inset(0% 0% 0% 0% round 0px)',
      ease: 'none',
      scrollTrigger: {
        trigger: sectionEl,
        start: 'top 90%',
        end: 'top 10%',
        scrub: 1.2,
      }
    }
  );

  // Also scale/zoom the content inside for parallax depth
  gsap.fromTo(sectionEl.querySelector('.iris-content'),
    { scale: 1.4 },
    {
      scale: 1,
      ease: 'none',
      scrollTrigger: {
        trigger: sectionEl,
        start: 'top 90%',
        end: 'top 10%',
        scrub: 1.2,
      }
    }
  );
}
```

**Variation — horizontal bar open (blinds effect):**
```javascript
// Two bars that slide apart (one from top, one from bottom)
function initBlindsOpen(topBar, bottomBar, revealEl) {
  const tl = gsap.timeline({
    scrollTrigger: {
      trigger: revealEl,
      start: 'top 70%',
      toggleActions: 'play none none reverse',
    }
  });

  tl.to(topBar, { yPercent: -100, duration: 1.0, ease: 'power3.inOut' })
    .to(bottomBar, { yPercent: 100, duration: 1.0, ease: 'power3.inOut' }, 0);
}
```

---

## Pattern 3: Curtain Panel Roll-Up {#curtain-rollup}

Multiple layered panels. Each one "rolls up" from top, exposing the panel beneath. Like peeling back wallpaper layers to reveal what's underneath. Uses z-index stacking.

```css
.curtain-stack {
  position: relative;
  height: 100vh;
  overflow: hidden;
}

.curtain-panel {
  position: absolute;
  inset: 0;
  /* Stack panels — panel 1 on top, panel N on bottom */
}
.curtain-panel:nth-child(1) { z-index: 5; background: #0f0f0f; }
.curtain-panel:nth-child(2) { z-index: 4; background: #1a0a2e; }
.curtain-panel:nth-child(3) { z-index: 3; background: #2d0b4e; }
.curtain-panel:nth-child(4) { z-index: 2; background: #1e3a8a; }
/* Final revealed content at z-index 1 */
```

```javascript
function initCurtainRollUp(containerEl) {
  const panels = gsap.utils.toArray('.curtain-panel', containerEl);

  const tl = gsap.timeline({
    scrollTrigger: {
      trigger: containerEl,
      start: 'top top',
      end: `+=${panels.length * 120}%`,
      pin: true,
      scrub: 1,
    }
  });

  panels.forEach((panel, i) => {
    const segmentDuration = 1 / panels.length;
    const segmentStart = i * segmentDuration;

    // Each panel rolls up — clip from bottom rises to top
    tl.to(panel, {
      clipPath: 'inset(100% 0 0% 0)', // rolls up: bottom clips first, rising to 100%
      duration: segmentDuration,
      ease: 'power2.inOut',
    }, segmentStart);

    // Heading for this panel fades in
    const heading = panel.querySelector('.panel-heading');
    if (heading) {
      tl.from(heading, {
        opacity: 0,
        y: 30,
        duration: segmentDuration * 0.4,
      }, segmentStart + segmentDuration * 0.1);
    }
  });

  return tl;
}
```

---

## Pattern 4: SVG Morph Border {#svg-morph}

The section's edge is not a hard straight line — it morphs between shapes (rectangle → wave → diagonal → organic curve) as the user scrolls. Makes sections feel alive and fluid.

```html
<!-- SVG clipPath element -->
<svg width="0" height="0" style="position:absolute">
  <defs>
    <clipPath id="morphClip" clipPathUnits="objectBoundingBox">
      <path id="morphPath" d="M0,0 L1,0 L1,0.95 Q0.5,1.05 0,0.95 Z"/>
    </clipPath>
  </defs>
</svg>

<section class="morphed-section" style="clip-path: url(#morphClip)">
  <!-- section content -->
</section>
```

```javascript
function initSVGMorphBorder() {
  const morphPath = document.getElementById('morphPath');

  const paths = {
    straight: 'M0,0 L1,0 L1,1 L0,1 Z',
    wave:     'M0,0 L1,0 L1,0.95 Q0.75,1.05 0.5,0.95 Q0.25,0.85 0,0.95 Z',
    diagonal: 'M0,0 L1,0 L1,0.88 L0,1.0 Z',
    organic:  'M0,0 L1,0 L1,0.92 C0.8,1.04 0.6,0.88 0.4,1.0 C0.2,1.12 0.1,0.90 0,0.96 Z',
  };

  ScrollTrigger.create({
    trigger: '.morphed-section',
    start: 'top 80%',
    end: 'bottom 20%',
    scrub: 2,
    onUpdate: (self) => {
      const p = self.progress;
      // Morph between straight → wave → diagonal as scroll progresses
      if (p < 0.5) {
        // Interpolate straight → wave
        morphPath.setAttribute('d', p < 0.25 ? paths.straight : paths.wave);
      } else {
        morphPath.setAttribute('d', p < 0.75 ? paths.wave : paths.diagonal);
      }
    }
  });
}
```

---

## Pattern 5: Diagonal Wipe Birth {#diagonal-wipe}

Content is revealed by a diagonal sweep across the screen — from top-left corner to bottom-right (or any corner combination). Feels cinematic and directional.

```javascript
function initDiagonalWipe(el, direction = 'top-left') {
  const clipPaths = {
    'top-left': {
      from: 'polygon(0 0, 0 0, 0 0)',
      to:   'polygon(0 0, 120% 0, 0 120%)',
    },
    'top-right': {
      from: 'polygon(100% 0, 100% 0, 100% 0)',
      to:   'polygon(-20% 0, 100% 0, 100% 120%)',
    },
    'center-out': {
      from: 'polygon(50% 50%, 50% 50%, 50% 50%, 50% 50%)',
      to:   'polygon(-10% -10%, 110% -10%, 110% 110%, -10% 110%)',
    },
  };

  const { from, to } = clipPaths[direction];

  gsap.fromTo(el,
    { clipPath: from },
    {
      clipPath: to,
      duration: 1.4,
      ease: 'power3.inOut',
      scrollTrigger: {
        trigger: el,
        start: 'top 70%',
      }
    }
  );
}
```

---

## Pattern 6: Circle Iris Expand {#circle-iris}

The most dramatic reveal: a perfect circle expands from the center of the section outward, like an aperture opening or a spotlight switching on.

```javascript
function initCircleIris(el, originX = '50%', originY = '50%') {
  gsap.fromTo(el,
    { clipPath: `circle(0% at ${originX} ${originY})` },
    {
      clipPath: `circle(80% at ${originX} ${originY})`,
      ease: 'none',
      scrollTrigger: {
        trigger: el,
        start: 'top 75%',
        end: 'top 25%',
        scrub: 1,
      }
    }
  );
}

// Variant: iris opens from cursor position on hover
function initHoverIris(el) {
  el.addEventListener('mouseenter', (e) => {
    const rect = el.getBoundingClientRect();
    const x = ((e.clientX - rect.left) / rect.width * 100).toFixed(1) + '%';
    const y = ((e.clientY - rect.top) / rect.height * 100).toFixed(1) + '%';

    gsap.fromTo(el,
      { clipPath: `circle(0% at ${x} ${y})` },
      { clipPath: `circle(100% at ${x} ${y})`, duration: 0.6, ease: 'power2.out' }
    );
  });
}
```

---

## Pattern 7: Multi-Directional Stagger Grid {#multi-direction}

When a grid or set of cards appears, each item enters from a different edge/direction — creating a dynamic assembly effect instead of uniform fade-ups.

```javascript
function initMultiDirectionalGrid(gridEl) {
  const items = gsap.utils.toArray('.grid-item', gridEl);

  const directions = [
    { x: -80, y: 0 },   // from left
    { x: 0, y: -80 },   // from top
    { x: 80, y: 0 },    // from right
    { x: 0, y: 80 },    // from bottom
    { x: -60, y: -60 }, // from top-left
    { x: 60, y: -60 },  // from top-right
    { x: -60, y: 60 },  // from bottom-left
    { x: 60, y: 60 },   // from bottom-right
  ];

  items.forEach((item, i) => {
    const dir = directions[i % directions.length];

    gsap.from(item, {
      x: dir.x,
      y: dir.y,
      opacity: 0,
      duration: 0.8,
      ease: 'power3.out',
      scrollTrigger: {
        trigger: gridEl,
        start: 'top 75%',
      },
      delay: i * 0.08, // stagger
    });
  });
}
```

---

## Pattern 8: Loading Screen Curtain Lift {#loading-screen}

A full-viewport branded intro screen that physically lifts off the page on load, revealing the site beneath. Sets cinematic expectations before any scroll animation begins.

```css
.loading-curtain {
  position: fixed;
  inset: 0;
  z-index: 9999;
  background: #0a0a0a; /* or brand color */
  display: flex;
  align-items: center;
  justify-content: center;
  /* Split into two halves for dramatic split-open effect */
}

.curtain-top {
  position: absolute;
  top: 0; left: 0; right: 0;
  height: 50%;
  background: inherit;
  transform-origin: top center;
}

.curtain-bottom {
  position: absolute;
  bottom: 0; left: 0; right: 0;
  height: 50%;
  background: inherit;
  transform-origin: bottom center;
}
```

```javascript
function initLoadingCurtain() {
  const curtainTop = document.querySelector('.curtain-top');
  const curtainBottom = document.querySelector('.curtain-bottom');
  const curtainLogo = document.querySelector('.curtain-logo');
  const loadingScreen = document.querySelector('.loading-curtain');

  // Prevent scroll during loading
  document.body.style.overflow = 'hidden';

  const tl = gsap.timeline({
    delay: 0.5,
    onComplete: () => {
      document.body.style.overflow = '';
      loadingScreen.style.display = 'none';
      // Init all scroll animations AFTER curtain lifts
      initAllAnimations();
    }
  });

  // Logo appears first
  tl.from(curtainLogo, { opacity: 0, scale: 0.8, duration: 0.6, ease: 'power2.out' })
    // Brief hold
    .to({}, { duration: 0.4 })
    // Logo fades out
    .to(curtainLogo, { opacity: 0, scale: 1.1, duration: 0.4, ease: 'power2.in' })
    // Curtain splits: top goes up, bottom goes down
    .to(curtainTop, { yPercent: -100, duration: 0.9, ease: 'power4.inOut' }, '-=0.1')
    .to(curtainBottom, { yPercent: 100, duration: 0.9, ease: 'power4.inOut' }, '<');
}

window.addEventListener('load', initLoadingCurtain);
```

---

## Combining Directional Reveals

For maximum cinematic impact, chain directional reveals between sections:

```
Section 1 → Section 2: Window pane iris (section 2 peeks through a keyhole)
Section 2 → Section 3: Top-down clip birth (section 3 drops from top)
Section 3 → Section 4: Diagonal wipe (section 4 sweeps in from corner)
Section 4 → Section 5: Circle iris (section 5 opens from center)
Section 5 → Section 6: Curtain panel roll-up (exposes multiple layers)
```

Each transition feels distinct, keeping the user engaged across the full scroll experience.
