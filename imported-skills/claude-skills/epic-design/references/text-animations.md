# Text Animation Reference

## Table of Contents
1. [Setup: SplitText & Dependencies](#setup)
2. [Technique 1: Split Converge (Left+Right Merge)](#split-converge)
3. [Technique 2: Masked Line Curtain Reveal](#masked-line)
4. [Technique 3: Character Cylinder Rotation](#cylinder)
5. [Technique 4: Word-by-Word Scroll Lighting](#word-lighting)
6. [Technique 5: Scramble Text](#scramble)
7. [Technique 6: Skew + Elastic Bounce Entry](#skew-bounce)
8. [Technique 7: Theatrical Enter + Auto Exit](#theatrical)
9. [Technique 8: Offset Diagonal Layout](#offset-diagonal)
10. [Technique 9: Line Clip Wipe](#line-clip-wipe)
11. [Technique 10: Scroll-Speed Reactive Marquee](#marquee)
12. [Technique 11: Variable Font Wave](#variable-font)
13. [Technique 12: Bleed Typography](#bleed-type)

---

## Setup: SplitText & Dependencies {#setup}

```html
<!-- GSAP SplitText (free in GSAP 3.12+) -->
<script src="https://cdn.jsdelivr.net/npm/gsap@3.12.5/dist/gsap.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/gsap@3.12.5/dist/SplitText.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/gsap@3.12.5/dist/ScrollTrigger.min.js"></script>
<script>
  gsap.registerPlugin(SplitText, ScrollTrigger);
</script>
```

### Universal Text Setup CSS

```css
/* All text elements that animate need this */
.anim-text {
  overflow: hidden; /* Contains line mask reveals */
  line-height: 1.15;
}
/* Screen reader: preserve meaning even when SplitText fragments it */
.anim-text[aria-label] > * {
  aria-hidden: true;
}
```

---

## Technique 1: Split Converge (Left+Right Merge) {#split-converge}

The signature effect: two halves of a title fly in from opposite sides, converge to form the complete title, hold, then diverge and disappear on scroll exit. Exactly what the user described.

```css
.hero-title {
  display: flex;
  flex-wrap: wrap;
  gap: 0.25em;
  overflow: visible; /* allow parts to fly from outside viewport */
}
.hero-title .word-left {
  display: inline-block;
  /* starts at far left */
}
.hero-title .word-right {
  display: inline-block;
  /* starts at far right */
}
```

```javascript
function initSplitConverge(titleEl) {
  // Preserve accessibility
  const fullText = titleEl.textContent;
  titleEl.setAttribute('aria-label', fullText);

  const words = titleEl.querySelectorAll('.word');
  const midpoint = Math.floor(words.length / 2);

  const leftWords = Array.from(words).slice(0, midpoint);
  const rightWords = Array.from(words).slice(midpoint);

  const tl = gsap.timeline({
    scrollTrigger: {
      trigger: titleEl.closest('.scene'),
      start: 'top top',
      end: '+=250%',
      pin: true,
      scrub: 1.2,
    }
  });

  // Phase 1 — ENTER (0% → 25%): Words converge from sides
  tl.fromTo(leftWords,
    { x: '-120vw', opacity: 0 },
    { x: 0, opacity: 1, duration: 0.25, ease: 'power3.out', stagger: 0.03 },
    0
  )
  .fromTo(rightWords,
    { x: '120vw', opacity: 0 },
    { x: 0, opacity: 1, duration: 0.25, ease: 'power3.out', stagger: -0.03 },
    0
  )

  // Phase 2 — HOLD (25% → 70%): Nothing — words are readable, section pinned
  // (empty duration keeps the scrub paused here)
  .to({}, { duration: 0.45 }, 0.25)

  // Phase 3 — EXIT (70% → 100%): Words diverge back out
  .to(leftWords,
    { x: '-120vw', opacity: 0, duration: 0.28, ease: 'power3.in', stagger: 0.02 },
    0.70
  )
  .to(rightWords,
    { x: '120vw', opacity: 0, duration: 0.28, ease: 'power3.in', stagger: -0.02 },
    0.70
  );

  return tl;
}
```

### HTML Template

```html
<h1 class="hero-title anim-text" aria-label="Your Brand Name">
  <span class="word word-left">Your</span>
  <span class="word word-left">Brand</span>
  <span class="word word-right">Name</span>
  <span class="word word-right">Here</span>
</h1>
```

---

## Technique 2: Masked Line Curtain Reveal {#masked-line}

Lines slide upward from behind an invisible curtain. Each line is hidden in an `overflow: hidden` container and translates up into view.

```css
.curtain-text .line-mask {
  overflow: hidden;
  line-height: 1.2;
  /* The mask — content starts below and slides up into view */
}
.curtain-text .line-inner {
  display: block;
  /* Starts translated down below the mask */
  transform: translateY(110%);
}
```

```javascript
function initCurtainReveal(textEl) {
  // SplitText splits into lines automatically
  const split = new SplitText(textEl, {
    type: 'lines',
    linesClass: 'line-inner',
    // Wraps each line in overflow:hidden container
    lineThreshold: 0.1,
  });

  // Wrap each line in a mask container
  split.lines.forEach(line => {
    const mask = document.createElement('div');
    mask.className = 'line-mask';
    line.parentNode.insertBefore(mask, line);
    mask.appendChild(line);
  });

  gsap.from(split.lines, {
    y: '110%',
    duration: 0.9,
    ease: 'power4.out',
    stagger: 0.12,
    scrollTrigger: {
      trigger: textEl,
      start: 'top 80%',
    }
  });
}
```

---

## Technique 3: Character Cylinder Rotation {#cylinder}

Letters rotate in on a 3D cylinder axis — like a slot machine or odometer rolling into place. Premium, memorable.

```css
.cylinder-text {
  perspective: 800px;
}
.cylinder-text .char {
  display: inline-block;
  transform-origin: center center -60px; /* pivot point BEHIND the letter */
  transform-style: preserve-3d;
}
```

```javascript
function initCylinderRotation(titleEl) {
  const split = new SplitText(titleEl, { type: 'chars' });

  gsap.from(split.chars, {
    rotateX: -90,
    opacity: 0,
    duration: 0.6,
    ease: 'back.out(1.5)',
    stagger: {
      each: 0.04,
      from: 'start'
    },
    scrollTrigger: {
      trigger: titleEl,
      start: 'top 75%',
    }
  });
}
```

---

## Technique 4: Word-by-Word Scroll Lighting {#word-lighting}

Words appear to light up one at a time, driven by scroll position. Apple's signature prose technique.

```css
.scroll-lit-text {
  /* Start all words dim */
}
.scroll-lit-text .word {
  display: inline-block;
  color: rgba(255, 255, 255, 0.15); /* dim unlit state */
  transition: color 0.1s ease;
}
.scroll-lit-text .word.lit {
  color: rgba(255, 255, 255, 1.0); /* bright lit state */
}
```

```javascript
function initWordScrollLighting(containerEl, textEl) {
  const split = new SplitText(textEl, { type: 'words' });
  const words = split.words;
  const totalWords = words.length;

  // Pin the section and light words as user scrolls
  ScrollTrigger.create({
    trigger: containerEl,
    start: 'top top',
    end: `+=${totalWords * 80}px`, // ~80px per word
    pin: true,
    scrub: 0.5,
    onUpdate: (self) => {
      const progress = self.progress;
      const litCount = Math.round(progress * totalWords);
      words.forEach((word, i) => {
        word.classList.toggle('lit', i < litCount);
      });
    }
  });
}
```

---

## Technique 5: Scramble Text {#scramble}

Characters cycle through random values before resolving to real text. Feels digital, techy, premium.

```html
<script src="https://cdn.jsdelivr.net/npm/gsap@3.12.5/dist/TextPlugin.min.js"></script>
```

```javascript
// Custom scramble implementation (no plugin needed)
function scrambleText(el, finalText, duration = 1.5) {
  const chars = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789!@#$%';
  let startTime = null;
  const originalText = finalText;

  function step(timestamp) {
    if (!startTime) startTime = timestamp;
    const progress = Math.min((timestamp - startTime) / (duration * 1000), 1);

    let result = '';
    for (let i = 0; i < originalText.length; i++) {
      if (originalText[i] === ' ') {
        result += ' ';
      } else if (i / originalText.length < progress) {
        // This character has resolved
        result += originalText[i];
      } else {
        // Still scrambling
        result += chars[Math.floor(Math.random() * chars.length)];
      }
    }
    el.textContent = result;

    if (progress < 1) requestAnimationFrame(step);
  }

  requestAnimationFrame(step);
}

// Trigger on scroll
ScrollTrigger.create({
  trigger: '.scramble-title',
  start: 'top 80%',
  once: true,
  onEnter: () => {
    scrambleText(
      document.querySelector('.scramble-title'),
      document.querySelector('.scramble-title').dataset.text,
      1.8
    );
  }
});
```

---

## Technique 6: Skew + Elastic Bounce Entry {#skew-bounce}

Elements enter with a skew that corrects itself, combined with a slight overshoot. Feels physical and energetic.

```javascript
function initSkewBounce(elements) {
  gsap.from(elements, {
    y: 80,
    skewY: 7,
    opacity: 0,
    duration: 0.9,
    ease: 'back.out(1.7)',
    stagger: 0.1,
    scrollTrigger: {
      trigger: elements[0],
      start: 'top 85%',
    }
  });
}
```

---

## Technique 7: Theatrical Enter + Auto Exit {#theatrical}

Element automatically animates in when entering the viewport AND animates out when leaving — zero JavaScript needed.

```css
/* Enter animation */
@keyframes theatrical-enter {
  from {
    opacity: 0;
    transform: translateY(60px);
    filter: blur(4px);
  }
  to {
    opacity: 1;
    transform: translateY(0);
    filter: blur(0px);
  }
}

/* Exit animation */
@keyframes theatrical-exit {
  from {
    opacity: 1;
    transform: translateY(0);
  }
  to {
    opacity: 0;
    transform: translateY(-60px);
  }
}

.theatrical {
  /* Enter when element comes into view */
  animation: theatrical-enter linear both;
  animation-timeline: view();
  animation-range: entry 0% entry 40%;
}

.theatrical-with-exit {
  animation: theatrical-enter linear both, theatrical-exit linear both;
  animation-timeline: view(), view();
  animation-range: entry 0% entry 30%, exit 60% exit 100%;
}
```

**Zero JavaScript required.** Just add `.theatrical` or `.theatrical-with-exit` class.

---

## Technique 8: Offset Diagonal Layout {#offset-diagonal}

Lines of a title start at offset positions (one top-left, one lower-right), then animate FROM their natural offset positions FROM opposite directions. Creates a staircase visual composition that feels dynamic even before animation.

```css
.offset-title {
  position: relative;
  /* Don't center — let offset do the work */
}
.offset-title .line-1 {
  /* Top-left */
  display: block;
  text-align: left;
  padding-left: 5%;
  font-size: clamp(48px, 8vw, 100px);
}
.offset-title .line-2 {
  /* Lower-right — drops down and shifts right */
  display: block;
  text-align: right;
  padding-right: 5%;
  margin-top: 0.4em;
  font-size: clamp(48px, 8vw, 100px);
}
```

```javascript
function initOffsetDiagonal(titleEl) {
  const line1 = titleEl.querySelector('.line-1');
  const line2 = titleEl.querySelector('.line-2');

  gsap.from(line1, {
    x: '-15vw',
    opacity: 0,
    duration: 1.0,
    ease: 'power4.out',
    scrollTrigger: { trigger: titleEl, start: 'top 75%' }
  });

  gsap.from(line2, {
    x: '15vw',
    opacity: 0,
    duration: 1.0,
    ease: 'power4.out',
    delay: 0.15,
    scrollTrigger: { trigger: titleEl, start: 'top 75%' }
  });
}
```

---

## Technique 9: Line Clip Wipe {#line-clip-wipe}

Each line of text reveals from left to right, like a typewriter but with a clean clip-path sweep.

```javascript
function initLineClipWipe(textEl) {
  const split = new SplitText(textEl, { type: 'lines' });

  split.lines.forEach((line, i) => {
    gsap.fromTo(line,
      { clipPath: 'inset(0 100% 0 0)' },
      {
        clipPath: 'inset(0 0% 0 0)',
        duration: 0.8,
        ease: 'power3.out',
        delay: i * 0.12, // stagger between lines
        scrollTrigger: {
          trigger: textEl,
          start: 'top 80%',
        }
      }
    );
  });
}
```

---

## Technique 10: Scroll-Speed Reactive Marquee {#marquee}

Infinite scrolling text. Speed scales with scroll velocity — fast scroll = fast marquee. Slow scroll = slow/paused.

```css
.marquee-wrapper {
  overflow: hidden;
  white-space: nowrap;
}
.marquee-track {
  display: inline-flex;
  gap: 4rem;
  /* Two copies side by side for seamless loop */
}
.marquee-track .marquee-item {
  display: inline-block;
  font-size: clamp(2rem, 5vw, 5rem);
  font-weight: 700;
  letter-spacing: -0.02em;
}
```

```javascript
function initReactiveMarquee(wrapperEl) {
  const track = wrapperEl.querySelector('.marquee-track');
  let currentX = 0;
  let velocity = 0;
  let baseSpeed = 0.8; // px per frame base speed
  let lastScrollY = window.scrollY;
  let lastTime = performance.now();

  // Track scroll velocity
  window.addEventListener('scroll', () => {
    const now = performance.now();
    const dt = now - lastTime;
    const dy = window.scrollY - lastScrollY;
    velocity = Math.abs(dy / dt) * 30; // scale to marquee speed
    lastScrollY = window.scrollY;
    lastTime = now;
  }, { passive: true });

  function animate() {
    velocity = Math.max(0, velocity - 0.3); // decay
    const speed = baseSpeed + velocity;
    currentX -= speed;

    // Reset when first copy exits viewport
    const trackWidth = track.children[0].offsetWidth * track.children.length / 2;
    if (Math.abs(currentX) >= trackWidth) {
      currentX += trackWidth;
    }

    track.style.transform = `translateX(${currentX}px)`;
    requestAnimationFrame(animate);
  }
  animate();
}
```

---

## Technique 11: Variable Font Wave {#variable-font}

If the font supports variable axes (weight, width), animate them per-character for a wave/ripple effect.

```javascript
function initVariableFontWave(titleEl) {
  const split = new SplitText(titleEl, { type: 'chars' });

  // Wave through characters using weight axis
  gsap.to(split.chars, {
    fontVariationSettings: '"wght" 800',
    duration: 0.4,
    ease: 'power2.inOut',
    stagger: {
      each: 0.06,
      yoyo: true,
      repeat: -1, // infinite loop
    }
  });
}
```

**Note:** Requires a variable font. Free options: Inter Variable, Fraunces, Recursive. Load from Google Fonts with `?display=swap&axes=wght`.

---

## Technique 12: Bleed Typography {#bleed-type}

Oversized headline that intentionally exceeds section boundaries. Creates drama, depth, and visual tension.

```css
.bleed-title {
  font-size: clamp(80px, 18vw, 220px);
  font-weight: 900;
  line-height: 0.9;
  letter-spacing: -0.04em;

  /* Allow bleeding outside section */
  position: relative;
  z-index: 10;
  pointer-events: none;

  /* Negative margins to bleed out */
  margin-left: -0.05em;
  margin-right: -0.05em;

  /* Optionally: half above, half below section boundary */
  transform: translateY(30%);
}

/* Parent section allows overflow */
.bleed-section {
  overflow: visible;
  position: relative;
  z-index: 2;
}
/* Next section needs to be higher to "trap" the bleed */
.bleed-section + .next-section {
  position: relative;
  z-index: 3;
}
```

```javascript
// Parallax on the bleed title — moves at slightly different rate
// to emphasize that it belongs to a different depth than content
gsap.to('.bleed-title', {
  y: '-12%',
  ease: 'none',
  scrollTrigger: {
    trigger: '.bleed-section',
    start: 'top bottom',
    end: 'bottom top',
    scrub: true,
  }
});
```

---

## Technique 13: Ghost Outlined Background Text {#ghost-text}

Massive atmospheric text sitting BEHIND the main product using only a thin stroke
with transparent fill. Supports the scene without competing with the content.

```css
.ghost-bg-text {
  color: transparent;
  -webkit-text-stroke: 1px rgba(255, 255, 255, 0.15); /* light sites */
  /* dark sites: -webkit-text-stroke: 1px rgba(255, 106, 26, 0.18); */

  font-size: clamp(5rem, 15vw, 18rem);
  font-weight: 900;
  line-height: 0.85;
  letter-spacing: -0.04em;
  white-space: nowrap;

  z-index: 2; /* must be lower than the hero product (depth-3 = z-index 3+) */
  pointer-events: none;
  user-select: none;
}
```

```javascript
// Entrance: lines slide up from a masked overflow:hidden parent
function initGhostTextEntrance(lines) {
  gsap.set(lines, { y: '110%' });
  gsap.to(lines, {
    y: '0%',
    stagger: 0.1,
    duration: 1.1,
    ease: 'power4.out',
    delay: 0.2,
  });
}

// Exit: lines drift apart as hero scrolls out
function addGhostTextExit(scrubTimeline, line1, line2) {
  scrubTimeline
    .to(line1, { x: '-12vw', opacity: 0.06, duration: 0.3 }, 0)
    .to(line2, { x:  '12vw', opacity: 0.06, duration: 0.3 }, 0)
    .to(line1, { x: '-40vw', opacity: 0,    duration: 0.25 }, 0.4)
    .to(line2, { x:  '40vw', opacity: 0,    duration: 0.25 }, 0.4);
}
```

Stroke opacity guide:
- `0.08–0.12` → barely-there atmosphere
- `0.15–0.22` → readable on inspection, still subtle
- `0.25–0.35` → prominently visible — only if it IS the visual focus

Rules:
1. Always `aria-hidden="true"` — never the real heading
2. A real `<h1>` must exist elsewhere for SEO/screen readers
3. Only works on dark backgrounds — thin strokes vanish on light ones
4. Maximum 2 lines — 3+ becomes noise
5. Best with ultra-heavy weights (800–900) and tight letter-spacing

---

## Combining Techniques

The most premium results come from layering multiple text techniques in the same section:

```javascript
// Example: Full hero text sequence
function initHeroTextSequence() {
  const tl = gsap.timeline({
    scrollTrigger: {
      trigger: '.hero-scene',
      start: 'top top',
      end: '+=300%',
      pin: true,
      scrub: 1,
    }
  });

  // 1. Bleed title already visible via CSS
  // 2. Subtitle curtain reveal
  tl.from('.hero-sub .line-inner', {
    y: '110%', duration: 0.2, stagger: 0.05
  }, 0)
  // 3. CTA skew bounce
  .from('.hero-cta', {
    y: 40, skewY: 5, opacity: 0, duration: 0.15, ease: 'back.out'
  }, 0.15)
  // 4. On scroll-through: title exits via split converge reverse
  .to('.hero-title .word-left', {
    x: '-80vw', opacity: 0, duration: 0.25, stagger: 0.03
  }, 0.7)
  .to('.hero-title .word-right', {
    x: '80vw', opacity: 0, duration: 0.25, stagger: -0.03
  }, 0.7);
}
```
