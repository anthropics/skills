# GSAP Animation Patterns — Entrance, ScrollTrigger, Parallax, Floats

This reference answers exactly one decision: **what 5 animation patterns make a landing page feel "premium" without overshooting into demo-reel territory, and how are they implemented in GSAP + CSS?**

## The Five Required Patterns

| Pattern | Tool | Purpose |
|---|---|---|
| 1. Hero entrance | GSAP timeline | Staggered fade-in of hero elements on page load |
| 2. Mouse parallax | GSAP mousemove handler | Depth perception in hero — shapes drift opposite cursor |
| 3. Scroll-triggered reveals | GSAP ScrollTrigger | Feature cards fade + tilt as they enter viewport |
| 4. Floating shapes | CSS keyframes | Continuous ambient motion in hero bg |
| 5. Scroll indicator | CSS keyframes | Chevron bounce hint at bottom of hero |

## Pattern 1: Hero Entrance (GSAP Timeline)

### The discipline: gsap.set() FIRST

The single most common landing-page bug is **FOUC** (Flash Of Unstyled Content) — the elements appear at their final positions for one frame before the entrance animation runs.

The fix is `gsap.set()` to apply initial states **before** any timeline runs:

```js
// CORRECT — initial states set first
gsap.set([".eyebrow", ".hero h1", ".hero .subtitle", ".btn-primary", ".scroll-down"], {
  opacity: 0,
  y: 30
});

const tl = gsap.timeline({ defaults: { ease: "power3.out" } });
tl.to(".eyebrow",      { opacity: 1, y: 0, duration: 0.6 })
  .to(".hero h1",      { opacity: 1, y: 0, duration: 0.8 }, "-=0.3")
  .to(".hero .subtitle", { opacity: 1, y: 0, duration: 0.6 }, "-=0.5")
  .to(".btn-primary",  { opacity: 1, y: 0, duration: 0.5 }, "-=0.3")
  .to(".scroll-down",  { opacity: 1, y: 0, duration: 0.4 }, "-=0.2");
```

### Stagger timings

The `-=` syntax overlaps animations. Standard pattern:
- H1 starts 0.3s into eyebrow
- Subtitle starts 0.5s into H1 (overlapping middle of H1)
- Button + scroll-down trail by 0.3s + 0.2s

Total entrance: ~1.5 seconds from page load. Faster feels rushed; slower feels sluggish.

### Easing

`power3.out` — strong deceleration. Elements arrive at final position quickly and "settle." This feels intentional vs `ease-linear` which feels mechanical.

Alternatives:
- `power2.out` — gentler; better for subtle reveals
- `back.out(1.4)` — slight overshoot then settle; playful tone
- `expo.out` — very strong deceleration; "elastic premium" feel

## Pattern 2: Mouse Parallax

```js
const hero = document.querySelector(".hero");
hero.addEventListener("mousemove", (e) => {
  const x = (e.clientX / window.innerWidth - 0.5) * 2;   // -1 to 1
  const y = (e.clientY / window.innerHeight - 0.5) * 2;  // -1 to 1

  gsap.to(".hero-shapes-back", { x: x * 45, y: y * 22, duration: 0.8 });
  gsap.to(".hero-shapes-mid",  { x: x * 22, y: y * 11, duration: 0.8 });
  gsap.to(".hero .container",  { x: x * 8,  y: y * 5,  duration: 0.8 });
});
```

### Depth ratio: 45 / 22 / 8

The three layers move at different multipliers to create depth:
- **Back layer (45 / 22):** moves most — feels "far" from cursor
- **Mid layer (22 / 11):** moves half as much
- **Content layer (8 / 5):** barely moves — feels "with" the user

Direction is the same for all (move with mouse, not opposite) for the "looking through" parallax effect.

### Duration 0.8s

Longer than the mouse movement itself — lag creates the parallax feel. Shorter durations (0.3s) feel reactive; longer (1.2s+) feel laggy.

### Disable on mobile

Touch devices don't have meaningful mouse position. Add:

```js
if (window.matchMedia("(hover: none)").matches) {
  // Skip mouse parallax setup
}
```

## Pattern 3: Scroll-Triggered Feature Cards

```js
gsap.set(".feature-card", { opacity: 0, y: 55, rotateX: 18 });

ScrollTrigger.batch(".feature-card", {
  start: "top 80%",   // fires when card top is 80% from viewport top
  onEnter: batch => gsap.to(batch, {
    opacity: 1,
    y: 0,
    rotateX: 0,
    duration: 0.8,
    stagger: 0.11,
    ease: "power2.out"
  })
});
```

### Initial state: rotateX: 18

The slight 3D tilt (around the X-axis) creates the "card flipping up" effect on entrance. Pure y-translation feels flat; rotateX adds dimension.

Higher rotateX (30°+) feels gimmicky; lower (8°) is invisible. 18° is the sweet spot.

### Stagger 0.11s

Cards reveal in sequence with 110ms between each. Faster feels machine-gun; slower feels like the page is broken.

### `start: "top 80%"`

The card's top edge passes 80% from the top of the viewport. This fires the animation slightly before the card is fully in view, so by the time the user looks at the card, it's already mostly settled.

## Pattern 4: Floating Decorative Shapes (CSS Keyframes)

Continuous ambient motion uses **CSS keyframes, not GSAP**. Two reasons:

1. **Performance** — CSS animations are GPU-composited at the browser level; cheaper than GSAP tweens for indefinite animation.
2. **Discipline** — GSAP for *triggered* / *interactive* animations; CSS for *ambient* / *continuous*.

```css
@keyframes floatA {
  0%, 100% { transform: translate(0, 0) rotate(0deg); }
  50%      { transform: translate(20px, -30px) rotate(8deg); }
}
@keyframes floatB {
  0%, 100% { transform: translate(0, 0) rotate(0deg); }
  50%      { transform: translate(-15px, 25px) rotate(-6deg); }
}
@keyframes floatC {
  0%, 100% { transform: translate(0, 0) rotate(0deg); }
  50%      { transform: translate(12px, -18px) rotate(5deg); }
}

.hero-shapes-back .shape-a { animation: floatA 12s ease-in-out infinite; }
.hero-shapes-back .shape-b { animation: floatB 16s ease-in-out infinite; }
.hero-shapes-mid  .shape-c { animation: floatC 10s ease-in-out infinite; }
```

### Varied durations + rotations

If all shapes use the same animation, they move in lockstep — feels mechanical. Different durations (10s, 12s, 16s) keep the relationship asynchronous and natural.

`ease-in-out` for the continuous motion — smoother than linear, doesn't have the "snap" of `ease-out`.

## Pattern 5: Scroll Indicator (CSS Bounce)

```css
@keyframes bounce {
  0%, 100% { transform: translateY(0); }
  50%      { transform: translateY(8px); }
}

.scroll-down {
  animation: bounce 2s ease-in-out infinite;
}
```

Subtle, continuous. The chevron points down + bounces 8px every 2 seconds. Stronger bounce (16px+) feels too eager; gentler (4px) is invisible.

## When GSAP vs CSS

| Animation type | Tool | Why |
|---|---|---|
| Page-load entrance | GSAP timeline | Needs precise sequencing + overlap |
| User-triggered (hover, scroll, mouse) | GSAP | Needs to respond to events |
| Continuous ambient | CSS keyframes | GPU-composited, cheaper |
| State transitions (button hover) | CSS transitions | Built-in, no JS needed |
| Complex multi-property orchestration | GSAP timeline | Easier to choreograph |

## Anti-Patterns

- **Skipping gsap.set() initial states** — causes FOUC. The cardinal sin.
- **Using GSAP for continuous ambient motion** — wasteful; CSS handles it cheaper
- **No mobile fallback for mouse parallax** — looks broken on touch devices (which can't fire mousemove meaningfully)
- **Too many entrance animations** — page feels like a demo reel. 5 patterns max per page.
- **Linear easing on entrance** — feels mechanical. Always use power*.out or expo.out.
- **Stagger > 0.2s** — viewer notices waiting; animation feels slow.
- **rotateX > 30°** — gimmicky; feels like a flipbook.
- **Bounce amplitude > 16px** — chevron looks anxious.

## Operational Checklist (Per Generation)

- [ ] All animated elements have `gsap.set()` initial states BEFORE the timeline
- [ ] Hero entrance uses GSAP timeline with overlap timings
- [ ] Mouse parallax disabled on touch devices (`matchMedia("(hover: none)")`)
- [ ] Feature cards use ScrollTrigger.batch with start "top 80%"
- [ ] Floating shapes use CSS keyframes (NOT GSAP)
- [ ] Scroll indicator uses CSS bounce keyframe
- [ ] Easing functions: `power3.out` for entrance, `power2.out` for scroll reveals, `ease-in-out` for CSS floats
- [ ] Stagger times: 0.11s for cards, 0.3s overlap for hero timeline

## Citations (7 sources)

1. **GSAP Documentation — GreenSock.com (ongoing).** Authoritative source for the timeline + ScrollTrigger + easing semantics. https://greensock.com/docs/

2. **Val Head, *Designing Interface Animation* (Rosenfeld, 2016).** The book argues for animation as functional communication, not decoration. The "5 patterns max" discipline derives from her framework.

3. **Rachel Nabors, *Animation at Work* (A Book Apart, 2017).** Covers the "12 principles of animation" applied to UI. The easing choices (power3.out for entrance, power2.out for scroll) follow her recommendations.

4. **Sarah Drasner, *SVG Animations* (O'Reilly, 2017).** Comprehensive on web animation performance. Source for the GSAP-for-interactive / CSS-for-continuous discipline.

5. **GPU-Accelerated CSS — Paul Irish (HTML5 Rocks, 2012, updated).** Foundational article on why CSS transforms are cheaper than JS-driven property changes. Justifies using CSS keyframes for the floating shapes.

6. **Material Design Motion — Google (2014, updated 2024).** Source for "ease decelerated" pattern (= GSAP's power*.out). Material's motion guidelines specify duration ranges (200-500ms for state changes, 400-1000ms for entrance) that the skill mirrors.

7. **WCAG 2.2 — Animation from Interactions (Success Criterion 2.3.3)** — provides guidance on respecting `prefers-reduced-motion`. The skill should respect this in production (gate the entrance + mouse parallax behind `@media (prefers-reduced-motion: no-preference)`); included as a future-improvement note. https://www.w3.org/TR/WCAG22/#animation-from-interactions
