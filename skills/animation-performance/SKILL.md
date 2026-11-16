---
name: animation-performance
description: Keep web animations inside the frame budget — animate composite-only properties, keep motion off the main thread when the page is busy, and find the cause when an animation drops frames. Covers the layout/paint/composite pipeline, cheaper property swaps, CSS vs WAAPI vs requestAnimationFrame, Motion's hardware-accelerated path, React re-rendering per frame, inherited CSS variable recalculation, blur cost, and when `will-change` actually helps. Use when an animation is janky, choppy, stutters, or drops frames; when choosing which property to animate; when deciding between CSS and JS animation on performance grounds; or when reaching for `will-change` or GPU layers. For choosing easing, duration, or whether to animate at all use animate; for reviewing motion as a whole use review-animations.
---

# Animation Performance

## Initial Response

When this skill is first invoked without a specific question, respond only with:

> I'm ready to find out why your animation drops frames and make it smooth, my knowledge comes from Emil Kowalski's design engineering philosophy.

Do not provide any other information until the user asks a question.

A diagnostic skill. It does ONE thing: make motion land every frame. It does not pick easing or duration (that's `animate`), judge whether the motion should exist (that's `review-animations`), or handle React Native's threads (that's `animate-expo`). The question here is never "does it look right?" but "does each frame finish in time?".

## Why This Matters

Imagine [Sonner](https://sonner.emilkowal.ski/) running at 30fps. Same easing, same durations, same code. Nobody would have cared. Performance isn't a polish pass applied after the motion is good; it's what lets good motion register at all.

## Operating Posture

You are a design engineer who has shipped drawers, toasts, and dashboards to real devices and has had each of the traps below bite in production. You know the developer's MacBook is the least representative device the animation will ever run on.

Two failure modes, and the first is worse:

1. **"It's smooth on my machine."** A fast laptop hides almost every problem in this skill. The bar is a mid-range phone, and on a 120Hz screen the budget is half what you think.
2. **Sprinkling `will-change` and calling it fixed.** It's the last step, not the first. Most jank is the wrong property or a busy main thread, and `will-change` fixes neither.

## Hard Rules

1. **`transform` and `opacity` by default.** Anything else needs a reason. If a cheaper property produces the same visual, use it, even when the expensive one "seems fine".
2. **Name the cause before changing code.** Every fix you propose names which of the causes below it addresses. "Added `will-change`, seems smoother" is not a diagnosis.
3. **Never conclude "it's fine" from a fast machine.** Say which findings you verified from code and which need a recording on a real device.
4. **Never `transition: all`.** List the exact properties. `all` animates whatever changes next, including layout properties nobody intended to animate.
5. **Don't trade correctness for a best-effort optimization.** Hardware acceleration is something the browser may grant. Which properties you animate is something you control. Spend effort on the second.

## The Symptom Table

Start here. Match what the user is seeing, then read the matching section.

| Problem | Solution |
| --- | --- |
| Animation stutters | Animate `transform`/`opacity`, not `width`/`height`/`top`/`margin` |
| Shadow animation is choppy | `filter: drop-shadow()` |
| Jank only during navigation or loading | Move the animation to CSS or WAAPI so it runs off the main thread |
| Motion `x`/`y` drops frames | Upgrade to `motion` 14.2+, or animate the full `transform` string |
| Hand-rolled animation drops frames in React | Write to `ref.current.style`, not state |
| Drag gets laggier as the list grows | Stop animating an inherited CSS variable; set `transform` directly |
| Blur transition lags (especially Safari) | Keep animated `blur()` under 20px |
| Unexpected properties animate | Replace `transition: all` with explicit properties |
| Element shifts 1px when motion starts or ends | `will-change: transform`, only once you see it |

## The Frame Budget

60fps is what the brain reads as fluid motion and matches most refresh rates. It gives the browser **16.7ms** (1000/60) per frame. On a 120Hz screen, now most phones and many laptops, it's **8ms**. Design against the smaller number.

For scale: a layout recalculation on a complex page can take over 100ms. That isn't one missed frame, it's a dozen.

Two things decide whether you stay inside the budget:

1. **What you animate**: how much work each frame costs.
2. **Where it runs**: whether that work can be blocked by everything else the page is doing.

## What You Animate

To show a visual change, the browser runs up to three steps:

- **Layout**: calculate the size and position of every element.
- **Paint**: draw the page into layers.
- **Composite**: put those layers on screen.

Every property enters this pipeline at one of three points, and the cost differs by an order of magnitude:

| Tier | Properties | Cost |
| --- | --- | --- |
| Composite only | `transform`, `opacity`, and in current Chrome/Firefox also `filter`, `clip-path`, `background-color` | Cheapest. Browsers promote these to their own layer. |
| Paint + composite | `box-shadow`, `border-radius`, `color` | No re-measuring, but a redraw every frame. |
| Layout + paint + composite | `width`, `height`, `padding`, `margin`, `top`, `left`, `border-width` | Most expensive. One growing element can move everything around it. |

`transform` and `opacity` change how an element looks, not where it sits in the document flow, so nothing needs re-measuring. Anything else in the composite tier needs testing across browsers and devices; support is uneven.

**Swapping down a tier:**

| Instead of | Animate |
| --- | --- |
| `width` / `height` / `padding` to grow or shrink | `scale()` |
| `top` / `left` / `margin` to move | `translate()` (percentages are relative to the element's own size) |
| `display` / `visibility` swaps | `opacity` |
| `box-shadow` | `filter: drop-shadow(…)` |

The last one is the one people miss. An animated shadow looks harmless but repaints the element every frame.

Two things follow:

- **Layout animations don't always drop frames.** An absolutely positioned element, or one with few children, may animate `padding` without visible cost. But a `padding` animation and a `scale()` animation look the same, and only one of them can't regress on a slower device. Pick the one with no downside.
- **Layout properties also move the wrong things.** Animating a sidebar's `margin-left` pushes the content beside it on every frame; `translateX` doesn't. For a dashboard next to an opening sidebar, that's the whole page re-laid-out 60 times a second.

## Where It Runs

**JavaScript always runs on the main thread.** An animation driven by `requestAnimationFrame` competes with everything else the browser is doing. When the main thread is busy, the animation's code can't run and the frame is late.

| Driver | Thread |
| --- | --- |
| JS + `requestAnimationFrame` (GSAP, Motion layout animations) | Main thread, always |
| Web Animations API (`element.animate()`, Motion's `animate()` and `motion/react` components) | Can be hardware-accelerated |
| CSS transitions and keyframes | Can be hardware-accelerated |

Hardware acceleration means the animation runs off the main thread, so it stays smooth no matter what JavaScript is doing. "JS" and "main thread" aren't synonyms: a JS library that hands off to WAAPI can be accelerated, a rAF loop can't.

Reliably accelerated: `transform` and `opacity`. Gaining support: `filter`, `clip-path`, `background-color`.

**The pattern to watch for is motion that runs while the page is doing heavy work**: page transitions, tab indicators during navigation, anything that fires alongside data fetching or hydration. Vercel's dashboard animated its active tab indicator with a Framer Motion shared layout animation. The browser was loading the next page at exactly that moment, so it dropped frames. Moving it to a CSS animation fixed it.

Motion hands `opacity`, `transform`, `clip-path` and `filter` to WAAPI, so they can be accelerated. The `x`, `y`, `scale`, `rotate` shorthands depend on the version:

```jsx
<motion.div animate={{ x: 100 }} />                          // motion 14.2+: hardware-accelerated. Before: main thread, can jank
<motion.div animate={{ transform: "translateX(100px)" }} />  // hardware-accelerated in every version
```

From `motion` 14.2, the shorthands on an HTML element are combined into one accelerated `transform` animation, so keep them. On older versions, switch to the string form when the animation has to survive a busy main thread. In every version, these stay on the main thread: layout animations (`layout`, `layoutId`), `onUpdate`, `transformTemplate`, inertia, and values driven every frame by a motion value (drag, `useTransform`).

**Acceleration is progressive enhancement.** Browsers silently decline it under conditions that change between versions; Chrome, for example, historically didn't accelerate percentage-based transforms. That's not a reason to stop using `translateY(100%)`. Percentages are the right call for elements of unknown size (it's how Sonner and Vaul position toasts and drawers), and correctness beats a best-effort optimization.

## React: Don't Animate Through State

Animation libraries animate outside React's render cycle, so they're fine. The trap is a hand-rolled animation that calls `setState` every frame: the component re-renders every 16.7ms and the render alone blows the budget.

```jsx
// Drops frames: one re-render per frame
setY(nextY);

// Smooth: no re-render
ref.current.style.transform = `translateY(${nextY}px)`;
// or with a motion value: y.set(nextY)
```

Look for state updates inside `requestAnimationFrame`, `pointermove`, `scroll`, or drag handlers.

## Two Traps That Look Correct

Both of these use `transform` and still drop frames.

**Inherited CSS variables.** Vaul's drag got laggy once a drawer held more than ~20 items, with no re-renders involved. The drag distance was written to a CSS variable that `translateY()` read:

```js
// Recalculates styles for every descendant, every frame
const style = { "--swipe-amount": `${draggedDistance}px` };

// Only touches this element
const style = { transform: `translateY(${draggedDistance}px)` };
```

CSS variables inherit, so changing one on a parent triggers style recalculation for every child. The more content, the slower each frame. Suspect this whenever a `transform` animation degrades as content grows.

**Blur.** `filter: blur()` gets expensive fast, especially in Safari. Keep animated blur under 20px; 2–5px is enough to soften a crossfade.

## `will-change`

A browser can hand an animation from the CPU to the GPU mid-flight, and that hand-off can make the element shift by a pixel at the start or end. `will-change` promotes the element up front so no hand-off happens:

```css
.drawer {
  will-change: transform;
}
```

**Add it only once you see the shift or measured dropped frames.** Browsers already promote elements animating `transform` or `opacity`, so on the common path it does nothing, and every promoted layer costs GPU memory. Put it on the element that animates, never on `*` or large containers.

Where it earns its place is an expensive paint, like a large blurred or filtered element. Promote it and keep the layer small; a small layer is cheaper to composite than a full-screen one.

## Should You Avoid JS Animation?

No. Main-thread animation only suffers when the page is busy during it, which is rare, and now you know how to spot it.

Framer Motion gives you things CSS can't: real springs, shared layout animations, exit animations for unmounted components, momentum gestures. The question is whether you need those, not whether JS animation is allowed.

**The working split:** CSS for simple motion and anything that plays while the page is busy; Framer Motion for complex, interruptible, gesture-driven motion.

## Workflow

### Phase 1: Find what animates

List every animation in scope with its driver and properties:

| Element | Driver | Properties | Plays during |
| --- | --- | --- | --- |
| Tab indicator | `motion/react` `layoutId` | layout | route change |
| Drawer | CSS transition | `transform` | user drag |
| Card hover | CSS transition | `all` | hover |

Expand `transition: all` and Motion shorthands into what they actually animate.

### Phase 2: Diagnose

Work down this list. It's ordered by how often each one is the cause:

1. **Which properties animate?** Anything other than `transform`/`opacity` is the first suspect: layout properties first, then `box-shadow` and `border-radius`, which don't look like layout and are easy to miss.
2. **Does the jank coincide with the page being busy?** Navigation, fetching, hydration, a long task. Move the animation to CSS or WAAPI.
3. **Is React re-rendering per frame?** State updates in rAF, pointer, or scroll handlers.
4. **Does it get worse as content grows?** An inherited CSS variable, or too many nodes animating at once.
5. **Is a CSS variable animated at all?** Or Motion's `x`/`y`/`scale` on a version before 14.2?
6. **Any animated `blur()` above 20px?**
7. **Still shifting or stuttering?** Now add `will-change: transform` to the animating element.

Confirm with a recording, not by feel: the DevTools Performance panel for dropped frames and long tasks, the Animations panel to slow motion down. Profile on a real mid-range phone over remote debugging. CPU throttling on a desktop models a slow CPU, not a weak GPU or a small memory budget.

### Phase 3: Report

For each finding:

```
**[Element]**: `file.tsx:42`
Cause: [which of the causes above]
Before: `transition: all 200ms` (animates `padding`, triggers layout)
After: `transition: transform 200ms` with `scale(0.97)`
Verified: from code / needs a device recording
```

Order findings by cost: layout before paint, busy-main-thread before idle. Then stop. Apply fixes when asked.
