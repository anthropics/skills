# Choreography Recipes

Copy-ready patterns for the relationships in [SKILL.md](SKILL.md). The values are starting points, so tune them on a recording.

## Overlap: CSS stagger with an index variable

For one-shot entrances (a hero, a personal site intro). The delay is computed per element from a custom property, so you don't need one class per item.

```tsx
<div className="stagger">
  <h1 style={{ "--i": 0 }}>Title</h1>
  <p style={{ "--i": 0 }}>First paragraph, same beat as the title</p>
  <p style={{ "--i": 1 }}>Supporting paragraph</p>
  <div style={{ "--i": 2 }}>CTAs</div>
</div>
```

```css
.stagger > * {
  --step: 120ms;
  animation: enter 0.6s ease both;
  animation-delay: calc(var(--step) * var(--i));
}

@keyframes enter {
  from {
    opacity: 0;
    transform: translateY(10px);
  }
}

@media (prefers-reduced-motion: reduce) {
  .stagger > * {
    animation-name: fade;
    animation-delay: 0ms;
  }
  @keyframes fade {
    from { opacity: 0; }
  }
}
```

- `both` is required. `backwards` applies the first keyframe during the delay, so later items don't flash their final state before they animate. `forwards` keeps the end state.
- Omitting `to` makes the keyframe animate to the element's own styles.
- Changing a custom property on a parent recalculates styles for every descendant. That's fine for a one-shot entrance, but don't drive per-frame values (a drag) through an inherited variable on a large tree.

## Overlap: Motion variants with a non-uniform stagger

```tsx
import { motion, stagger } from "motion/react";

const list = {
  hidden: {},
  show: {
    transition: {
      // Delays shrink as the group goes on, so it reads as a wave, not a metronome
      delayChildren: stagger(0.06, { ease: "easeOut" }),
    },
  },
};

const lead = {
  hidden: { opacity: 0, y: 12 },
  show: { opacity: 1, y: 0, transition: { duration: 0.5, ease: [0.23, 1, 0.32, 1] } },
};

const support = {
  hidden: { opacity: 0, y: 6 },
  show: { opacity: 1, y: 0, transition: { duration: 0.4, ease: [0.23, 1, 0.32, 1] } },
};

const decoration = {
  hidden: { opacity: 0 },
  show: { opacity: 1, transition: { duration: 0.3 } },
};

<motion.section variants={list} initial="hidden" animate="show">
  <motion.span variants={decoration}>New</motion.span>
  <motion.h1 variants={lead}>Title</motion.h1>
  <motion.p variants={support}>Subtitle</motion.p>
  <motion.div variants={support}>CTAs</motion.div>
</motion.section>
```

- Each role gets its own variant (distance, duration). The stagger only sets *when* each one starts.
- `stagger(0.05, { from: "center" })` radiates out from the middle. Use a number index to radiate from the item the user interacted with.
- Older Motion versions use `staggerChildren: 0.06` instead of `delayChildren: stagger(...)`.
- For long lists, give items beyond the first ~6 the same delay as the 6th, so the group never takes longer than ~300ms.

## Together: remove the exiting element from the flow

Siblings close the gap *while* the removed item fades, not after.

```tsx
<ul>
  <AnimatePresence mode="popLayout" initial={false}>
    {chips.map((chip) => (
      <motion.li
        key={chip.id}
        layout
        exit={{ opacity: 0, scale: 0.95 }}
        transition={{ duration: 0.2, ease: [0.23, 1, 0.32, 1] }}
      >
        {chip.label}
      </motion.li>
    ))}
  </AnimatePresence>
</ul>
```

Without a library: before running the exit, read the element's offset, set `position: absolute` with that `top`/`left` on it (the parent needs `position: relative`), then animate it out. Animate the siblings with FLIP or let them reflow.

## Together: crossfade views in a resizing container

The container's height and the content swap are one object: same duration, same easing family.

```tsx
import useMeasure from "react-use-measure";

const [ref, bounds] = useMeasure();
const prevHeight = useRef<number>();

// The fade duration scales with how far the container moves
const fadeDuration = useMemo(() => {
  const MIN = 0.15;
  const MAX = 0.27;
  if (!prevHeight.current) {
    prevHeight.current = bounds.height;
    return MIN;
  }
  const delta = Math.abs(bounds.height - prevHeight.current);
  prevHeight.current = bounds.height;
  return Math.min(Math.max(delta / 500, MIN), MAX);
}, [bounds.height]);

<motion.div
  animate={{ height: bounds.height }}
  transition={{ duration: 0.27, ease: [0.25, 1, 0.5, 1] }}
  style={{ overflow: "hidden" }}
>
  <div ref={ref}>
    <AnimatePresence initial={false} mode="popLayout">
      <motion.div
        key={view}
        initial={{ opacity: 0, scale: 0.96 }}
        animate={{ opacity: 1, scale: 1 }}
        exit={{ opacity: 0, scale: 0.96 }}
        transition={{ duration: fadeDuration, ease: [0.26, 0.08, 0.25, 1] }}
      >
        {content}
      </motion.div>
    </AnimatePresence>
  </div>
</motion.div>
```

- The height uses a strong `ease-out`, and the content uses a lighter curve from the same family, so the swap stays visible without falling out of sync.
- `key` on the child is what tells `AnimatePresence` a view left. A missing key is the first thing to check when an exit doesn't play.
- If the container is part of a larger component (a drawer), bring that component's own open duration in line with this one so the whole thing feels like one entity.

## Direction-aware steps

```tsx
const [[step, direction], setStep] = useState([0, 0]);
const go = (d: 1 | -1) => setStep(([s]) => [s + d, d]);

const variants = {
  initial: (d: number) => ({ x: `${110 * d}%`, opacity: 0 }),
  active: { x: "0%", opacity: 1 },
  exit: (d: number) => ({ x: `${-110 * d}%`, opacity: 0 }),
};

<MotionConfig transition={{ type: "spring", duration: 0.5, bounce: 0 }}>
  <AnimatePresence mode="popLayout" initial={false} custom={direction}>
    <motion.div
      key={step}
      custom={direction}
      variants={variants}
      initial="initial"
      animate="active"
      exit="exit"
    >
      {content}
    </motion.div>
  </AnimatePresence>
  <motion.div layout>{/* Back / Continue follow the height change */}</motion.div>
</MotionConfig>
```

`custom` goes on **both** `AnimatePresence` and the child. The exiting child reads the latest direction from `AnimatePresence`. Without that, it uses the direction it had when it mounted.

For small containers or similar views, swap the 110% slide for a crossfade with an 8px shift and a light blur. The eyes barely move and the change still reads.

## Sequence: one draw after another

```css
.square {
  animation: draw 0.6s cubic-bezier(0.645, 0.045, 0.355, 1) forwards;
}

.checkmark {
  animation: draw 0.4s cubic-bezier(0.645, 0.045, 0.355, 1) forwards;
  animation-delay: 0.6s; /* = the square's duration */
}

@keyframes draw {
  to { stroke-dashoffset: 0; }
}
```

With `pathLength="100"` on both paths, `stroke-dasharray: 100; stroke-dashoffset: 100` hides each one with round numbers. To make the handoff read as one gesture, start the checkmark slightly before the square finishes (e.g. 0.5s).

## Sequence: morph between two rich states with a crossfade

`mode="wait"` is the safe default when a container changes width *and* height between dense views. To keep a crossfade anyway:

1. Render the active view twice. Copy A animates only the **enter**. Copy B is `position: absolute`, sits at `opacity: 0`, and only becomes visible while **exiting**: its exit is a keyframe that starts at `opacity: 1` and fades out.
2. Give the exiting copy its own transform depending on where the container is going. Scale it up if the next state is larger and down if it's smaller, with `scaleX` pulling it toward the center when the container narrows so it doesn't bleed out of the edges.
3. With a handful of states, hardcode these values (and the spring bounce) per state pair, and pass them through `custom`. Smaller states get more bounce.

## Carry: steer a shared layout animation through its parent

You can't customize the path a `layoutId` animation takes, but you can move the container it lands in.

```tsx
<motion.div
  animate={{ y: 73 }}
  transition={{ delay: 0.13, duration: 0.3, ease: [0.23, 1, 0.32, 1] }}
>
  {selected.map((img) => (
    <motion.img key={img.id} layoutId={img.id} src={img.src} />
  ))}
</motion.div>
```

The images morph into the bin *and* drop with it. Show the bin's front face with a delay timed to when the images have almost landed, so they never visibly pass through it.

## Imperative orchestration (`useAnimate`)

Use this only when several elements coordinate across several events and you need to await completion.

```tsx
const [scope, animate] = useAnimate();
const running = useRef<ReturnType<typeof animate>[]>([]);
const ready = useRef(false); // a flag that never renders, so no useState

function play(steps: ReturnType<typeof animate>[]) {
  running.current.forEach((a) => a.stop()); // never stack sequences
  running.current = steps;
  return Promise.all(steps);
}

const onEnter = async () => {
  ready.current = false;
  await play([
    animate("[data-animate='icon']", { y: -4 }, { duration: 0.3 }),
    ...[...scope.current.querySelectorAll("[data-animate='line']")].map((el, i) =>
      animate(
        el,
        { strokeDashoffset: [1.05, 0] },
        { duration: 0.5, times: [0.7, 0.9], delay: i === 1 ? 0 : 0.04 },
      ),
    ),
  ]);
  ready.current = true;
};

const onClick = () => {
  if (!ready.current) return;
  // A repeat action skips the buildup: the same proportions, earlier in the timeline
  play([animate("[data-animate='bg']", { scale: [1, 0.96, 1.02, 1] }, { duration: 0.4 })]);
};

const onLeave = async () => {
  await play([/* reset every element */]);
  startIdle(); // only once the reset has finished
};

function startIdle() {
  // Tracked in `running`, so the next onEnter stops the loop
  running.current = [
    animate("[data-animate='icon']", { y: [0, -3, 0] }, {
      delay: 2.5,
      repeat: Infinity,
      repeatDelay: 6,
    }),
  ];
}
```

- Target elements with `data-animate` selectors inside `scope` instead of keeping a ref per element.
- Await `Promise.all` when the durations differ. Awaiting just one animation is only safe when they all share a duration.
