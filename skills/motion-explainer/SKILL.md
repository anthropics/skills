---
name: motion-explainer
description: Create animated, step-by-step visual explanations of concepts using p5.js — math, physics, CS, chemistry, or any system with a structure worth revealing. Use this when users ask to explain, visualize, animate, or walk through a concept; when they need an interactive educational explainer; or when a concept benefits from motion, prediction pauses, parameter sliders, misconception callouts, math rendering, or 2D/3D visual scaffolding.
license: Complete terms in LICENSE.txt
---

# Motion Explainer

Motion explainers are animated visual narratives. They reveal understanding through motion: every scene is one beat, every transition is part of the argument, and every color carries meaning.

Deliverables:
1. **Explanation Narrative** — a `.md` file, 4–6 paragraphs.
2. **Single HTML Artifact** — based on `templates/viewer.html`, self-contained except for CDN dependencies: p5.js, Google Fonts, and KaTeX.

## Required workflow

### 1. Write the explanation narrative first

Before code, identify:
- **Concept** — exactly what is being explained.
- **Core insight** — the one sentence that makes the concept click.
- **Arc** — Confusion → Intuition → Formalism → Consequence.
- **Scenes** — usually 3–7; one idea per scene.
- **Visual metaphors** — concrete things that move, split, combine, trace, or transform.
- **Color language** — assign one meaning per color and keep it consistent.
- **Interactions** — add prediction pauses or sliders only where they deepen understanding.
- **Misconceptions** — explicitly show common wrong ideas when useful.

Output the narrative as Markdown before creating the HTML.

### 2. Build from the template

1. Read `templates/viewer.html`.
2. Use it as the literal starting point.
3. Replace only the **Variable Section**:
   - `CONCEPT_TITLE`
   - `CONCEPT_SUBTITLE`
   - `CONCEPT_RENDERER`
   - `P` palette, if needed
   - `CONCEPT_PARAMS`
   - concept-specific helper data/functions
   - `scenes`
4. Keep the fixed viewer runtime, controls, layout, and standard library intact unless the user explicitly asks for template development.

## Scene model

Each scene is an object:

```javascript
{
  title: "Why the formula exists",
  duration: 6,             // seconds
  type: "normal",          // optional: normal | interaction | misconception
  transition: "fade",      // optional fade in/out
  onEnter(params) {},       // optional one-time setup for expensive data
  onExit() {},              // optional cleanup
  onParamChange(params) {}, // optional response to slider changes
  draw(t) {                 // t runs from 0 → 1
    // render one explanatory beat
  }
}
```

Use `t` as the only clock. Use `Ease.gate(t, start, window)` for staged reveals and pauses inside a scene.

## Built-in features in `viewer.html`

The template includes:
- Responsive p5 canvas with 2D or WEBGL renderer.
- Playback controls: play/pause, prev/next, 0.25×/0.5×/1×/2×/4× speed, scrubber.
- Correct fractional-speed playback.
- Keyboard shortcuts: Space, ←, →, R, L.
- Loop toggle.
- Per-scene and global progress indicators.
- Scene list with type tags.
- Restart and Save Frame actions.
- Font-load guard to avoid first-frame font flash.
- KaTeX overlay for real math notation.
- Pooled math labels to avoid per-frame DOM churn.
- Interaction scenes with pause-and-predict overlay.
- Misconception scenes with badge and red emphasis.
- `onEnter` / `onExit` hooks for complex precomputation.
- Optional parameter sliders via `CONCEPT_PARAMS`.

## Standard library

Available directly in `viewer.html`:

### Animation
```javascript
Ease.inOut(t)
Ease.out(t)
Ease.in(t)
Ease.outBounce(t)
Ease.outElastic(t)
Ease.gate(t, start, window)
animate(a, b, t, easeFn = Ease.inOut)
fadeIn(t, start, end)
typewriter(text, t)
```

### Drawing primitives
```javascript
drawPartialPath(points, t, weight, color)
drawArrow(x1, y1, x2, y2, color, weight, headSize)
drawLabel(x, y, text, { size, col, bg, alpha, align, weight })
drawHighlight(x, y, w, h, color, alpha, radius)
```

These helpers preserve p5 drawing state with `push()` / `pop()`.

### Coordinates
```javascript
const cs = new CoordinateSystem(width/2, height/2, 80);
cs.drawAxes([-5, 5], [-4, 4]);
cs.plotFunction(x => Math.sin(x), -5, 5, P.primary);
const [sx, sy] = cs.toScreen(1, 0);
```

`plotFunction` skips non-finite values, so discontinuities such as `1/x` do not create spikes.

### Typography
```javascript
Typography.headline("The core insight", width/2, 80, alpha);
Typography.stepLabel("Step 2 of 5", width/2, 45, alpha);
Typography.annotation("this is the slope", x + 20, y, P.primary, alpha);
Typography.math("f(x) = e^(ix)", width/2, height/2, 22, alpha);
```

### KaTeX math labels

Use `mathLabel(latex, x, y, opts)` for proper fractions, binomials, integrals, and aligned formulas:

```javascript
mathLabel('\\binom{k+n-1}{n-1}', width/2, 120, { size: 28, alpha: 255 });
```

Call `clearMathLabels()` only if you write custom render loops outside the template. The standard `draw()` already clears and pools labels each frame.

## Interaction scenes

Use interaction scenes to make the viewer predict before the reveal:

```javascript
{
  title: "Predict the next step",
  type: "interaction",
  pauseAt: 0.45,
  questionTitle: "Pause and predict",
  question: "Where should the next bar go?",
  draw(t) {
    // draw setup before pause, reveal after Continue
  }
}
```

The scene pauses once at `pauseAt`; Continue marks the scene as interacted and resumes playback. Scrubbing past `pauseAt` also marks it interacted to avoid repeated overlays.

## Misconception scenes

Use misconception scenes to show a tempting but wrong mental model:

```javascript
{
  title: "The tempting wrong count",
  type: "misconception",
  duration: 5,
  draw(t) {
    // contrast wrong idea with the correction
  }
}
```

The viewer adds a warning badge and red emphasis automatically.

## Parameter sliders

Expose live parameters in the sidebar:

```javascript
const CONCEPT_PARAMS = {
  k: { label: 'Objects', min: 1, max: 20, step: 1, value: 5 },
  n: { label: 'Boxes', min: 2, max: 8, step: 1, value: 3 }
};
```

Read them as `params.k` and `params.n` in `draw(t)` or `onEnter(params)`. Use `onParamChange(params)` if cached data must be recomputed after slider changes.

## Complex visualizations

For complex work:
- Use `onEnter(params)` for expensive precomputation: graph layouts, Fourier coefficients, particle initial states, simulation traces.
- Keep `draw(t)` deterministic and cheap; it should render cached state, not recompute it.
- Use sliders for the few parameters that change the learner's intuition.
- Use `CONCEPT_RENDERER = 'webgl'` only when the concept truly needs 3D, shaders, or GPU-style particle work.
- In WEBGL mode, account for p5's centered coordinate system and avoid relying on 2D screen-space assumptions without testing.

## Honest limitations

This skill is strongest for concepts that can be made spatial, temporal, or structural. It is weaker for:
- concepts with no useful visual metaphor,
- very long derivations that become slide decks,
- dense symbolic proofs unless paired with careful KaTeX pacing,
- audio-first topics unless you manually add p5.sound or another audio layer,
- massive graph/network views that exceed the canvas,
- production-grade 3D scenes requiring full camera, lighting, and asset pipelines.

If a concept is mostly symbolic, use a hybrid mode: small visuals plus KaTeX derivation steps. If it is mostly conceptual, prioritize misconception and prediction scenes over decorative animation.

## Craft principles

- One concept per scene.
- Motion must explain, not decorate.
- Use consistent colors for consistent meanings.
- Reveal formulas as consequences of the picture, not as magic.
- Prefer 3–7 excellent scenes over 12 thin scenes.
- Every beat should feel inevitable in retrospect.
