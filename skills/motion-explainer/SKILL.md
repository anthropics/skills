---
name: motion-explainer
description: Create animated, step-by-step visual explanations of concepts using p5.js — math, physics, CS, chemistry, or any system with a structure worth revealing. Like 3Blue1Brown but buildable from a prompt. Use this when users ask to "explain", "visualize", "animate", or "walk through" any concept; when they want to understand something deeply rather than just see it; or when they want to build an interactive educational explainer or animated breakdown.
license: Complete terms in LICENSE.txt
---
 
Motion explainers are animated visual narratives. They do not show data — they reveal understanding. Each frame is earned. Each animation is a word in the argument.
 
This unfolds in two steps:
1. **Explanation Narrative** — the intellectual architecture of the explainer
2. **Animated Implementation** — p5.js scenes that embody that architecture
 
---
 
## STEP 1: EXPLANATION NARRATIVE
 
Before a single line of code, create the **Explanation Narrative** — a structured plan for *how understanding will be built*, scene by scene.
 
### THE CORE QUESTION
 
Ask: **What is the single insight that makes this concept click?**
 
Not the definition. Not the formula. The *moment* — the pivot where confusion becomes clarity. That moment is the climax of your explainer. Build toward it.
 
Everything before it is scaffolding. Everything after it is consequence.
 
### THE NARRATIVE ARC
 
A great explainer follows an emotional and intellectual arc:
 
```
Confusion → Intuition → Formalism → Consequence
```
 
- **Confusion**: Show what's strange or counterintuitive about the concept. Start with the question, not the answer. Let the viewer feel the gap.
- **Intuition**: Introduce the simplest possible visual that makes the core mechanism visible. No equations yet. Just the shape of the idea.
- **Formalism**: Now that the intuition lives in the viewer's mind, layer in the structure — notation, relationships, definitions. They will stick now.
- **Consequence**: Show what this unlocks. A surprising result. An application. The "why it matters." Leave the viewer richer than you found them.
 
### HOW TO WRITE THE NARRATIVE
 
**Name the concept clearly** — state exactly what will be explained, stripped to its essence.
 
**Identify the core insight** — the single sentence that, if understood, makes everything else follow. This is your north star.
 
**Design the scenes** (typically 3–7):
- Each scene = one idea, one visual, one beat of understanding
- A scene should end only when its insight is complete, not before
- Scene titles should be revelation-shaped: not "Definition" but "Why the definition exists"
- Sequence scenes so each one *creates the need* for the next
 
**Identify the visual metaphors**:
- What physical thing does this concept *behave like*?
- What can be drawn, moved, and traced that makes the abstract concrete?
- Fourier → rotating circles. Gradient descent → ball rolling downhill. Recursion → mirror facing mirror. Find yours.
 
**Define the color language**:
- Each distinct concept gets its own color. Assign them once, use them always.
- The viewer's eye learns: "orange is always X." Consistency IS comprehension.
- Use the Anthropic palette (primary orange, steel blue, sage green) as your starting point.
 
**Write the narrative** (4–6 paragraphs):
- Describe the arc from confusion to consequence
- Describe each scene's visual metaphor and what it reveals
- Describe how transitions between scenes carry the argument forward
- Emphasize: the animation must feel *inevitable* in retrospect — every element earned its place
 
**CRITICAL GUIDELINES:**
- Avoid narrating facts; narrate *revelations*
- Each scene must be more understandable than text alone would be — if a scene is better as a sentence, cut it
- Repeat this principle: the implementation must feel like it was refined by someone who has explained this concept a hundred times, each time finding a cleaner path to the "aha"
- The animation timing (how long each beat takes) is part of the argument — too fast loses the viewer, too slow loses the thread
 
Output the Explanation Narrative as a `.md` file before writing any code.
 
---
 
## NARRATIVE EXAMPLES
 
**"How Fourier Transforms Work"**
Core insight: any signal is secretly a sum of spinning circles. Visual metaphor: literal circles rotating on the canvas, their endpoints tracing the signal. Arc: start with a mystery (strange wave) → simplest case (one circle = one sine) → add circles → full reconstruction → generalise to arbitrary waveform. Color: each frequency gets its own color; the reconstructed signal is always white.
 
**"Why e^iπ + 1 = 0"**
Core insight: e^it is a point moving around the unit circle in the complex plane. Visual metaphor: the complex plane as canvas; a rotating arm of length 1; πt as the angle. Arc: real numbers on a line → complex plane introduced → e^x as a stretching operation → e^it as a rotating operation → π as the half-turn → +1 brings us back to zero. Every scene is one geometric fact.
 
**"How Gradient Descent Finds Minima"**
Core insight: follow the slope downhill. Visual metaphor: a ball rolling on a surface; the surface is a loss landscape in 2D. Arc: the problem (which point is lowest?) → naive search fails → what if we could feel the slope? → gradient as direction of steepest ascent → descent = negate it → learning rate as step size → convergence → local vs. global minima as a gotcha.
 
**"SN2 Reaction Mechanism"** *(using MechLang visuals)*
Core insight: the nucleophile attacks from the back, forcing an inversion. Visual metaphor: animate the incoming nucleophile, show the trigonal bipyramidal transition state, show the inversion like an umbrella flipping inside-out. Arc: the bond that must break → the nucleophile that wants to form a new bond → the geometry of attack → the transition state → the product and its inversion. Color: nucleophile = orange, leaving group = blue, carbon = dark.
 
*These are condensed examples. The actual narrative should be 4–6 substantial paragraphs.*
 
---
 
## STEP 2: P5.JS IMPLEMENTATION
 
### ⚠️ STEP 0: READ THE TEMPLATE FIRST ⚠️
 
**CRITICAL — before writing any HTML:**
 
1. **Read** `templates/viewer.html` using the Read tool
2. **Read** `templates/generator_template.js` for animation patterns and primitives
3. **Use `viewer.html` as the LITERAL STARTING POINT** — not inspiration
4. **Keep all FIXED sections exactly** (layout, branding, playback controls, scene list, actions)
5. **Replace only the VARIABLE sections** (scenes array, draw functions, concept metadata)
 
**Avoid:**
- ❌ Rebuilding the HTML from scratch
- ❌ Inventing custom layout or color schemes
- ❌ Removing playback controls or scene navigation
- ❌ Creating separate JS files — everything is inline
 
**Follow:**
- ✅ Copy the template's exact HTML structure
- ✅ Keep Anthropic branding (Poppins/Lora, light palette, orange accents)
- ✅ Maintain sidebar order: Concept Info → Scene List → Playback → Actions
- ✅ Replace only the `scenes` array and everything inside it
 
---
 
### SCENE SYSTEM
 
Each scene is an object with three fields:
 
```javascript
{
    title: "Why the formula exists",    // Short, revelation-shaped name
    duration: 5,                        // Seconds
    draw(t) {                           // t = 0.0 → 1.0 over duration
        // Your animation logic here
        // t is the only clock you need
    }
}
```
 
**t is everything.** At `t = 0`, the scene just started. At `t = 1`, it's complete. All motion is derived from t. Nothing is frame-counted manually.
 
Use `Ease.gate(t, start, window)` to stagger elements:
 
```javascript
// This element starts appearing at t=0.3 and fully appears by t=0.6
const alpha = Ease.gate(t, 0.3, 0.3) * 255;
fill(20, 20, 19, alpha);
text("This appears later", x, y);
```
 
---
 
### ANIMATION PRINCIPLES
 
**One concept per scene.** If you're tempted to show two things at once, make two scenes.
 
**Make the motion itself explanatory.** Don't animate just for beauty — animate because *the movement IS the explanation*. An arrow that traces a path teaches differently than an arrow that appears all at once.
 
**Use `drawPartialPath` to trace trajectories** as t increases. The viewer's eye follows the path as it's drawn — they understand the trajectory *while it happens*.
 
**Use `drawArrow` for connections.** When two things are related, show the relation as a directed arrow that fades in at the right moment. The timing of appearance IS the argument.
 
**Typewriter text for equations.** Don't reveal an equation all at once — reveal it as a statement being made. Use `typewriter(text, t)`.
 
**Color encodes meaning.** If orange means "the nucleophile" in scene 1, it means the nucleophile in every scene. Never use a color for decoration.
 
---
 
### TYPOGRAPHY
 
Always use the two typefaces from the template:
- `Lora, serif` — concept titles, emotional beats, the "voice" of the explainer
- `Poppins, sans-serif` — labels, annotations, UI, the "hand" pointing at things
- `Courier New, monospace` — equations, code, precise notation
 
Use `Typography` helpers from `generator_template.js`:
```javascript
Typography.headline("The core insight", width/2, 80, alpha);  // Big reveal text
Typography.annotation("this is the slope", x + 20, y, P.primary, alpha); // Callout
Typography.math("f(x) = e^(ix)", width/2, height/2, 22, alpha); // Equation
```
 
---
 
### COORDINATE SYSTEMS
 
For mathematical concepts, establish a coordinate system immediately:
 
```javascript
const cs = new CoordinateSystem(width/2, height/2, 80); // origin at center, 80px/unit
cs.drawAxes([-5, 5], [-4, 4]); // draw x and y axes
cs.plotFunction(x => Math.sin(x), -5, 5, P.primary); // plot sin(x) in orange
const [sx, sy] = cs.toScreen(1, 0); // convert (1,0) world → canvas
```
 
This keeps your math in real units and your rendering clean.
 
---
 
### CRAFTSMANSHIP
 
The final implementation should feel like it was refined through *countless iterations* by someone who has thought deeply about this concept. Every timing choice should be intentional. Every color assignment should be consistent. Every easing curve should match the mood of the transition.
 
- A discovery should arrive with `Ease.outElastic` — something clicking into place
- A slow accumulation should use `Ease.inOut` — the workhorse of understanding
- A sudden reveal should use a sharp threshold gate — no easing, just presence
 
The animation timing *is* the argument. Respect it.
 
---
 
### OUTPUT FORMAT
 
Output:
1. **Explanation Narrative** — as a `.md` file, 4–6 paragraphs
2. **Single HTML Artifact** — self-contained, built from `templates/viewer.html`
 
The HTML artifact contains everything inline. It runs immediately in claude.ai or any browser. No server, no build step, no external dependencies except p5.js from CDN.
 
---
 
## WHAT'S FIXED vs VARIABLE
 
**FIXED** (copy exactly from template):
- HTML layout: sidebar, canvas area, overlay
- Anthropic branding: colors, fonts, gradients, shadows
- Scene list rendering (auto-generated from `scenes` array)
- Playback controls: play/pause, prev/next, speed, scrubber
- Actions: Restart, Save frame
- All UI handler functions at the bottom of the script
 
**VARIABLE** (replace for each explainer):
- `CONCEPT_TITLE` and `CONCEPT_SUBTITLE`
- The `scenes` array — titles, durations, draw functions
- The `P` palette (if customizing beyond Anthropic defaults)
- Any helper classes or precomputed data specific to the concept
 
---
 
## RESOURCES
 
- **`templates/viewer.html`** — REQUIRED starting point. Contains the full UI shell. Replace only the variable sections.
- **`templates/generator_template.js`** — Animation primitives: `Ease`, `Scene`, `CoordinateSystem`, `Typography`, `drawArrow`, `drawPartialPath`, `drawLabel`, `drawHighlight`, `typewriter`, `fadeIn`. Reference these before implementing.
 
**Critical reminder**:
- The template is the *foundation*, not inspiration
- The scenes array is where creativity lives
- The explanation narrative drives every implementation decision
- The animation's job is to make one thing true: the viewer understands something they didn't before
 
