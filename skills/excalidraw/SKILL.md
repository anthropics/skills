---
name: excalidraw
description: Generate hand-drawn style diagrams using Excalidraw. Accepts natural language descriptions, generates Excalidraw scene JSON, and renders to PNG/SVG via headless Playwright. Use when user asks for diagrams, architecture charts, flowcharts, or visual illustrations.
dependencies:
  - Node.js >= 18
  - "@playwright/test"
  - Chromium (installed via Playwright)
allowed-tools:
  - Bash
  - Read
  - Write
  - Edit
  - Glob
---

# Excalidraw Diagram Generator

Generate hand-drawn style diagrams programmatically using Excalidraw's rendering engine.

## Configuration

| Setting | Default | Description |
|---------|---------|-------------|
| Output directory | `diagrams/` | Where `.excalidraw` and rendered files are saved |

> Adjust the output directory to match your project structure. Common choices:
> `docs/diagrams/`, `assets/diagrams/`, `static/images/diagrams/`

## Workflow

```
User describes diagram
  → Step 0: Design Phase — determine visual style (+ style review)
  → Step 1: Claude generates .excalidraw JSON following the style brief
  → Step 2: render.mjs → PNG
  → Step 3: Review the rendered image (scoring + iteration)
  → Step 4: Fix issues and re-render (loop until approved)
  → Done: Final PNG/SVG output
```

### Step 0: Design Phase (Recommended)

Before writing any JSON, you **SHOULD** first determine the visual style. This prevents the common failure of jumping straight to coordinates without thinking about what makes the diagram effective.

**If oh-my-claudecode is installed**, spawn an `oh-my-claudecode:architect` agent as a design consultant with the prompt below. **Otherwise**, perform this design thinking yourself before writing any JSON.

**Design consultant prompt template:**

```
You are a visual communication designer. Before I create an Excalidraw diagram, help me determine the visual style.

Context:
- Article/post topic: [e.g., "How to use CLAUDE.md to make AI code match team standards"]
- Diagram purpose: [e.g., "Twitter cover image showing before/after code quality comparison"]
- Target platform: [e.g., "Twitter feed, 16:9, must be readable at 500px wide thumbnail"]
- Target audience: [e.g., "Frontend developers, tech leads"]

Decide on:

1. **Visual Metaphor** — What real-world analogy best communicates this concept?
   (e.g., "blueprint vs sketch", "filter/funnel", "bridge between two worlds", "before/after transformation")

2. **Layout Strategy** — Which layout pattern fits?
   - Left-to-right flow (transformation, process)
   - Top-to-bottom hierarchy (layers, architecture)
   - Center-out radial (hub-and-spoke, ecosystem)
   - Split comparison (vs, before/after)
   - Single focal point (hero concept with annotations)

3. **Information Density** — How much text should be on the image?
   - Minimal (3-5 words max, icon-driven, for social media thumbnails)
   - Light (short labels + one key data point)
   - Medium (bullet points inside boxes, for blog posts)
   - Dense (detailed architecture, for documentation)

4. **Tone** — What feeling should the diagram convey?
   - Technical precision (clean lines, code font, structured)
   - Casual/approachable (hand-drawn, playful, loose)
   - Authoritative/professional (bold, minimal, high contrast)
   - Educational (annotated, step-by-step, guided)

5. **Color Strategy** — Within the monochrome-first constraint:
   - Pure monochrome (black strokes, transparent/light gray fills, no accent)
   - Monochrome + single accent (black + one purple/blue highlight for the key concept)
   - Semantic pair (black strokes + two meaningful background colors, e.g., light red vs light green for comparison)

Output a **Style Brief** in this exact format:

---
STYLE BRIEF
Metaphor: [one line]
Layout: [pattern name]
Density: [level]
Tone: [one line]
Colors: [strategy + specific hex codes to use]
Key visual element: [the ONE thing that should catch the eye first]
Anti-patterns to avoid: [what would make this diagram look bad]
---
```

**Style Review (adversarial):**

After producing the Style Brief, review it critically. **If oh-my-claudecode is installed**, spawn a `oh-my-claudecode:critic` agent. **Otherwise**, challenge the brief yourself using this checklist:

```
Review the Style Brief. Challenge any choices that are:
1. Generic/cliché (would this produce a diagram that looks like every other tech blog?)
2. Mismatched to platform (is the density appropriate for the target size?)
3. Over-designed (is it trying to say too much? Should we simplify?)
4. Under-differentiated (will this stand out, or will people scroll past it?)

Either approve the brief or suggest ONE specific change for the biggest improvement.
```

Merge the feedback, then proceed to Step 1 using the finalized Style Brief as your guide.

### Step 1: Generate Scene JSON

Following the Style Brief from Step 0, create a `.excalidraw` file. Save it to your configured output directory (default: `diagrams/`).

**Before writing any JSON, verify your plan against the Style Brief:**
- Does the layout match the chosen pattern?
- Is the information density at the right level?
- Are colors within the specified strategy?
- Is the "key visual element" the most prominent thing in the composition?

### Step 2: Render to Image

Requires: `@playwright/test` + Chromium browser (`npx playwright install chromium`)

```bash
node scripts/excalidraw/render.mjs diagrams/my-diagram.excalidraw diagrams/my-diagram.png
```

Options:
- `--width=1600` (default 1600)
- `--height=900` (default 900)
- `--scale=2` (default 2, for retina/HiDPI)
- `--theme=light|dark` (default light, affects background color only)

For SVG output, use `.svg` extension:
```bash
node scripts/excalidraw/render.mjs diagrams/my-diagram.excalidraw diagrams/my-diagram.svg
```

**How it works:** Loads React + Excalidraw from CDN in a headless Chromium, runs `exportToCanvas`/`exportToSvg`, outputs the result. No extra npm deps needed beyond Playwright.

### Step 3: Design Review (Recommended)

After rendering, you **SHOULD** review the generated image for visual quality. **If oh-my-claudecode is installed**, spawn a `oh-my-claudecode:designer` agent for an adversarial review. **Otherwise**, review the image yourself using the scoring rubric below.

**Review prompt template:**

```
Review this Excalidraw diagram image for visual quality. Read the image at [path].

This diagram is intended for: [purpose, e.g., "Twitter post, 16:9 ratio, needs to be eye-catching at small sizes"]

Score each dimension 1-10 and provide specific fixes:

1. **Layout & Composition** — Is content well-centered? Is there good use of whitespace? Are elements balanced?
2. **Visual Hierarchy** — Does the eye flow naturally? Are titles prominent enough? Is the most important info emphasized?
3. **Proportions & Spacing** — Are gaps between elements consistent? Are boxes proportional to their content? Any cramped or sparse areas?
4. **Readability** — Is text large enough to read at the target display size? Is there enough contrast between text and backgrounds?
5. **Color Discipline** — Is the diagram monochrome-first? Count the number of distinct strokeColors and backgroundColors used. Rules:
   - strokeColor should be "#1e1e1e" (black) for ALL elements unless there's a strong semantic reason
   - Maximum 2-3 backgroundColors total (transparent + 1-2 light fills)
   - Maximum 1 accent color (purple "#6741d9") for emphasis
   - If you see red/green/blue/orange strokeColors on different boxes, score 3/10 and demand they all become black
   - Exception: BAD vs GOOD comparisons may use red/green backgrounds only (NOT stroke colors)
6. **Overall Polish** — Does it look professional and intentional? Would you be proud to post this publicly? Hand-drawn style should feel deliberate and clean, not cluttered.

For each issue found, provide the EXACT fix as a JSON path change, e.g.:
- "Element 'title': increase fontSize from 32 to 40"
- "Element 'model-box': move x from 100 to 200, increase width from 300 to 400"
- "Add 60px more vertical gap between the boxes and the bottom result bar"

The .excalidraw JSON is at [json_path] — reference element IDs directly.

Minimum passing score: 7/10 on ALL dimensions. If any dimension scores below 7, the diagram MUST be revised.
```

### Step 4: Fix and Re-render

Based on the review feedback:

1. Edit the `.excalidraw` JSON file with the specific coordinate/size/style changes
2. Re-render with `node scripts/excalidraw/render.mjs`
3. If any dimension scored below 7, go back to Step 3
4. Maximum 3 review rounds — after 3 rounds, ship the best version

**Common fixes:**

| Issue | Typical Fix |
|-------|-------------|
| Title too small | Increase `fontSize` to 36-40 for main title |
| Cramped layout | Increase gaps between elements by 40-80px |
| Off-center | Adjust `x` coordinates to center content in viewport |
| Text overflow | Reduce `fontSize` or increase container `width`/`height` |
| Poor contrast | Change `strokeColor` to darker shade, increase `strokeWidth` |
| Inconsistent spacing | Align elements to a grid (multiples of 40px) |
| Visual clutter | Remove unnecessary elements, simplify labels |
| Weak hierarchy | Make primary elements larger/bolder, secondary elements lighter |

## Excalidraw Scene JSON Format

A `.excalidraw` file is JSON with this structure:

```json
{
  "type": "excalidraw",
  "version": 2,
  "elements": [ ... ],
  "appState": {
    "viewBackgroundColor": "#ffffff",
    "theme": "light",
    "gridSize": null
  }
}
```

## Element Reference

### Common Properties (all elements share these)

```json
{
  "id": "unique-id-string",
  "type": "rectangle|ellipse|diamond|text|arrow|line|freedraw|image",
  "x": 100,
  "y": 100,
  "width": 200,
  "height": 100,
  "angle": 0,
  "strokeColor": "#1e1e1e",
  "backgroundColor": "transparent",
  "fillStyle": "solid",
  "strokeWidth": 2,
  "strokeStyle": "solid",
  "roughness": 1,
  "opacity": 100,
  "groupIds": [],
  "roundness": null,
  "seed": 12345,
  "version": 1,
  "isDeleted": false,
  "boundElements": null,
  "locked": false
}
```

### Key Properties Explained

| Property | Values | Description |
|----------|--------|-------------|
| `fillStyle` | `"solid"`, `"hachure"`, `"cross-hatch"`, `"dots"` | How backgrounds are filled. `"hachure"` = classic hand-drawn |
| `strokeWidth` | `1`, `2`, `4` | Line thickness. 2 is standard |
| `strokeStyle` | `"solid"`, `"dashed"`, `"dotted"` | Line style |
| `roughness` | `0`, `1`, `2` | Hand-drawn roughness. 0=smooth, 1=normal, 2=very rough |
| `roundness` | `null` or `{"type": 3}` | null=sharp corners, type:3=rounded corners |
| `opacity` | `0`-`100` | Element opacity |

### Color Philosophy: Monochrome-First

**Default to black (#1e1e1e) for all strokeColor.** Too many colors make hand-drawn diagrams look cluttered and cheap.

**Core principle: use shapes and layout to convey information, not color.**

```
Default palette (covers 90% of use cases):
  strokeColor:      "#1e1e1e"  (black for all elements)
  backgroundColor:  "transparent" or a single light fill
  fillStyle:        "hachure"  (hatching itself provides visual layers)

Only introduce color for semantic distinction, max 2-3:
  Accent:  "#6741d9"  (purple — for key concepts/arrow labels)

Light backgrounds (for area differentiation, not decoration):
  "#f5f5f5"  (very light gray — default area background)
  "#e8e8e8"  (light gray — secondary areas)
  "#fef9c3"  (pale yellow — highlight/emphasis area)
```

**Forbidden:**
- Different strokeColor per box (red box, green box, blue box = cluttered)
- Using color coding instead of text labels
- More than 3 backgroundColors

**Only exception:** When the diagram's core meaning IS a color comparison (e.g., BAD red vs GOOD green), use 2 semantic backgrounds only, keep strokeColor black.

### Rectangle

```json
{
  "id": "rect-1",
  "type": "rectangle",
  "x": 100,
  "y": 100,
  "width": 250,
  "height": 80,
  "strokeColor": "#1e1e1e",
  "backgroundColor": "#f5f5f5",
  "fillStyle": "hachure",
  "strokeWidth": 2,
  "roughness": 2,
  "roundness": null,
  "boundElements": [
    { "id": "text-in-rect", "type": "text" }
  ]
}
```

### Text (standalone)

```json
{
  "id": "text-1",
  "type": "text",
  "x": 100,
  "y": 100,
  "width": 120,
  "height": 25,
  "text": "Hello World",
  "fontSize": 20,
  "fontFamily": 1,
  "textAlign": "center",
  "verticalAlign": "middle",
  "strokeColor": "#1e1e1e",
  "backgroundColor": "transparent",
  "fillStyle": "hachure",
  "roughness": 2
}
```

`fontFamily`: 1 = Virgil (hand-drawn), 2 = Helvetica, 3 = Cascadia (code)

### Text Bound to a Container

To put text inside a rectangle/ellipse/diamond, use `containerId`:

```json
{
  "id": "text-in-rect",
  "type": "text",
  "x": 130,
  "y": 125,
  "width": 190,
  "height": 25,
  "text": "My Label",
  "fontSize": 20,
  "fontFamily": 1,
  "textAlign": "center",
  "verticalAlign": "middle",
  "containerId": "rect-1",
  "strokeColor": "#1e1e1e",
  "backgroundColor": "transparent"
}
```

**Important:** The container element must have `boundElements` referencing this text:
```json
"boundElements": [{ "id": "text-in-rect", "type": "text" }]
```

### Arrow

```json
{
  "id": "arrow-1",
  "type": "arrow",
  "x": 350,
  "y": 140,
  "width": 100,
  "height": 0,
  "points": [[0, 0], [100, 0]],
  "strokeColor": "#1e1e1e",
  "strokeWidth": 2,
  "roughness": 2,
  "startArrowhead": null,
  "endArrowhead": "arrow",
  "startBinding": {
    "elementId": "rect-1",
    "focus": 0,
    "gap": 5
  },
  "endBinding": {
    "elementId": "rect-2",
    "focus": 0,
    "gap": 5
  }
}
```

**Arrowheads:** `null`, `"arrow"`, `"bar"`, `"dot"`, `"triangle"`

**Bindings:** When an arrow connects two shapes, set `startBinding` and `endBinding` with the shape's `id`. The connected shapes must list the arrow in their `boundElements`:
```json
"boundElements": [{ "id": "arrow-1", "type": "arrow" }]
```

**Multi-segment arrows (with bends):**
```json
"points": [[0, 0], [50, 0], [50, 100], [100, 100]]
```

### Ellipse

```json
{
  "id": "ellipse-1",
  "type": "ellipse",
  "x": 100,
  "y": 100,
  "width": 150,
  "height": 150,
  "strokeColor": "#1e1e1e",
  "backgroundColor": "#f5f5f5",
  "fillStyle": "hachure",
  "roundness": { "type": 2 }
}
```

### Diamond

```json
{
  "id": "diamond-1",
  "type": "diamond",
  "x": 100,
  "y": 100,
  "width": 150,
  "height": 100,
  "strokeColor": "#1e1e1e",
  "backgroundColor": "#f5f5f5",
  "fillStyle": "hachure"
}
```

### Line (no arrowheads)

```json
{
  "id": "line-1",
  "type": "line",
  "x": 100,
  "y": 100,
  "width": 200,
  "height": 0,
  "points": [[0, 0], [200, 0]],
  "strokeColor": "#1e1e1e",
  "strokeWidth": 2,
  "strokeStyle": "dashed"
}
```

### Grouping Elements

To group elements visually, give them the same `groupIds` value:

```json
{ "id": "a", "groupIds": ["group-1"], ... },
{ "id": "b", "groupIds": ["group-1"], ... }
```

## Layout Guidelines

### Canvas Sizing

- **Twitter 16:9**: Use `--width=1600 --height=900` (default)
- **Square**: Use `--width=1200 --height=1200`
- **Blog wide**: Use `--width=1920 --height=1080`

### Spacing Rules

- **Between shapes**: 80-120px gap
- **Arrow length**: 60-100px
- **Text padding inside shapes**: 20-30px from edge
- **Title text**: fontSize 36-44, regular text: fontSize 18-22
- **Grid alignment**: Place elements at multiples of 20 for clean alignment

### Typical Layout Patterns

**Horizontal flow (left to right):**
```
x=100  →  x=400  →  x=700  →  x=1000
y=350 for all (centered vertically in 900h canvas)
```

**Vertical flow (top to bottom):**
```
y=80  →  y=280  →  y=480  →  y=680
x=600 for all (centered horizontally in 1600w canvas)
```

**Three-column layout:**
```
Left: x=100    Center: x=550    Right: x=1000
```

## Generation Rules for Claude

When generating Excalidraw scenes, follow these rules:

1. **Every element MUST have ALL required properties** — id, type, x, y, width, height, strokeColor, backgroundColor, fillStyle, strokeWidth, roughness, opacity, angle, groupIds, roundness, seed, version, isDeleted, boundElements, locked

2. **Use unique `seed` values** — each element needs a different integer seed for the hand-drawn randomization to look natural

3. **Container-text binding is bidirectional** — when putting text in a shape:
   - The text element needs `containerId` pointing to the shape
   - The shape needs `boundElements` listing the text `{ "id": "...", "type": "text" }`

4. **Arrow binding is bidirectional** — when connecting arrows to shapes:
   - The arrow needs `startBinding`/`endBinding` referencing shape ids
   - The shapes need `boundElements` listing the arrow `{ "id": "...", "type": "arrow" }`

5. **Use `roughness: 2`** for the classic hand-drawn look. Use `roughness: 0` only for clean/technical diagrams.

6. **Use `fillStyle: "hachure"`** for the classic Excalidraw sketch feel (default). Use `"solid"` for clean/modern look.

7. **Monochrome-first coloring (CRITICAL):**
   - ALL `strokeColor` MUST be `"#1e1e1e"` (black) by default
   - ALL `backgroundColor` should be `"transparent"` or a single light gray `"#f5f5f5"`
   - Maximum 1 accent color: `"#6741d9"` (purple) for emphasis labels/arrows
   - Do NOT use red/green/blue/orange strokeColors on different boxes
   - Exception: BAD vs GOOD comparisons may use light red/green backgrounds only, strokeColor stays black

8. **Center content in the viewport** — for a 1600x900 canvas, main content should be roughly centered around x=800, y=450.

9. **Font sizes**: Title=36-44, Subtitle=24-28, Body=18-22, Small=14-16

10. **File naming**: Save as `<output-dir>/<name>.excalidraw`

11. **After generating the JSON, immediately run the render command**, then review the rendered image (Step 3).
