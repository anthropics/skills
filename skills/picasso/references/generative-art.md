# Generative Art Reference

## Table of Contents
1. Philosophy
2. p5.js Patterns
3. SVG Generative Art
4. Canvas 2D API
5. Noise Functions
6. Color in Generative Art
7. Seeded Randomness
8. Animation vs Static
9. Performance
10. Common Mistakes

---

## 1. Philosophy

Generative art is intentional design expressed through algorithms. Randomness is a tool, not the goal. The artist defines the system, its constraints, and its parameter space. The algorithm explores that space. Every output should feel curated, as if the artist chose it from a thousand variations.

The quality bar: a viewer should not think "a computer made this." They should think "someone designed this." The difference is in constraint. Unconstrained randomness produces noise. Constrained randomness produces beauty.

Three principles guide generative design:
- **Parameterize everything.** Every magic number becomes a parameter. This lets you explore the design space systematically.
- **Seed everything.** Reproducibility is non-negotiable. A good output must be recoverable.
- **Curate ruthlessly.** Generate hundreds of variations. Ship the best five. The algorithm is a collaborator, not the artist.

---

## 2. p5.js Patterns

### Canvas Setup
Always size the canvas to the container or a specific aspect ratio. Never hardcode pixel dimensions without a reason.

```javascript
function setup() {
  const canvas = createCanvas(windowWidth, windowHeight);
  canvas.parent('canvas-container');
  pixelDensity(2); // retina support
  randomSeed(params.seed);
  noiseSeed(params.seed);
}

function windowResized() {
  resizeCanvas(windowWidth, windowHeight);
}
```

### Flow Field

A complete flow field with particle trails. Particles follow angles derived from Perlin noise, accumulating into organic density maps.

```javascript
const params = {
  seed: 42,
  particleCount: 2000,
  noiseScale: 0.003,
  speed: 2,
  trailAlpha: 10,
  fieldRotation: 0
};

let particles = [];

function setup() {
  createCanvas(800, 800);
  randomSeed(params.seed);
  noiseSeed(params.seed);
  background(15);

  for (let i = 0; i < params.particleCount; i++) {
    particles.push({
      x: random(width),
      y: random(height),
      prevX: 0,
      prevY: 0
    });
  }
}

function draw() {
  for (const p of particles) {
    const angle = noise(p.x * params.noiseScale, p.y * params.noiseScale) *
      TAU * 2 + params.fieldRotation;
    p.prevX = p.x;
    p.prevY = p.y;
    p.x += cos(angle) * params.speed;
    p.y += sin(angle) * params.speed;

    // Wrap around edges
    if (p.x < 0) p.x = width;
    if (p.x > width) p.x = 0;
    if (p.y < 0) p.y = height;
    if (p.y > height) p.y = 0;

    stroke(255, params.trailAlpha);
    strokeWeight(0.5);
    line(p.prevX, p.prevY, p.x, p.y);
  }
}
```

### Particle System

Self-contained particle class with lifecycle management.

```javascript
class Particle {
  constructor(x, y, hue) {
    this.pos = createVector(x, y);
    this.vel = p5.Vector.random2D().mult(random(0.5, 2));
    this.acc = createVector(0, 0);
    this.lifespan = 255;
    this.hue = hue;
    this.size = random(2, 6);
  }

  applyForce(force) {
    this.acc.add(force);
  }

  update() {
    this.vel.add(this.acc);
    this.vel.limit(4);
    this.pos.add(this.vel);
    this.acc.mult(0);
    this.lifespan -= 2;
  }

  draw() {
    noStroke();
    fill(`oklch(0.75 0.15 ${this.hue} / ${this.lifespan / 255})`);
    circle(this.pos.x, this.pos.y, this.size);
  }

  isDead() {
    return this.lifespan <= 0;
  }
}
```

### Single-File HTML Scaffold

All generative art ships as a single HTML file with p5.js from CDN.

```html
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>Generative Piece</title>
  <script src="https://cdnjs.cloudflare.com/ajax/libs/p5.js/1.9.4/p5.min.js"></script>
  <style>
    * { margin: 0; padding: 0; box-sizing: border-box; }
    body { background: #0f0f0f; overflow: hidden; }
    #controls {
      position: fixed; bottom: 16px; left: 16px;
      display: flex; gap: 8px; z-index: 10;
    }
    #controls button {
      padding: 6px 14px; border: 1px solid rgba(255,255,255,0.2);
      background: rgba(0,0,0,0.6); color: #fff; border-radius: 6px;
      cursor: pointer; font-size: 13px;
    }
    #seed-display {
      position: fixed; top: 16px; left: 16px;
      color: rgba(255,255,255,0.4); font: 13px/1 monospace;
    }
  </style>
</head>
<body>
  <div id="seed-display"></div>
  <div id="controls">
    <button onclick="prevSeed()">Prev</button>
    <button onclick="nextSeed()">Next</button>
    <button onclick="randomizeSeed()">Random</button>
    <button onclick="saveCanvas('output', 'png')">Export PNG</button>
  </div>
  <script>
    /* params, setup, draw, seed controls here */
  </script>
</body>
</html>
```

---

## 3. SVG Generative Art

SVG output is resolution-independent and ideal for print, plotters, and crisp digital display. Build SVG strings programmatically or use DOM manipulation.

### Programmatic SVG Construction

```javascript
function generateSVG(width, height, seed) {
  const rng = createRNG(seed);
  const paths = [];

  for (let i = 0; i < 50; i++) {
    const cx = rng() * width;
    const cy = rng() * height;
    const points = [];

    for (let a = 0; a < Math.PI * 2; a += 0.1) {
      const r = 40 + rng() * 30;
      const x = cx + Math.cos(a) * r;
      const y = cy + Math.sin(a) * r;
      points.push(`${x.toFixed(2)},${y.toFixed(2)}`);
    }

    const hue = (i * 7.2) % 360;
    paths.push(
      `<polygon points="${points.join(' ')}" ` +
      `fill="oklch(0.7 0.12 ${hue})" fill-opacity="0.3" ` +
      `stroke="oklch(0.5 0.15 ${hue})" stroke-width="0.5" />`
    );
  }

  return `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ${width} ${height}">
    <rect width="${width}" height="${height}" fill="oklch(0.12 0.01 260)" />
    ${paths.join('\n    ')}
  </svg>`;
}
```

### Path Generation with Cubic Beziers

For smooth organic curves, use cubic bezier path commands. Generate control points with noise-influenced offsets.

```javascript
function noisyPath(startX, startY, steps, rng, noiseScale = 0.02) {
  let d = `M ${startX} ${startY}`;
  let x = startX, y = startY;

  for (let i = 0; i < steps; i++) {
    const angle = simplexNoise2D(x * noiseScale, y * noiseScale) * Math.PI * 2;
    const length = 20 + rng() * 40;
    const cp1x = x + Math.cos(angle) * length * 0.5;
    const cp1y = y + Math.sin(angle) * length * 0.5;
    x += Math.cos(angle) * length;
    y += Math.sin(angle) * length;
    const cp2x = x - Math.cos(angle) * length * 0.3;
    const cp2y = y - Math.sin(angle) * length * 0.3;
    d += ` C ${cp1x} ${cp1y}, ${cp2x} ${cp2y}, ${x} ${y}`;
  }

  return d;
}
```

### Exporting SVG

```javascript
function downloadSVG(svgString, filename = 'generative.svg') {
  const blob = new Blob([svgString], { type: 'image/svg+xml' });
  const url = URL.createObjectURL(blob);
  const a = document.createElement('a');
  a.href = url;
  a.download = filename;
  a.click();
  URL.revokeObjectURL(url);
}
```

---

## 4. Canvas 2D API

When you need raw performance without a library, use the native Canvas 2D context.

```javascript
function initCanvas(width, height) {
  const canvas = document.createElement('canvas');
  canvas.width = width * devicePixelRatio;
  canvas.height = height * devicePixelRatio;
  canvas.style.width = `${width}px`;
  canvas.style.height = `${height}px`;
  const ctx = canvas.getContext('2d');
  ctx.scale(devicePixelRatio, devicePixelRatio);
  return { canvas, ctx };
}

function drawFlowField(ctx, w, h, seed) {
  const rng = createRNG(seed);
  ctx.fillStyle = 'oklch(0.08 0.01 260)';
  ctx.fillRect(0, 0, w, h);

  ctx.strokeStyle = 'oklch(0.85 0.04 200 / 0.04)';
  ctx.lineWidth = 0.5;

  for (let i = 0; i < 3000; i++) {
    let x = rng() * w;
    let y = rng() * h;
    ctx.beginPath();
    ctx.moveTo(x, y);

    for (let step = 0; step < 80; step++) {
      const angle = simplexNoise2D(x * 0.003, y * 0.003) * Math.PI * 4;
      x += Math.cos(angle) * 1.5;
      y += Math.sin(angle) * 1.5;
      ctx.lineTo(x, y);
    }

    ctx.stroke();
  }
}
```

### Pixel-Level Manipulation

For effects like reaction-diffusion or cellular automata, work directly with pixel data.

```javascript
function pixelEffect(ctx, w, h) {
  const imageData = ctx.getImageData(0, 0, w, h);
  const data = imageData.data;

  for (let i = 0; i < data.length; i += 4) {
    const px = (i / 4) % w;
    const py = Math.floor(i / 4 / w);
    const n = simplexNoise2D(px * 0.01, py * 0.01);
    data[i] = Math.floor(n * 128 + 128);     // R
    data[i + 1] = Math.floor(n * 64 + 128);  // G
    data[i + 2] = Math.floor(n * 180 + 75);  // B
    data[i + 3] = 255;                        // A
  }

  ctx.putImageData(imageData, 0, 0);
}
```

---

## 5. Noise Functions

### Perlin vs Simplex

| Property | Perlin | Simplex |
|---|---|---|
| Dimensions | Works well in 2D-3D | Scales cleanly to 4D+ |
| Artifacts | Grid-aligned directional artifacts | No directional bias |
| Performance | Moderate | Faster in higher dimensions |
| Use case | p5.js `noise()` default | Preferred for custom implementations |

### Practical Usage

```javascript
// Single-octave noise: smooth, blobby
const value = noise(x * scale, y * scale);

// Multi-octave (fractal) noise: organic detail
function fractalNoise(x, y, octaves = 4, lacunarity = 2, persistence = 0.5) {
  let total = 0;
  let frequency = 1;
  let amplitude = 1;
  let maxValue = 0;

  for (let i = 0; i < octaves; i++) {
    total += simplexNoise2D(x * frequency, y * frequency) * amplitude;
    maxValue += amplitude;
    amplitude *= persistence;
    frequency *= lacunarity;
  }

  return total / maxValue; // normalized to -1..1
}
```

### Noise Scale Guide

| Scale | Effect | Use Case |
|---|---|---|
| 0.001-0.005 | Very smooth, continent-like | Large flow fields, terrain |
| 0.005-0.02 | Gentle undulation | Particle paths, soft gradients |
| 0.02-0.1 | Visible texture | Surface detail, displacement |
| 0.1-0.5 | High frequency, gritty | Texture overlay, grain |

### Layering Noise

Combine noise at different scales for complex organic results.

```javascript
function layeredNoise(x, y) {
  const base = fractalNoise(x, y, 4, 2, 0.5);         // large form
  const detail = simplexNoise2D(x * 0.08, y * 0.08);   // medium texture
  const grain = simplexNoise2D(x * 0.5, y * 0.5);      // fine grain
  return base * 0.7 + detail * 0.2 + grain * 0.1;
}
```

---

## 6. Color in Generative Art

Use OKLCH for all generative color work. Its perceptual uniformity means programmatic palette generation produces visually coherent results, unlike HSL where "equal" lightness values look uneven.

### Palette Generation Algorithms

```javascript
// Analogous palette: hues clustered within a range
function analogousPalette(baseHue, count = 5, spread = 30) {
  return Array.from({ length: count }, (_, i) => {
    const hue = (baseHue - spread / 2 + (spread / (count - 1)) * i) % 360;
    return `oklch(0.7 0.15 ${hue})`;
  });
}

// Complementary with variation
function complementaryPalette(baseHue) {
  return [
    `oklch(0.65 0.2 ${baseHue})`,
    `oklch(0.75 0.1 ${baseHue})`,
    `oklch(0.65 0.2 ${(baseHue + 180) % 360})`,
    `oklch(0.80 0.08 ${(baseHue + 180) % 360})`,
  ];
}

// Triadic palette
function triadicPalette(baseHue, lightness = 0.65, chroma = 0.18) {
  return [0, 120, 240].map(offset =>
    `oklch(${lightness} ${chroma} ${(baseHue + offset) % 360})`
  );
}
```

### Color from Noise

Map noise values to hue ranges for smooth, organic color transitions.

```javascript
function noiseColor(x, y, noiseScale = 0.005) {
  const n = noise(x * noiseScale, y * noiseScale); // 0..1
  const hue = lerp(200, 320, n);                    // blue to magenta
  const lightness = lerp(0.5, 0.8, n);
  const chroma = lerp(0.08, 0.2, n);
  return `oklch(${lightness} ${chroma} ${hue})`;
}
```

### Background and Contrast

Dark backgrounds with luminous strokes produce the best generative art contrast. Use near-black with a slight hue tint, never pure `#000000`.

```javascript
const bg = 'oklch(0.08 0.015 260)';  // dark blue-tinted black
const stroke = 'oklch(0.85 0.12 200 / 0.06)'; // faint luminous trail
```

---

## 7. Seeded Randomness

Every generative piece must be reproducible. Same seed, same output. Always.

### Minimal Seeded RNG

A fast, high-quality 32-bit PRNG (Mulberry32) that fits in any project.

```javascript
function createRNG(seed) {
  let s = seed | 0;
  return function () {
    s = (s + 0x6d2b79f5) | 0;
    let t = Math.imul(s ^ (s >>> 15), 1 | s);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

const rng = createRNG(42);
rng(); // 0.0..1.0, deterministic
```

### Seed Management in p5.js

```javascript
let currentSeed = 42;

function regenerate(newSeed) {
  currentSeed = newSeed;
  randomSeed(currentSeed);
  noiseSeed(currentSeed);
  clear();
  background(15);
  draw(); // or loop() for animated pieces
}

function nextSeed() { regenerate(currentSeed + 1); }
function prevSeed() { regenerate(currentSeed - 1); }
function randomizeSeed() { regenerate(Math.floor(Math.random() * 999999)); }
```

### Seed from URL

Let users share specific outputs via URL.

```javascript
function seedFromURL() {
  const urlParams = new URLSearchParams(window.location.search);
  return urlParams.has('seed') ? parseInt(urlParams.get('seed'), 10) : 42;
}

function updateURL(seed) {
  const url = new URL(window.location);
  url.searchParams.set('seed', seed);
  window.history.replaceState({}, '', url);
}
```

---

## 8. Animation vs Static

### When to Animate
- The piece explores temporal evolution (particles finding equilibrium, growth systems)
- Real-time interactivity adds meaning (mouse-reactive fields, audio-reactive visuals)
- The animation reveals the process (watching the flow field build creates wonder)

### When to Stay Static
- The final composition is the point (print-quality output)
- The algorithm is computationally expensive (reaction-diffusion, deep recursion)
- The piece will be exported as PNG/SVG

### Animation Loop Pattern

```javascript
let isAnimating = true;

function draw() {
  if (!isAnimating) return;
  // drawing logic here
}

// For non-p5 contexts
function animate(ctx, state) {
  function frame(timestamp) {
    if (!state.running) return;
    update(state, timestamp);
    render(ctx, state);
    state.frameId = requestAnimationFrame(frame);
  }
  state.frameId = requestAnimationFrame(frame);
}

function stop(state) {
  state.running = false;
  cancelAnimationFrame(state.frameId);
}
```

### Export Workflow for Animated Pieces

Render a fixed number of frames, then stop and allow PNG export.

```javascript
const TOTAL_FRAMES = 300;
let frameCount = 0;

function draw() {
  if (frameCount >= TOTAL_FRAMES) {
    noLoop();
    document.getElementById('export-btn').disabled = false;
    return;
  }
  // render frame
  frameCount++;
}
```

---

## 9. Performance

### Offscreen Canvas

Pre-render static or expensive layers to an offscreen canvas, then composite.

```javascript
function createOffscreenLayer(width, height, drawFn) {
  const offscreen = document.createElement('canvas');
  offscreen.width = width;
  offscreen.height = height;
  const offCtx = offscreen.getContext('2d');
  drawFn(offCtx, width, height);
  return offscreen;
}

// Usage: render background noise once
const bgLayer = createOffscreenLayer(800, 800, (ctx, w, h) => {
  // expensive noise texture
  pixelEffect(ctx, w, h);
});

// In the main draw loop, just composite
mainCtx.drawImage(bgLayer, 0, 0);
```

### Batching Draw Calls

Group similar operations. One `beginPath()` with many `lineTo()` calls is much faster than many individual `beginPath()/stroke()` pairs.

```javascript
// Fast: single path for all particles of the same color
ctx.beginPath();
ctx.strokeStyle = 'oklch(0.8 0.1 220 / 0.05)';
for (const p of particles) {
  ctx.moveTo(p.prevX, p.prevY);
  ctx.lineTo(p.x, p.y);
}
ctx.stroke(); // one draw call

// Slow: individual stroke per particle (avoid this)
```

### requestAnimationFrame Discipline

Never use `setInterval` or `setTimeout` for animation. Always use `requestAnimationFrame`. It syncs to the display refresh, pauses in background tabs, and produces smooth frame pacing.

### Pixel Density

On retina screens, match the device pixel ratio but keep the logical coordinate space the same.

```javascript
const dpr = window.devicePixelRatio || 1;
canvas.width = logicalWidth * dpr;
canvas.height = logicalHeight * dpr;
canvas.style.width = `${logicalWidth}px`;
canvas.style.height = `${logicalHeight}px`;
ctx.scale(dpr, dpr);
```

---

## 10. Common Mistakes

- Using `Math.random()` without seeding (outputs are unreproducible and cannot be shared or revisited)
- Hardcoding canvas dimensions instead of deriving from container or aspect ratio (breaks on different screens)
- Forgetting to wrap particle coordinates at edges (particles fly offscreen and waste computation)
- Calling `background()` every frame in pieces meant to accumulate trails (erases the trail effect)
- Using HSL for programmatic color generation (perceptually uneven; a green and blue at the same HSL lightness look completely different in brightness)
- Animating when the piece should be static (wasting battery and CPU for a composition that is complete after frame 1)
- Not providing seed navigation UI (users cannot explore the design space or recover a good output)
- Rendering at 1x on retina displays (produces blurry output; always account for `devicePixelRatio`)
- Creating one `Path2D` or `beginPath/stroke` per particle instead of batching (kills frame rate above a few hundred elements)
- Using `noise()` with a scale of 1.0 (produces white noise; useful noise scales are typically 0.001 to 0.1)
- Generating palettes with random RGB values (produces muddy, clashing colors; derive palettes algorithmically in OKLCH)
- Shipping without an export button (the whole point is producing artifacts worth keeping)
