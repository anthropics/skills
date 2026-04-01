# Generative Art Reference

## Process

### Step 1: Algorithmic Philosophy
Before writing code, write a manifesto (4-6 paragraphs) that describes the computational aesthetic. Name the movement (1-2 words). Describe how the philosophy manifests through computational processes, noise functions, particle behaviors, temporal evolution, and parametric variation.

### Step 2: Implementation
Express the philosophy through p5.js with seeded randomness. The algorithm should be 90% generative, 10% parameters.

### Core Technical Requirements

**Seeded Randomness:**
```javascript
let seed = 12345;
randomSeed(seed);
noiseSeed(seed);
```
Same seed always produces the same output. Different seeds reveal different facets.

**Parameter Structure:**
```javascript
let params = {
  seed: 12345,
  particleCount: 1000,
  noiseScale: 0.005,
  speed: 1.5,
  // Add parameters specific to the algorithm
};
```

**Single-File HTML:**
Everything inline, no external files except p5.js CDN:
```html
<script src="https://cdnjs.cloudflare.com/ajax/libs/p5.js/1.7.0/p5.min.js"></script>
```

### Required UI Features
1. **Seed navigation**: prev/next/random buttons, seed display, jump-to-seed input
2. **Parameter controls**: sliders for numeric values, color pickers for palette
3. **Actions**: regenerate, reset defaults, download PNG

### Philosophy Examples

**Flow Fields**: Layered Perlin noise driving particle trails. Thousands of particles follow vector forces, accumulating into organic density maps.

**Quantum Harmonics**: Particles on a grid with phase values evolving through sine waves. Constructive/destructive interference creates emergent patterns.

**Stochastic Crystallization**: Randomized circle packing or Voronoi tessellation. Random points evolve through relaxation algorithms until equilibrium.

**Recursive Whispers**: Branching structures that subdivide recursively, constrained by golden ratios with noise perturbations.

### Quality Bar
The output should look like it was refined by a computational artist over hundreds of iterations. Every parameter should feel carefully tuned. The result should reward sustained viewing.
