/**
 * ═══════════════════════════════════════════════════════════════════════════
 *              MOTION EXPLAINER - ANIMATION ENGINE BEST PRACTICES
 * ═══════════════════════════════════════════════════════════════════════════
 *
 * This file is STRUCTURE and PRINCIPLES for p5.js motion explainers.
 * It is NOT a recipe. Your concept's narrative should drive what you build.
 *
 * Core philosophy: Every frame serves understanding. Beauty is a byproduct
 * of clarity — not the other way around.
 *
 * ═══════════════════════════════════════════════════════════════════════════
 */

// ============================================================================
// 1. SCENE SYSTEM — The atomic unit of explanation
// ============================================================================
// A "Scene" is one beat of understanding. One insight. One revelation.
// Each scene has a lifecycle: enter → sustain → exit.
// t = 0.0 means "just started", t = 1.0 means "fully revealed".

class Scene {
    constructor(title, durationSeconds) {
        this.title = title;
        this.duration = durationSeconds * 60; // convert to frames at 60fps
        this.frame = 0;
        this.done = false;
    }

    // t goes smoothly from 0 → 1 over the scene's duration
    get t() {
        return min(this.frame / this.duration, 1.0);
    }

    // Call once per frame when this scene is active
    update() {
        this.frame++;
        if (this.frame >= this.duration) this.done = true;
    }

    draw() {
        // Override in subclasses or use inline functions
        // This is where you render the scene at time t
    }

    reset() {
        this.frame = 0;
        this.done = false;
    }
}

// ============================================================================
// 2. SCENE MANAGER — Orchestrates the sequence
// ============================================================================

class SceneManager {
    constructor(scenes) {
        this.scenes = scenes;
        this.currentIndex = 0;
        this.playing = false;
        this.speed = 1.0; // 0.5x, 1x, 2x supported
    }

    get current() {
        return this.scenes[this.currentIndex];
    }

    get totalScenes() {
        return this.scenes.length;
    }

    update() {
        if (!this.playing) return;

        // Speed multiplier: run update() multiple times for faster playback
        const steps = this.speed >= 2 ? 2 : 1;
        for (let i = 0; i < steps; i++) {
            if (this.current && !this.current.done) {
                this.current.update();
            } else if (this.currentIndex < this.scenes.length - 1) {
                this.goToScene(this.currentIndex + 1);
            } else {
                this.playing = false; // Reached end
            }
        }
    }

    draw() {
        if (this.current) this.current.draw();
    }

    goToScene(index) {
        if (index < 0 || index >= this.scenes.length) return;
        this.scenes[index].reset();
        this.currentIndex = index;
    }

    nextScene() { this.goToScene(this.currentIndex + 1); }
    prevScene() { this.goToScene(this.currentIndex - 1); }

    // Jump to a moment within the current scene (0.0 to 1.0)
    scrubTo(t) {
        this.current.frame = floor(t * this.current.duration);
        this.playing = false;
    }
}

// ============================================================================
// 3. EASING LIBRARY — How things arrive matters as much as where they land
// ============================================================================

const Ease = {
    // Smooth start and stop — the workhorse of animation
    inOut: t => t < 0.5 ? 2 * t * t : 1 - Math.pow(-2 * t + 2, 2) / 2,

    // Decelerates in: snappy arrivals
    out: t => 1 - Math.pow(1 - t, 3),

    // Accelerates out: things launching into motion
    in: t => t * t * t,

    // Bounce at the end: playful, good for "clicking into place"
    outBounce: t => {
        if (t < 1/2.75) return 7.5625 * t * t;
        if (t < 2/2.75) return 7.5625 * (t -= 1.5/2.75) * t + 0.75;
        if (t < 2.5/2.75) return 7.5625 * (t -= 2.25/2.75) * t + 0.9375;
        return 7.5625 * (t -= 2.625/2.75) * t + 0.984375;
    },

    // Elastic overshoot: springs back, good for emphasis
    outElastic: t => {
        if (t === 0 || t === 1) return t;
        return Math.pow(2, -10 * t) * Math.sin((t * 10 - 0.75) * (2 * Math.PI / 3)) + 1;
    },

    // Gate: nothing happens until threshold, then smooth reveal
    // threshold: 0.0 to 1.0 — when does this element start appearing?
    // window: how much of t is used for the reveal (default 0.3)
    gate: (t, threshold = 0, window = 0.3) => {
        return Ease.inOut(constrain(map(t, threshold, threshold + window, 0, 1), 0, 1));
    }
};

// ============================================================================
// 4. ANIMATION PRIMITIVES — Build your visual vocabulary from these
// ============================================================================

// Animate a value from `a` to `b` over time t, with optional easing
function animate(a, b, t, easeFn = Ease.inOut) {
    return lerp(a, b, easeFn(constrain(t, 0, 1)));
}

// Draw a partial path (0 = nothing, 1 = full path) — great for "tracing" motion
// points: array of [x, y] pairs
function drawPartialPath(points, t, weight = 2, col = '#d97757') {
    if (points.length < 2) return;
    const totalSegments = points.length - 1;
    const progress = t * totalSegments;
    const fullSegments = floor(progress);
    const partial = progress - fullSegments;

    stroke(col);
    strokeWeight(weight);
    noFill();
    beginShape();
    for (let i = 0; i <= fullSegments && i < points.length; i++) {
        vertex(points[i][0], points[i][1]);
    }
    if (fullSegments < totalSegments) {
        const from = points[fullSegments];
        const to = points[fullSegments + 1];
        vertex(lerp(from[0], to[0], partial), lerp(from[1], to[1], partial));
    }
    endShape();
}

// Draw an annotation arrow — the pen of the explainer
// headSize controls arrowhead scale
function drawArrow(x1, y1, x2, y2, col = '#d97757', weight = 2, headSize = 12) {
    stroke(col);
    strokeWeight(weight);
    fill(col);

    const angle = atan2(y2 - y1, x2 - x1);
    const len = dist(x1, y1, x2, y2);
    const bodyLen = len - headSize;

    push();
    translate(x1, y1);
    rotate(angle);

    // Shaft
    line(0, 0, bodyLen, 0);

    // Head
    translate(bodyLen, 0);
    noStroke();
    triangle(0, -headSize * 0.4, 0, headSize * 0.4, headSize, 0);
    pop();
}

// Draw a label at (x, y) with optional background pill
function drawLabel(x, y, text, opts = {}) {
    const {
        size = 18,
        col = '#141413',
        bg = null,          // e.g., '#faf9f5' for background pill
        alpha = 255,
        align = CENTER,
        weight = 'normal'   // 'bold' or 'normal'
    } = opts;

    textAlign(align);
    textSize(size);

    if (bg) {
        const w = textWidth(text) + 20;
        const h = size + 12;
        fill(bg);
        noStroke();
        rectMode(CENTER);
        rect(x, y, w, h, 4);
    }

    fill(red(color(col)), green(color(col)), blue(color(col)), alpha);
    noStroke();
    text(text, x, y + size * 0.35);
    textAlign(LEFT); // Reset
}

// Highlight box — draw a glowing rectangle around something important
function drawHighlight(x, y, w, h, col = '#d97757', alpha = 80, radius = 8) {
    noStroke();
    fill(red(color(col)), green(color(col)), blue(color(col)), alpha);
    rectMode(CENTER);
    rect(x, y, w + 20, h + 12, radius);
    stroke(col);
    strokeWeight(2);
    noFill();
    rect(x, y, w + 20, h + 12, radius);
}

// Typewriter effect: reveal text one character at a time
// t = 0 → empty, t = 1 → full string
function typewriter(fullText, t) {
    const chars = ceil(t * fullText.length);
    return fullText.substring(0, chars);
}

// Fade alpha: returns an alpha value (0-255) that fades in over t ∈ [start, end]
function fadeIn(t, start = 0, end = 0.3) {
    return map(constrain(t, start, end), start, end, 0, 255);
}

// ============================================================================
// 5. COORDINATE SYSTEM — Map math to screen space
// ============================================================================
// For mathematical explanations, establish a coordinate system at setup.
// All your math lives in "world space"; translate to screen before drawing.

class CoordinateSystem {
    constructor(cx, cy, scale) {
        this.cx = cx;       // Canvas x of origin
        this.cy = cy;       // Canvas y of origin
        this.scale = scale; // Pixels per unit
    }

    // Convert world point to canvas point
    toScreen(wx, wy) {
        return [this.cx + wx * this.scale, this.cy - wy * this.scale];
    }

    // Draw axes with labels
    drawAxes(xRange = [-5, 5], yRange = [-4, 4], col = '#b0aea5') {
        const [x0, y0] = this.toScreen(xRange[0], 0);
        const [x1, y1] = this.toScreen(xRange[1], 0);
        const [ax0, ay0] = this.toScreen(0, yRange[0]);
        const [ax1, ay1] = this.toScreen(0, yRange[1]);

        stroke(col);
        strokeWeight(1.5);
        drawArrow(x0, y0, x1, y1, col, 1.5, 10);
        drawArrow(ax0, ay0, ax1, ay1, col, 1.5, 10);
    }

    // Plot a function f(x) from xMin to xMax with resolution steps
    plotFunction(f, xMin, xMax, col = '#d97757', weight = 2.5, steps = 200) {
        stroke(col);
        strokeWeight(weight);
        noFill();
        beginShape();
        for (let i = 0; i <= steps; i++) {
            const wx = map(i, 0, steps, xMin, xMax);
            const wy = f(wx);
            const [sx, sy] = this.toScreen(wx, wy);
            vertex(sx, sy);
        }
        endShape();
    }
}

// ============================================================================
// 6. TYPOGRAPHY — The voice of your explainer
// ============================================================================
// Use consistent type hierarchy. The viewer's eye should know where to look.

const Typography = {
    // Main concept title — shown once per scene at the top
    headline: (text, x, y, alpha = 255) => {
        textFont('Lora, serif');
        textSize(28);
        textAlign(CENTER);
        fill(20, 20, 19, alpha);
        noStroke();
        text(text, x, y);
    },

    // Step label — "Step 1 of 4" or scene subtitle
    stepLabel: (text, x, y, alpha = 180) => {
        textFont('Poppins, sans-serif');
        textSize(13);
        textAlign(CENTER);
        fill(176, 174, 165, alpha);
        noStroke();
        text(text, x, y);
    },

    // Body annotation — callout text next to a visual element
    annotation: (text, x, y, col = '#141413', alpha = 255) => {
        textFont('Poppins, sans-serif');
        textSize(15);
        textAlign(LEFT);
        fill(red(color(col)), green(color(col)), blue(color(col)), alpha);
        noStroke();
        text(text, x, y);
    },

    // Math expression (monospace)
    math: (text, x, y, size = 18, alpha = 255) => {
        textFont('Courier New, monospace');
        textSize(size);
        textAlign(CENTER);
        fill(20, 20, 19, alpha);
        noStroke();
        text(text, x, y);
    }
};

// ============================================================================
// 7. COLOR PALETTE — Consistent visual language
// ============================================================================
// Use one color per concept. If A is always orange, every orange thing is A.
// Consistency IS comprehension.

const Palette = {
    primary:    '#d97757', // Anthropic orange  — primary concept, emphasis
    secondary:  '#6a9bcc', // Steel blue        — secondary concept, contrast
    tertiary:   '#788c5d', // Sage green        — third concept, result
    neutral:    '#b0aea5', // Gray              — axes, guides, background elements
    dark:       '#141413', // Near-black        — labels, equations
    light:      '#faf9f5', // Off-white         — canvas background
    lightGray:  '#e8e6dc', // Light gray        — grid lines, borders
    highlight:  '#f5c89a', // Warm amber        — spotlight, callout bg
};

// ============================================================================
// 8. PERFORMANCE — Keep it smooth under animation
// ============================================================================

// For computationally expensive operations, precompute in scene.reset():
// - Lookup tables for trig functions
// - Path point arrays
// - Layout positions
// Then draw() just reads from those arrays — O(n) not O(n²)

// Frame rate throttle for heavy scenes:
// function setup() { frameRate(60); } — explicitly set this

// ============================================================================
// REMEMBER
// ============================================================================
//
// The goal is the "aha moment" — the viewer's understanding shifting.
// Every element on screen should be there BECAUSE it helps that shift.
// If it doesn't serve comprehension, cut it.
//
// Animation timing:
// - Too fast: viewer misses the revelation
// - Too slow: viewer loses the thread
// - Just right: they feel it before they think it
//
// ============================================================================
