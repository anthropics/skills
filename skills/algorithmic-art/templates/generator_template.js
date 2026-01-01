/**
 * ═══════════════════════════════════════════════════════════════════════════
 *                  P5.JS生成艺术 - 最佳实践
 * ═══════════════════════════════════════════════════════════════════════════
 *
 * 此文件显示p5.js生成艺术的结构和原则。
 * 它不规定您应该创建什么艺术。
 *
 * 您的算法哲学应该指导您构建什么。
 * 这些只是如何构建代码的最佳实践。
 *
 * ═══════════════════════════════════════════════════════════════════════════
 */

// ============================================================================
// 1. 参数组织
// ============================================================================
// 将所有可调参数保存在一个对象中
// 这使得以下操作变得容易：
// - 连接到UI控件
// - 重置为默认值
// - 序列化/保存配置

let params = {
    // 定义匹配您的算法的参数
    // 示例（为您的艺术自定义）：
    // - 计数：有多少元素（粒子、圆形、分支等）
    // - 比例：大小、速度、间距
    // - 概率：事件的可能性
    // - 角度：旋转、方向
    // - 颜色：调色板数组

    seed: 12345,
    // 将colorPalette定义为数组 -- 选择您喜欢的任何颜色 ['#d97757', '#6a9bcc', '#788c5d', '#b0aea5']
    // 根据您的算法在此处添加您的参数
};

// ============================================================================
// 2. 种子随机性（可重现性至关重要）
// ============================================================================
// 始终使用种子随机以获得Art Blocks风格的可重现输出

function initializeSeed(seed) {
    randomSeed(seed);
    noiseSeed(seed);
    // 现在所有random()和noise()调用都是确定性的
}

// ============================================================================
// 3. P5.JS LIFECYCLE
// ============================================================================

function setup() {
    createCanvas(800, 800);

    // Initialize seed first
    initializeSeed(params.seed);

    // Set up your generative system
    // This is where you initialize:
    // - Arrays of objects
    // - Grid structures
    // - Initial positions
    // - Starting states

    // For static art: call noLoop() at the end of setup
    // For animated art: let draw() keep running
}

function draw() {
    // Option 1: Static generation (runs once, then stops)
    // - Generate everything in setup()
    // - Call noLoop() in setup()
    // - draw() doesn't do much or can be empty

    // Option 2: Animated generation (continuous)
    // - Update your system each frame
    // - Common patterns: particle movement, growth, evolution
    // - Can optionally call noLoop() after N frames

    // Option 3: User-triggered regeneration
    // - Use noLoop() by default
    // - Call redraw() when parameters change
}

// ============================================================================
// 4. CLASS STRUCTURE (When you need objects)
// ============================================================================
// Use classes when your algorithm involves multiple entities
// Examples: particles, agents, cells, nodes, etc.

class Entity {
    constructor() {
        // Initialize entity properties
        // Use random() here - it will be seeded
    }

    update() {
        // Update entity state
        // This might involve:
        // - Physics calculations
        // - Behavioral rules
        // - Interactions with neighbors
    }

    display() {
        // Render the entity
        // Keep rendering logic separate from update logic
    }
}

// ============================================================================
// 5. PERFORMANCE CONSIDERATIONS
// ============================================================================

// For large numbers of elements:
// - Pre-calculate what you can
// - Use simple collision detection (spatial hashing if needed)
// - Limit expensive operations (sqrt, trig) when possible
// - Consider using p5 vectors efficiently

// For smooth animation:
// - Aim for 60fps
// - Profile if things are slow
// - Consider reducing particle counts or simplifying calculations

// ============================================================================
// 6. UTILITY FUNCTIONS
// ============================================================================

// Color utilities
function hexToRgb(hex) {
    const result = /^#?([a-f\d]{2})([a-f\d]{2})([a-f\d]{2})$/i.exec(hex);
    return result ? {
        r: parseInt(result[1], 16),
        g: parseInt(result[2], 16),
        b: parseInt(result[3], 16)
    } : null;
}

function colorFromPalette(index) {
    return params.colorPalette[index % params.colorPalette.length];
}

// Mapping and easing
function mapRange(value, inMin, inMax, outMin, outMax) {
    return outMin + (outMax - outMin) * ((value - inMin) / (inMax - inMin));
}

function easeInOutCubic(t) {
    return t < 0.5 ? 4 * t * t * t : 1 - Math.pow(-2 * t + 2, 3) / 2;
}

// Constrain to bounds
function wrapAround(value, max) {
    if (value < 0) return max;
    if (value > max) return 0;
    return value;
}

// ============================================================================
// 7. PARAMETER UPDATES (Connect to UI)
// ============================================================================

function updateParameter(paramName, value) {
    params[paramName] = value;
    // Decide if you need to regenerate or just update
    // Some params can update in real-time, others need full regeneration
}

function regenerate() {
    // Reinitialize your generative system
    // Useful when parameters change significantly
    initializeSeed(params.seed);
    // Then regenerate your system
}

// ============================================================================
// 8. COMMON P5.JS PATTERNS
// ============================================================================

// Drawing with transparency for trails/fading
function fadeBackground(opacity) {
    fill(250, 249, 245, opacity); // Anthropic light with alpha
    noStroke();
    rect(0, 0, width, height);
}

// Using noise for organic variation
function getNoiseValue(x, y, scale = 0.01) {
    return noise(x * scale, y * scale);
}

// Creating vectors from angles
function vectorFromAngle(angle, magnitude = 1) {
    return createVector(cos(angle), sin(angle)).mult(magnitude);
}

// ============================================================================
// 9. EXPORT FUNCTIONS
// ============================================================================

function exportImage() {
    saveCanvas('generative-art-' + params.seed, 'png');
}

// ============================================================================
// REMEMBER
// ============================================================================
//
// These are TOOLS and PRINCIPLES, not a recipe.
// Your algorithmic philosophy should guide WHAT you create.
// This structure helps you create it WELL.
//
// Focus on:
// - Clean, readable code
// - Parameterized for exploration
// - Seeded for reproducibility
// - Performant execution
//
// The art itself is entirely up to you!
//
// ============================================================================