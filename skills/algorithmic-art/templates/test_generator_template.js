/**
 * Tests for the pure utility functions in algorithmic-art/templates/generator_template.js.
 *
 * The template is a browser p5.js sketch (no module exports), so it is loaded
 * into a vm sandbox with stubbed p5 globals and the resulting functions are
 * exercised directly.
 */
const fs = require('fs');
const path = require('path');
const vm = require('vm');
const assert = require('assert');

const TEMPLATE_PATH = path.join(__dirname, 'generator_template.js');
const source = fs.readFileSync(TEMPLATE_PATH, 'utf-8');

// Stub the p5.js globals the template references at definition time.
// (setup/draw/etc. are only invoked when called, so the stubs are never hit
// during load.)
const sandbox = {
    randomSeed: () => {},
    noiseSeed: () => {},
    createCanvas: () => {},
    fill: () => {},
    noStroke: () => {},
    rect: () => {},
    noise: () => 0,
    cos: Math.cos,
    sin: Math.sin,
    createVector: (x, y) => ({ x, y, mult(n) { this.x *= n; this.y *= n; return this; } }),
    saveCanvas: () => {},
    Math,
    parseInt,
    console,
};
vm.createContext(sandbox);
vm.runInContext(source, sandbox);

function testHexToRgb() {
    const a = sandbox.hexToRgb('#d97757');
    assert.strictEqual(a.r, 217);
    assert.strictEqual(a.g, 119);
    assert.strictEqual(a.b, 87);
    const black = sandbox.hexToRgb('000000');
    assert.strictEqual(black.r, 0);
    assert.strictEqual(black.g, 0);
    assert.strictEqual(black.b, 0);
    const white = sandbox.hexToRgb('#ffffff');
    assert.strictEqual(white.r, 255);
    assert.strictEqual(white.g, 255);
    assert.strictEqual(white.b, 255);
    assert.strictEqual(sandbox.hexToRgb('nothex'), null);
    console.log('hexToRgb: OK');
}

function testMapRange() {
    assert.strictEqual(sandbox.mapRange(0, 0, 10, 0, 100), 0);
    assert.strictEqual(sandbox.mapRange(10, 0, 10, 0, 100), 100);
    assert.strictEqual(sandbox.mapRange(5, 0, 10, 0, 100), 50);
    console.log('mapRange: OK');
}

function testEaseInOutCubic() {
    assert.strictEqual(sandbox.easeInOutCubic(0), 0);
    assert.strictEqual(sandbox.easeInOutCubic(1), 1);
    const mid = sandbox.easeInOutCubic(0.5);
    assert.ok(mid > 0 && mid < 1, `mid should be in (0,1), got ${mid}`);
    console.log('easeInOutCubic: OK');
}

function testWrapAround() {
    // In-range values pass through (modulo)
    assert.strictEqual(sandbox.wrapAround(0, 10), 0);
    assert.strictEqual(sandbox.wrapAround(5, 10), 5);
    // The max value wraps to 0
    assert.strictEqual(sandbox.wrapAround(10, 10), 0);
    // Regression: values more than one step below 0 must wrap correctly.
    // The old implementation returned 10 for ANY negative value.
    assert.strictEqual(sandbox.wrapAround(-1, 10), 9, 'wrapAround(-1, 10) should be 9');
    assert.strictEqual(sandbox.wrapAround(-5, 10), 5, 'wrapAround(-5, 10) should be 5');
    // Values more than one step above max must wrap correctly.
    // The old implementation returned 0 for ANY value above max.
    assert.strictEqual(sandbox.wrapAround(11, 10), 1, 'wrapAround(11, 10) should be 1');
    assert.strictEqual(sandbox.wrapAround(25, 10), 5, 'wrapAround(25, 10) should be 5');
    console.log('wrapAround: OK');
}

testHexToRgb();
testMapRange();
testEaseInOutCubic();
testWrapAround();
console.log('\nAll utility function tests passed.');
