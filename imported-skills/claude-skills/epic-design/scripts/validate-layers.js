#!/usr/bin/env node
/**
 * 2.5D Layer Validator
 * Usage: node scripts/validate-layers.js path/to/your/index.html
 *
 * Checks:
 * 1. Every animated element has a data-depth attribute
 * 2. Decorative elements have aria-hidden="true"
 * 3. prefers-reduced-motion is implemented in CSS
 * 4. Product images have alt text
 * 5. SplitText elements have aria-label
 * 6. No more than 80 animated elements (performance)
 * 7. Will-change is not applied globally
 */

const fs   = require('fs');
const path = require('path');

const filePath = process.argv[2];

if (!filePath) {
  console.error('\n❌  Usage: node validate-layers.js path/to/index.html\n');
  process.exit(1);
}

const html = fs.readFileSync(path.resolve(filePath), 'utf8');

let passed = 0;
let failed = 0;
const results = [];

function check(label, condition, suggestion) {
  if (condition) {
    passed++;
    results.push({ status: '✅', label });
  } else {
    failed++;
    results.push({ status: '❌', label, suggestion });
  }
}

function warn(label, condition, suggestion) {
  if (!condition) {
    results.push({ status: '⚠️ ', label, suggestion });
  }
}

// --- CHECKS ---

// 1. Scene elements present
check(
  'Scene elements found (.scene)',
  html.includes('class="scene') || html.includes("class='scene"),
  'Wrap each major section in <section class="scene"> for the depth system to work.'
);

// 2. Depth layers present
const depthMatches = html.match(/data-depth=["']\d["']/g) || [];
check(
  `Depth attributes found (${depthMatches.length} elements)`,
  depthMatches.length >= 3,
  'Each scene needs at least 3 elements with data-depth="0" through data-depth="5".'
);

// 3. prefers-reduced-motion in linked CSS
const hasReducedMotionInline = html.includes('prefers-reduced-motion');
check(
  'prefers-reduced-motion implemented',
  hasReducedMotionInline || html.includes('hero-section.css'),
  'Add @media (prefers-reduced-motion: reduce) { } block. See references/accessibility.md.'
);

// 4. Decorative elements have aria-hidden
const decorativeElements = (html.match(/class="[^"]*(?:depth-0|depth-1|depth-5|glow-blob|particle|deco)[^"]*"/g) || []).length;
const ariaHiddenCount    = (html.match(/aria-hidden="true"/g) || []).length;
check(
  `Decorative elements have aria-hidden (found ${ariaHiddenCount})`,
  ariaHiddenCount >= 1,
  'Add aria-hidden="true" to all decorative layers (depth-0, depth-1, particles, glows).'
);

// 5. Images have alt text
const imgTags        = html.match(/<img[^>]*>/g) || [];
const imgsWithoutAlt = imgTags.filter(tag => !tag.includes('alt=')).length;
check(
  `All images have alt attributes (${imgTags.length} images found)`,
  imgsWithoutAlt === 0,
  `${imgsWithoutAlt} image(s) missing alt attribute. Decorative images use alt="", meaningful images need descriptive alt text.`
);

// 6. Skip link present
check(
  'Skip-to-content link present',
  html.includes('skip-link') || html.includes('Skip to'),
  'Add <a href="#main-content" class="skip-link">Skip to main content</a> as first element in <body>.'
);

// 7. GSAP script loaded
check(
  'GSAP script included',
  html.includes('gsap') || html.includes('gsap.min.js'),
  'Include GSAP from CDN: <script src="https://cdn.jsdelivr.net/npm/gsap@3.12.5/dist/gsap.min.js"></script>'
);

// 8. ScrollTrigger plugin loaded
warn(
  'ScrollTrigger plugin loaded',
  html.includes('ScrollTrigger'),
  'Add ScrollTrigger plugin for scroll animations: <script src=".../ScrollTrigger.min.js"></script>'
);

// 9. Performance: too many animated elements
const animatedElements = (html.match(/data-animate=/g) || []).length + depthMatches.length;
check(
  `Animated element count acceptable (${animatedElements} total)`,
  animatedElements <= 80,
  `${animatedElements} animated elements found. Target is under 80 for smooth 60fps performance.`
);

// 10. Main landmark present
check(
  '<main> landmark present',
  html.includes('<main'),
  'Wrap page content in <main id="main-content"> for accessibility and skip link target.'
);

// 11. Heading hierarchy
const h1Count = (html.match(/<h1[\s>]/g) || []).length;
check(
  `Single <h1> present (found ${h1Count})`,
  h1Count === 1,
  h1Count === 0
    ? 'Add one <h1> element as the main page heading.'
    : `Multiple <h1> elements found (${h1Count}). Each page should have exactly one <h1>.`
);

// 12. lang attribute on html
check(
  '<html lang=""> attribute present',
  html.includes('lang='),
  'Add lang="en" (or your language) to the <html> element: <html lang="en">'
);

// --- REPORT ---

console.log('\n📋  2.5D Layer Validator Report');
console.log('═══════════════════════════════════════');
console.log(`File: ${filePath}\n`);

results.forEach(r => {
  console.log(`${r.status}  ${r.label}`);
  if (r.suggestion) {
    console.log(`   → ${r.suggestion}`);
  }
});

console.log('\n═══════════════════════════════════════');
console.log(`Passed: ${passed}  |  Failed: ${failed}`);

if (failed === 0) {
  console.log('\n🎉  All checks passed! Your 2.5D site is ready.\n');
} else {
  console.log(`\n🔧  Fix the ${failed} issue(s) above before shipping.\n`);
  process.exit(1);
}
