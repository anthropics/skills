/**
 * Test the image-based PPTX workflow
 *
 * This script tests:
 * 1. HTML to PNG rendering with Puppeteer
 * 2. PPTX creation from PNG images
 * 3. Diagram overlay functionality
 */

const path = require('path');
const fs = require('fs');
const assert = require('assert');

const { renderSlides, renderHtml } = require('../scripts/render-slides.js');
const { createPresentation } = require('../scripts/create-from-images.js');

const testDir = __dirname;
const slidesDir = path.join(testDir, 'slides');
const outputDir = path.join(testDir, 'output');

async function cleanup() {
    if (fs.existsSync(outputDir)) {
        fs.rmSync(outputDir, { recursive: true });
    }
    fs.mkdirSync(outputDir, { recursive: true });
}

async function testRenderSlides() {
    console.log('\n📸 Test 1: Render HTML slides to PNG...');

    const results = await renderSlides(slidesDir, outputDir, {
        width: 960,
        height: 540,
        scale: 2
    });

    assert(results.length > 0, 'Should render at least one slide');
    assert(results.every(r => r.success), 'All slides should render successfully');

    const outputFile = path.join(outputDir, 'test-slide.png');
    assert(fs.existsSync(outputFile), 'Output PNG should exist');

    const stats = fs.statSync(outputFile);
    assert(stats.size > 10000, 'PNG should be a reasonable size (>10KB)');

    console.log('   ✅ Rendered', results.length, 'slide(s)');
    console.log('   ✅ Output file size:', Math.round(stats.size / 1024), 'KB');
}

async function testRenderHtml() {
    console.log('\n📸 Test 2: Render single HTML to PNG...');

    const diagramHtml = `<!DOCTYPE html>
<html>
<head>
<style>
body { margin: 0; padding: 20px; background: white; }
svg { display: block; }
</style>
</head>
<body>
<svg viewBox="0 0 200 100" width="200" height="100" xmlns="http://www.w3.org/2000/svg">
  <rect x="10" y="10" width="80" height="80" fill="#dc2626" rx="8"/>
  <rect x="110" y="10" width="80" height="80" fill="#16a34a" rx="8"/>
  <text x="50" y="55" text-anchor="middle" fill="white" font-size="12">Fixed</text>
  <text x="150" y="55" text-anchor="middle" fill="white" font-size="12">Custom</text>
</svg>
</body>
</html>`;

    const outputFile = path.join(outputDir, 'diagram.png');
    await renderHtml(diagramHtml, outputFile, {
        width: 240,
        height: 140,
        scale: 2,
        isFile: false
    });

    assert(fs.existsSync(outputFile), 'Diagram PNG should exist');

    const stats = fs.statSync(outputFile);
    assert(stats.size > 1000, 'Diagram PNG should be a reasonable size (>1KB)');

    console.log('   ✅ Rendered diagram');
    console.log('   ✅ Output file size:', Math.round(stats.size / 1024), 'KB');
}

async function testCreatePresentation() {
    console.log('\n📊 Test 3: Create PPTX from images...');

    const outputPptx = path.join(outputDir, 'test-presentation.pptx');

    await createPresentation(outputDir, outputPptx);

    assert(fs.existsSync(outputPptx), 'PPTX file should exist');

    const stats = fs.statSync(outputPptx);
    assert(stats.size > 10000, 'PPTX should be a reasonable size (>10KB)');

    console.log('   ✅ Created presentation');
    console.log('   ✅ Output file size:', Math.round(stats.size / 1024), 'KB');
}

async function testCreatePresentationWithConfig() {
    console.log('\n📊 Test 4: Create PPTX with diagram overlay...');

    const config = {
        title: 'Test Presentation',
        author: 'CI Test',
        layout: 'LAYOUT_16x9',
        slides: [
            {
                image: 'test-slide.png',
                diagram: 'diagram.png',
                diagramPos: { x: 6, y: 2, w: 3, h: 2 }
            }
        ]
    };

    const configPath = path.join(outputDir, 'config.json');
    fs.writeFileSync(configPath, JSON.stringify(config, null, 2));

    const outputPptx = path.join(outputDir, 'test-with-overlay.pptx');
    await createPresentation(outputDir, outputPptx, configPath);

    assert(fs.existsSync(outputPptx), 'PPTX with overlay should exist');

    const stats = fs.statSync(outputPptx);
    assert(stats.size > 10000, 'PPTX should be a reasonable size (>10KB)');

    console.log('   ✅ Created presentation with diagram overlay');
    console.log('   ✅ Output file size:', Math.round(stats.size / 1024), 'KB');
}

async function runTests() {
    console.log('🧪 Running PPTX Skill Tests\n');
    console.log('================================');

    try {
        await cleanup();
        await testRenderSlides();
        await testRenderHtml();
        await testCreatePresentation();
        await testCreatePresentationWithConfig();

        console.log('\n================================');
        console.log('✅ All tests passed!\n');
        process.exit(0);
    } catch (error) {
        console.error('\n================================');
        console.error('❌ Test failed:', error.message);
        console.error(error.stack);
        process.exit(1);
    }
}

runTests();
