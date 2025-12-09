/**
 * Test the image-based PPTX workflow
 *
 * This script tests the complete workflow for creating presentations
 * from complex HTML slides - the kind Claude would generate when asked
 * to create professional presentations with:
 * - SVG architecture diagrams
 * - CSS gradients and advanced styling
 * - Dashboard layouts with charts
 * - Diagram overlays
 *
 * Test slides simulate real Claude-generated content:
 * - test-slide.html: Basic slide with SVG and gradients
 * - architecture-slide.html: System architecture diagram
 * - metrics-slide.html: Dashboard with KPIs and charts
 * - diagram-overlay.html: Standalone diagram for overlay
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

/**
 * Test 1: Render all complex HTML slides to PNG
 * Validates that Puppeteer correctly renders:
 * - CSS gradients and backgrounds
 * - SVG diagrams with filters and gradients
 * - Flexbox and grid layouts
 * - Multiple font styles and colors
 */
async function testRenderComplexSlides() {
    console.log('\n[Test 1] Render complex HTML slides to PNG...');

    const results = await renderSlides(slidesDir, outputDir, {
        width: 960,
        height: 540,
        scale: 2
    });

    // Should render all test slides
    const expectedSlides = ['test-slide.html', 'architecture-slide.html', 'metrics-slide.html', 'diagram-overlay.html'];
    assert(results.length >= expectedSlides.length, `Should render at least ${expectedSlides.length} slides, got ${results.length}`);
    assert(results.every(r => r.success), 'All slides should render successfully');

    // Verify each expected slide was rendered
    for (const slideName of expectedSlides) {
        const pngName = slideName.replace('.html', '.png');
        const pngPath = path.join(outputDir, pngName);
        assert(fs.existsSync(pngPath), `${pngName} should exist`);

        const stats = fs.statSync(pngPath);
        assert(stats.size > 5000, `${pngName} should be >5KB (got ${Math.round(stats.size/1024)}KB)`);
    }

    console.log(`   OK: Rendered ${results.length} slides`);
    results.forEach(r => {
        const size = Math.round(fs.statSync(r.imagePath).size / 1024);
        console.log(`   - ${path.basename(r.imagePath)}: ${size}KB`);
    });
}

/**
 * Test 2: Render standalone diagram from HTML string
 * Tests the renderHtml function for creating diagram overlays
 */
async function testRenderDiagramFromString() {
    console.log('\n[Test 2] Render diagram from HTML string...');

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
  <text x="50" y="55" text-anchor="middle" fill="white" font-size="12">Input</text>
  <text x="150" y="55" text-anchor="middle" fill="white" font-size="12">Output</text>
  <line x1="90" y1="50" x2="110" y2="50" stroke="#64748b" stroke-width="2" marker-end="url(#arr)"/>
  <defs><marker id="arr" markerWidth="6" markerHeight="6" refX="5" refY="3" orient="auto">
    <polygon points="0 0, 6 3, 0 6" fill="#64748b"/>
  </marker></defs>
</svg>
</body>
</html>`;

    const outputFile = path.join(outputDir, 'inline-diagram.png');
    await renderHtml(diagramHtml, outputFile, {
        width: 240,
        height: 140,
        scale: 2,
        isFile: false
    });

    assert(fs.existsSync(outputFile), 'Inline diagram PNG should exist');
    const stats = fs.statSync(outputFile);
    assert(stats.size > 1000, 'Diagram PNG should be >1KB');

    console.log(`   OK: Rendered inline diagram (${Math.round(stats.size/1024)}KB)`);
}

/**
 * Test 3: Render diagram from HTML file
 * Tests rendering the diagram-overlay.html file
 */
async function testRenderDiagramFromFile() {
    console.log('\n[Test 3] Render diagram from HTML file...');

    const diagramFile = path.join(slidesDir, 'diagram-overlay.html');
    const outputFile = path.join(outputDir, 'file-diagram.png');

    await renderHtml(diagramFile, outputFile, {
        width: 400,
        height: 300,
        scale: 2,
        isFile: true
    });

    assert(fs.existsSync(outputFile), 'File-based diagram PNG should exist');
    const stats = fs.statSync(outputFile);
    assert(stats.size > 2000, 'Diagram PNG should be >2KB');

    console.log(`   OK: Rendered file-based diagram (${Math.round(stats.size/1024)}KB)`);
}

/**
 * Test 4: Create basic PPTX from all rendered images
 * Tests auto-discovery of PNG files
 */
async function testCreateBasicPresentation() {
    console.log('\n[Test 4] Create PPTX from rendered images...');

    const outputPptx = path.join(outputDir, 'basic-presentation.pptx');
    await createPresentation(outputDir, outputPptx);

    assert(fs.existsSync(outputPptx), 'PPTX file should exist');
    const stats = fs.statSync(outputPptx);
    assert(stats.size > 50000, 'PPTX should be >50KB (multiple slides)');

    console.log(`   OK: Created presentation (${Math.round(stats.size/1024)}KB)`);
}

/**
 * Test 5: Create PPTX with diagram overlay configuration
 * Tests the full workflow with explicit slide ordering and overlay positioning
 */
async function testCreatePresentationWithOverlay() {
    console.log('\n[Test 5] Create PPTX with diagram overlay...');

    const config = {
        title: 'Complex Presentation Test',
        author: 'Claude Code CI',
        subject: 'Testing image-based PPTX workflow',
        layout: 'LAYOUT_16x9',
        slides: [
            { image: 'architecture-slide.png' },
            { image: 'metrics-slide.png' },
            {
                image: 'test-slide.png',
                diagram: 'file-diagram.png',
                diagramPos: { x: 5.5, y: 1.5, w: 4, h: 3 }
            }
        ]
    };

    const configPath = path.join(outputDir, 'presentation-config.json');
    fs.writeFileSync(configPath, JSON.stringify(config, null, 2));

    const outputPptx = path.join(outputDir, 'presentation-with-overlay.pptx');
    await createPresentation(outputDir, outputPptx, configPath);

    assert(fs.existsSync(outputPptx), 'PPTX with overlay should exist');
    const stats = fs.statSync(outputPptx);
    assert(stats.size > 100000, 'PPTX with overlay should be >100KB');

    console.log(`   OK: Created presentation with overlay (${Math.round(stats.size/1024)}KB)`);
}

/**
 * Test 6: Verify PPTX structure (basic validation)
 * PPTX files are ZIP archives - verify basic structure
 */
async function testVerifyPptxStructure() {
    console.log('\n[Test 6] Verify PPTX file structure...');

    const pptxPath = path.join(outputDir, 'presentation-with-overlay.pptx');
    const pptxBuffer = fs.readFileSync(pptxPath);

    // PPTX files are ZIP archives - check for ZIP signature
    const zipSignature = pptxBuffer.slice(0, 4).toString('hex');
    assert(zipSignature === '504b0304', 'PPTX should be a valid ZIP archive (PK signature)');

    console.log('   OK: PPTX has valid ZIP structure');
}

async function runTests() {
    console.log('='.repeat(50));
    console.log('PPTX Skill Test Suite');
    console.log('Testing image-based workflow for complex slides');
    console.log('='.repeat(50));

    try {
        await cleanup();
        await testRenderComplexSlides();
        await testRenderDiagramFromString();
        await testRenderDiagramFromFile();
        await testCreateBasicPresentation();
        await testCreatePresentationWithOverlay();
        await testVerifyPptxStructure();

        console.log('\n' + '='.repeat(50));
        console.log('All tests passed!');
        console.log('='.repeat(50) + '\n');
        process.exit(0);
    } catch (error) {
        console.error('\n' + '='.repeat(50));
        console.error('TEST FAILED:', error.message);
        console.error(error.stack);
        console.error('='.repeat(50) + '\n');
        process.exit(1);
    }
}

runTests();
