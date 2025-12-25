/**
 * Render HTML slides to PNG images using Puppeteer
 *
 * This script provides high-fidelity rendering of complex HTML slides
 * that may not convert well using the html2pptx approach.
 *
 * Use this when your slides contain:
 * - Complex SVG diagrams
 * - CSS gradients or advanced styling
 * - Intricate layouts that don't convert properly
 *
 * Usage:
 *   node render-slides.js <slides-dir> <output-dir> [options]
 *
 * Options:
 *   --width=960      Viewport width in pixels (default: 960)
 *   --height=540     Viewport height in pixels (default: 540)
 *   --scale=2        Device scale factor for high-DPI (default: 2)
 *   --pattern=*.html Glob pattern for slide files (default: *.html)
 *
 * Example:
 *   node render-slides.js ./slides ./slide-images --scale=2
 */

const puppeteer = require('puppeteer');
const path = require('path');
const fs = require('fs');

async function renderSlides(slidesDir, outputDir, options = {}) {
    const {
        width = 960,
        height = 540,
        scale = 2,
        pattern = '*.html',
        headless = true
    } = options;

    // Create output directory if it doesn't exist
    if (!fs.existsSync(outputDir)) {
        fs.mkdirSync(outputDir, { recursive: true });
    }

    // Find all HTML files matching pattern
    const files = fs.readdirSync(slidesDir)
        .filter(f => {
            if (pattern === '*.html') return f.endsWith('.html');
            // Simple glob matching for patterns like 'slide*.html'
            const regex = new RegExp('^' + pattern.replace('*', '.*') + '$');
            return regex.test(f);
        })
        .sort();

    if (files.length === 0) {
        console.error(`No files matching '${pattern}' found in ${slidesDir}`);
        process.exit(1);
    }

    console.log(`Rendering ${files.length} slides at ${width * scale}x${height * scale} (${scale}x scale)...`);

    // Use --no-sandbox in CI environments (GitHub Actions, etc.)
    const browserArgs = process.env.CI ? ['--no-sandbox', '--disable-setuid-sandbox'] : [];

    const browser = await puppeteer.launch({
        headless,
        args: browserArgs
    });
    const page = await browser.newPage();

    await page.setViewport({
        width: width,
        height: height,
        deviceScaleFactor: scale
    });

    const results = [];

    for (const file of files) {
        const htmlPath = path.resolve(slidesDir, file);
        const imageName = file.replace('.html', '.png');
        const imagePath = path.join(outputDir, imageName);

        console.log(`  Rendering: ${file}`);

        try {
            await page.goto(`file://${htmlPath}`, {
                waitUntil: 'domcontentloaded',
                timeout: 30000
            });

            await page.screenshot({
                path: imagePath,
                type: 'png',
                omitBackground: false
            });

            results.push({ file, imagePath, success: true });
        } catch (error) {
            console.error(`    Error: ${error.message}`);
            results.push({ file, error: error.message, success: false });
        }
    }

    await browser.close();

    const successful = results.filter(r => r.success).length;
    console.log(`\nRendered ${successful}/${files.length} slides to: ${outputDir}`);

    return results;
}

/**
 * Render a single HTML string or file to PNG
 * Useful for rendering standalone diagrams
 */
async function renderHtml(htmlContent, outputPath, options = {}) {
    const {
        width = 1000,
        height = 600,
        scale = 2,
        isFile = false
    } = options;

    // Use --no-sandbox in CI environments (GitHub Actions, etc.)
    const browserArgs = process.env.CI ? ['--no-sandbox', '--disable-setuid-sandbox'] : [];

    const browser = await puppeteer.launch({
        headless: true,
        args: browserArgs
    });
    const page = await browser.newPage();

    await page.setViewport({
        width: width,
        height: height,
        deviceScaleFactor: scale
    });

    if (isFile) {
        await page.goto(`file://${path.resolve(htmlContent)}`, {
            waitUntil: 'domcontentloaded',
            timeout: 30000
        });
    } else {
        await page.setContent(htmlContent, {
            waitUntil: 'domcontentloaded',
            timeout: 30000
        });
    }

    // Get actual content bounds for auto-sizing
    const bodyHandle = await page.$('body');
    const boundingBox = await bodyHandle.boundingBox();

    await page.screenshot({
        path: outputPath,
        type: 'png',
        clip: boundingBox ? {
            x: 0,
            y: 0,
            width: Math.ceil(boundingBox.width),
            height: Math.ceil(boundingBox.height)
        } : undefined
    });

    await browser.close();
    console.log(`Rendered to: ${outputPath}`);

    return outputPath;
}

// CLI interface
if (require.main === module) {
    const args = process.argv.slice(2);

    if (args.length < 2 || args.includes('--help') || args.includes('-h')) {
        console.log(`
Usage: node render-slides.js <slides-dir> <output-dir> [options]

Options:
  --width=960      Viewport width in pixels (default: 960)
  --height=540     Viewport height in pixels (default: 540)
  --scale=2        Device scale factor for high-DPI (default: 2)
  --pattern=*.html Glob pattern for slide files (default: *.html)

Example:
  node render-slides.js ./slides ./slide-images --scale=2
        `);
        process.exit(args.includes('--help') || args.includes('-h') ? 0 : 1);
    }

    const slidesDir = args[0];
    const outputDir = args[1];

    // Parse options
    const options = {};
    for (const arg of args.slice(2)) {
        const match = arg.match(/^--(\w+)=(.+)$/);
        if (match) {
            const [, key, value] = match;
            options[key] = isNaN(value) ? value : Number(value);
        }
    }

    renderSlides(slidesDir, outputDir, options)
        .catch(err => {
            console.error('Failed to render slides:', err);
            process.exit(1);
        });
}

module.exports = { renderSlides, renderHtml };
