/**
 * Create PowerPoint presentation from rendered PNG images
 *
 * This script creates a PPTX file from pre-rendered PNG slide images,
 * with support for diagram overlays.
 *
 * Usage:
 *   node create-from-images.js <images-dir> <output.pptx> [config.json]
 *
 * The config.json file (optional) allows specifying:
 * - Slide order
 * - Diagram overlays with positioning
 * - Presentation metadata
 *
 * Example config.json:
 * {
 *   "title": "My Presentation",
 *   "author": "Author Name",
 *   "layout": "LAYOUT_16x9",
 *   "slides": [
 *     { "image": "slide01.png" },
 *     { "image": "slide02.png", "diagram": "diagram.png", "diagramPos": { "x": 1, "y": 2, "w": 4, "h": 3 } }
 *   ]
 * }
 *
 * Without config.json, all PNG files in the directory are used in sorted order.
 */

const pptxgen = require('pptxgenjs');
const path = require('path');
const fs = require('fs');

async function createPresentation(imagesDir, outputPath, configPath = null) {
    const pptx = new pptxgen();

    let config = {
        title: 'Presentation',
        author: 'Claude Code',
        layout: 'LAYOUT_16x9',
        slides: null
    };

    // Load config if provided
    if (configPath && fs.existsSync(configPath)) {
        const userConfig = JSON.parse(fs.readFileSync(configPath, 'utf-8'));
        config = { ...config, ...userConfig };
    }

    // Set presentation properties
    pptx.layout = config.layout;
    pptx.author = config.author;
    pptx.title = config.title;
    if (config.subject) pptx.subject = config.subject;
    if (config.company) pptx.company = config.company;

    // Determine slides to process
    let slideConfigs;

    if (config.slides) {
        // Use explicit slide configuration
        slideConfigs = config.slides;
    } else {
        // Auto-discover PNG files in sorted order
        const pngFiles = fs.readdirSync(imagesDir)
            .filter(f => f.endsWith('.png'))
            .sort();

        if (pngFiles.length === 0) {
            console.error(`No PNG files found in ${imagesDir}`);
            process.exit(1);
        }

        slideConfigs = pngFiles.map(image => ({ image }));
    }

    console.log(`Creating presentation with ${slideConfigs.length} slides...`);

    // Create each slide
    for (const slideConfig of slideConfigs) {
        const imagePath = path.isAbsolute(slideConfig.image)
            ? slideConfig.image
            : path.join(imagesDir, slideConfig.image);

        if (!fs.existsSync(imagePath)) {
            console.error(`  Warning: Image not found: ${imagePath}`);
            continue;
        }

        console.log(`  Adding slide: ${slideConfig.image}`);

        const slide = pptx.addSlide();

        // Add background image (full slide)
        slide.addImage({
            path: imagePath,
            x: 0,
            y: 0,
            w: '100%',
            h: '100%'
        });

        // Add diagram overlay if specified
        if (slideConfig.diagram) {
            const diagramPath = path.isAbsolute(slideConfig.diagram)
                ? slideConfig.diagram
                : path.join(imagesDir, slideConfig.diagram);

            if (fs.existsSync(diagramPath)) {
                const pos = slideConfig.diagramPos || { x: 1, y: 1, w: 4, h: 3 };
                console.log(`    + Adding diagram: ${slideConfig.diagram}`);

                slide.addImage({
                    path: diagramPath,
                    x: pos.x,
                    y: pos.y,
                    w: pos.w,
                    h: pos.h
                });
            } else {
                console.error(`    Warning: Diagram not found: ${diagramPath}`);
            }
        }
    }

    // Save the presentation
    await pptx.writeFile({ fileName: outputPath });
    console.log(`\nPresentation saved to: ${outputPath}`);

    return outputPath;
}

// CLI interface
if (require.main === module) {
    const args = process.argv.slice(2);

    if (args.length < 2 || args.includes('--help') || args.includes('-h')) {
        console.log(`
Usage: node create-from-images.js <images-dir> <output.pptx> [config.json]

Arguments:
  images-dir    Directory containing PNG slide images
  output.pptx   Output PowerPoint file path
  config.json   Optional configuration file for slide order and overlays

Without config.json, all PNG files in the directory are used in sorted order.

Example config.json:
{
  "title": "My Presentation",
  "author": "Author Name",
  "layout": "LAYOUT_16x9",
  "slides": [
    { "image": "slide01.png" },
    {
      "image": "slide02.png",
      "diagram": "diagram.png",
      "diagramPos": { "x": 1, "y": 2, "w": 4, "h": 3 }
    }
  ]
}
        `);
        process.exit(args.includes('--help') || args.includes('-h') ? 0 : 1);
    }

    const imagesDir = args[0];
    const outputPath = args[1];
    const configPath = args[2] || null;

    createPresentation(imagesDir, outputPath, configPath)
        .catch(err => {
            console.error('Failed to create presentation:', err);
            process.exit(1);
        });
}

module.exports = { createPresentation };
