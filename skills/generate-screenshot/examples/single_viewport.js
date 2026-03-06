/**
 * Single Viewport Screenshot
 *
 * Captures routes using only one viewport and one colour mode.
 * Useful for quick captures or CI pipelines where you only need
 * a specific combination.
 *
 * Usage (manual):
 *   cd ~/.claude/skills/generate-screenshot && node run.js examples/single_viewport.js
 *   cd ~/.claude/skills/generate-screenshot && VIEWPORT=mobile MODE=dark node run.js examples/single_viewport.js
 *
 * Usage (via Claude):
 *   /generate-screenshot / --viewports mobile --modes dark
 *
 * Environment variables:
 *   BASE_URL   - Target URL (default: http://localhost:5173)
 *   OUTPUT_DIR - Output directory (default: ./screenshots)
 *   ROUTES     - Comma-separated routes (default: /)
 *   VIEWPORT   - One of: desktop, tablet, mobile (default: desktop)
 *   MODE       - One of: light, dark (default: light)
 *
 * Output (1 screenshot per route):
 *   screenshots/
 *   └── home--desktop--light.png
 */

const { chromium } = require('playwright');
const path = require('path');
const fs = require('fs');

(async () => {
  const baseUrl = process.env.BASE_URL || 'http://localhost:5173';
  const outputDir = process.env.OUTPUT_DIR || path.resolve(process.cwd(), 'screenshots');

  const routes = process.env.ROUTES
    ? process.env.ROUTES.split(',').map(r => r.trim())
    : ['/'];

  const allViewports = {
    desktop: { width: 1920, height: 1080 },
    tablet: { width: 768, height: 1024 },
    mobile: { width: 375, height: 812 },
  };

  const vpName = process.env.VIEWPORT || 'desktop';
  const mode = process.env.MODE || 'light';
  const vpSize = allViewports[vpName];

  if (!vpSize) {
    console.error(`Unknown viewport: "${vpName}". Use one of: desktop, tablet, mobile`);
    process.exit(1);
  }

  if (!['light', 'dark'].includes(mode)) {
    console.error(`Unknown mode: "${mode}". Use one of: light, dark`);
    process.exit(1);
  }

  fs.mkdirSync(outputDir, { recursive: true });

  console.log(`Viewport: ${vpName} (${vpSize.width}x${vpSize.height})`);
  console.log(`Mode: ${mode}`);
  console.log(`Routes: ${routes.join(', ')}\n`);

  const browser = await chromium.launch({ headless: true });
  const context = await browser.newContext({
    viewport: vpSize,
    colorScheme: mode,
  });
  const page = await context.newPage();
  const screenshots = [];

  for (const route of routes) {
    const url = `${baseUrl}${route}`;
    const routeName = route === '/' ? 'home' : route.replace(/^\//, '').replace(/\//g, '-');
    const fileName = `${routeName}--${vpName}--${mode}.png`;
    const filePath = path.resolve(outputDir, fileName);

    try {
      await page.goto(url, { waitUntil: 'networkidle', timeout: 30000 });
      await page.waitForTimeout(500);
      await page.screenshot({ path: filePath, fullPage: true });
      screenshots.push({ route, file: fileName, status: 'ok' });
      console.log(`  OK ${fileName}`);
    } catch (err) {
      screenshots.push({ route, file: fileName, status: 'failed', error: err.message });
      console.error(`  FAIL ${fileName} - ${err.message}`);
    }
  }

  await context.close();
  await browser.close();

  const ok = screenshots.filter(s => s.status === 'ok').length;
  const failed = screenshots.filter(s => s.status === 'failed').length;
  console.log(`\nDone: ${ok} captured, ${failed} failed, ${screenshots.length} total.`);
  console.log(`Screenshots saved to: ${outputDir}`);
})();
