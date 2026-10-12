/**
 * Multi-Route Screenshot
 *
 * Captures multiple routes across all viewports and colour modes.
 * Pass routes via the ROUTES environment variable (comma-separated)
 * or edit the defaults below.
 *
 * Usage (manual):
 *   cd ~/.claude/skills/generate-screenshot && node run.js examples/multi_route.js
 *   cd ~/.claude/skills/generate-screenshot && ROUTES="/,/login,/dashboard,/settings" node run.js examples/multi_route.js
 *
 * Usage (via Claude):
 *   /generate-screenshot /login /dashboard /settings
 *
 * Output (24 screenshots for 4 routes x 3 viewports x 2 modes):
 *   screenshots/
 *   ├── home--desktop--light.png
 *   ├── home--desktop--dark.png
 *   ├── home--tablet--light.png
 *   ├── ...
 *   ├── login--desktop--light.png
 *   ├── login--desktop--dark.png
 *   ├── ...
 *   ├── dashboard--desktop--light.png
 *   ├── ...
 *   └── settings--mobile--dark.png
 */

const { chromium } = require('playwright');
const path = require('path');
const fs = require('fs');

(async () => {
  const baseUrl = process.env.BASE_URL || 'http://localhost:5173';
  const outputDir = process.env.OUTPUT_DIR || path.resolve(process.cwd(), 'screenshots');

  const defaultRoutes = ['/', '/login', '/dashboard', '/settings'];
  const routes = process.env.ROUTES
    ? process.env.ROUTES.split(',').map(r => r.trim())
    : defaultRoutes;

  const viewports = {
    desktop: { width: 1920, height: 1080 },
    tablet: { width: 768, height: 1024 },
    mobile: { width: 375, height: 812 },
  };
  const modes = ['light', 'dark'];

  fs.mkdirSync(outputDir, { recursive: true });

  console.log(`Base URL: ${baseUrl}`);
  console.log(`Routes: ${routes.join(', ')}`);
  console.log(`Output: ${outputDir}\n`);

  const browser = await chromium.launch({ headless: true });
  const screenshots = [];

  for (const mode of modes) {
    for (const [vpName, vpSize] of Object.entries(viewports)) {
      const context = await browser.newContext({
        viewport: vpSize,
        colorScheme: mode,
      });
      const page = await context.newPage();

      for (const route of routes) {
        const url = `${baseUrl}${route}`;
        const routeName = route === '/' ? 'home' : route.replace(/^\//, '').replace(/\//g, '-');
        const fileName = `${routeName}--${vpName}--${mode}.png`;
        const filePath = path.resolve(outputDir, fileName);

        try {
          await page.goto(url, { waitUntil: 'networkidle', timeout: 30000 });
          await page.waitForTimeout(500);
          await page.screenshot({ path: filePath, fullPage: true });
          screenshots.push({ route, viewport: vpName, mode, file: fileName, status: 'ok' });
          console.log(`  OK ${fileName}`);
        } catch (err) {
          screenshots.push({ route, viewport: vpName, mode, file: fileName, status: 'failed', error: err.message });
          console.error(`  FAIL ${fileName} - ${err.message}`);
        }
      }

      await context.close();
    }
  }

  await browser.close();

  const ok = screenshots.filter(s => s.status === 'ok').length;
  const failed = screenshots.filter(s => s.status === 'failed').length;
  console.log(`\nDone: ${ok} captured, ${failed} failed, ${screenshots.length} total.`);
  console.log(`Screenshots saved to: ${outputDir}`);
})();
