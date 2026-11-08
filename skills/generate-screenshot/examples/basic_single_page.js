/**
 * Basic Single Page Screenshot
 *
 * Captures the home page across all three viewports (desktop, tablet, mobile)
 * in both light and dark mode. This is the default behaviour when running
 * /generate-screenshot with no arguments.
 *
 * Usage (manual):
 *   cd ~/.claude/skills/generate-screenshot && node run.js examples/basic_single_page.js
 *
 * Usage (via Claude):
 *   /generate-screenshot
 *
 * Output (6 screenshots):
 *   screenshots/
 *   ├── home--desktop--light.png
 *   ├── home--desktop--dark.png
 *   ├── home--tablet--light.png
 *   ├── home--tablet--dark.png
 *   ├── home--mobile--light.png
 *   └── home--mobile--dark.png
 */

const { chromium } = require('playwright');
const path = require('path');
const fs = require('fs');

(async () => {
  const baseUrl = process.env.BASE_URL || 'http://localhost:5173';
  const outputDir = process.env.OUTPUT_DIR || path.resolve(process.cwd(), 'screenshots');

  const viewports = {
    desktop: { width: 1920, height: 1080 },
    tablet: { width: 768, height: 1024 },
    mobile: { width: 375, height: 812 },
  };
  const modes = ['light', 'dark'];

  fs.mkdirSync(outputDir, { recursive: true });

  const browser = await chromium.launch({ headless: true });
  const screenshots = [];

  for (const mode of modes) {
    for (const [vpName, vpSize] of Object.entries(viewports)) {
      const context = await browser.newContext({
        viewport: vpSize,
        colorScheme: mode,
      });
      const page = await context.newPage();
      const fileName = `home--${vpName}--${mode}.png`;
      const filePath = path.resolve(outputDir, fileName);

      try {
        await page.goto(baseUrl, { waitUntil: 'networkidle', timeout: 30000 });
        await page.waitForTimeout(500);
        await page.screenshot({ path: filePath, fullPage: true });
        screenshots.push({ file: fileName, status: 'ok' });
        console.log(`  OK ${fileName}`);
      } catch (err) {
        screenshots.push({ file: fileName, status: 'failed', error: err.message });
        console.error(`  FAIL ${fileName} - ${err.message}`);
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
