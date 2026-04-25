/**
 * Authenticated Pages Screenshot
 *
 * Logs into the app first, then captures protected routes using
 * the authenticated session. Reuses the same browser context across
 * all routes so the session persists.
 *
 * Usage (manual):
 *   cd ~/.claude/skills/generate-screenshot && \
 *     USERNAME="user@example.com" PASSWORD="secret" node run.js examples/authenticated_pages.js
 *
 * Usage (via Claude):
 *   /generate-screenshot /dashboard /settings /profile
 *   (Claude will ask for credentials if login is required)
 *
 * Environment variables:
 *   BASE_URL    - Target URL (default: http://localhost:5173)
 *   OUTPUT_DIR  - Output directory (default: ./screenshots)
 *   LOGIN_URL   - Login page path (default: /login)
 *   USERNAME    - Login username/email
 *   PASSWORD    - Login password
 *   ROUTES      - Comma-separated protected routes (default: /dashboard,/settings,/profile)
 *
 * Selectors (override if your login form differs):
 *   SEL_USERNAME - Username input selector (default: input[name="email"])
 *   SEL_PASSWORD - Password input selector (default: input[name="password"])
 *   SEL_SUBMIT   - Submit button selector (default: button[type="submit"])
 *
 * Output:
 *   screenshots/
 *   ├── dashboard--desktop--light.png
 *   ├── dashboard--desktop--dark.png
 *   ├── dashboard--tablet--light.png
 *   ├── ...
 *   ├── settings--desktop--light.png
 *   ├── ...
 *   └── profile--mobile--dark.png
 */

const { chromium } = require('playwright');
const path = require('path');
const fs = require('fs');

(async () => {
  const baseUrl = process.env.BASE_URL || 'http://localhost:5173';
  const outputDir = process.env.OUTPUT_DIR || path.resolve(process.cwd(), 'screenshots');
  const loginPath = process.env.LOGIN_URL || '/login';
  const username = process.env.USERNAME || '';
  const password = process.env.PASSWORD || '';

  const selUsername = process.env.SEL_USERNAME || 'input[name="email"]';
  const selPassword = process.env.SEL_PASSWORD || 'input[name="password"]';
  const selSubmit = process.env.SEL_SUBMIT || 'button[type="submit"]';

  const routes = process.env.ROUTES
    ? process.env.ROUTES.split(',').map(r => r.trim())
    : ['/dashboard', '/settings', '/profile'];

  const viewports = {
    desktop: { width: 1920, height: 1080 },
    tablet: { width: 768, height: 1024 },
    mobile: { width: 375, height: 812 },
  };
  const modes = ['light', 'dark'];

  if (!username || !password) {
    console.error('Error: USERNAME and PASSWORD environment variables are required.');
    console.error('Usage: USERNAME="user@example.com" PASSWORD="secret" node run.js examples/authenticated_pages.js');
    process.exit(1);
  }

  fs.mkdirSync(outputDir, { recursive: true });

  console.log(`Base URL: ${baseUrl}`);
  console.log(`Login: ${loginPath}`);
  console.log(`Routes: ${routes.join(', ')}\n`);

  const browser = await chromium.launch({ headless: true });
  const screenshots = [];

  for (const mode of modes) {
    for (const [vpName, vpSize] of Object.entries(viewports)) {
      const context = await browser.newContext({
        viewport: vpSize,
        colorScheme: mode,
      });
      const page = await context.newPage();

      // --- Login ---
      try {
        console.log(`  Logging in (${vpName}, ${mode})...`);
        await page.goto(`${baseUrl}${loginPath}`, { waitUntil: 'networkidle', timeout: 30000 });
        await page.fill(selUsername, username);
        await page.fill(selPassword, password);
        await page.click(selSubmit);
        await page.waitForLoadState('networkidle', { timeout: 15000 });
        console.log('  Login successful.\n');
      } catch (err) {
        console.error(`  Login failed (${vpName}, ${mode}): ${err.message}`);
        console.error('  Skipping this viewport/mode combination.\n');
        await context.close();
        continue;
      }

      // --- Capture protected routes ---
      for (const route of routes) {
        const url = `${baseUrl}${route}`;
        const routeName = route.replace(/^\//, '').replace(/\//g, '-');
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
