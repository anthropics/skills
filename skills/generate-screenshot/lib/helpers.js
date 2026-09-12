/**
 * Helper utilities for the generate-screenshot skill.
 */

const http = require('http');
const https = require('https');

/**
 * Common development server ports to check.
 */
const DEFAULT_PORTS = [
  3000, 3001, 3002, 4200, 5000, 5173, 5174, 8000, 8080, 8888, 9000, 1234,
];

/**
 * Default viewport configurations.
 */
const VIEWPORTS = {
  desktop: { width: 1920, height: 1080 },
  tablet: { width: 768, height: 1024 },
  mobile: { width: 375, height: 812 },
};

/**
 * Default colour modes.
 */
const COLOUR_MODES = ['light', 'dark'];

/**
 * Check if a server is running on a given port.
 *
 * @param {number} port
 * @param {string} host
 * @returns {Promise<{port: number, url: string, status: number} | null>}
 */
function checkPort(port, host = 'localhost') {
  return new Promise((resolve) => {
    const url = `http://${host}:${port}`;
    const req = http.get(url, { timeout: 2000 }, (res) => {
      resolve({ port, url, status: res.statusCode });
      res.resume();
    });
    req.on('error', () => resolve(null));
    req.on('timeout', () => {
      req.destroy();
      resolve(null);
    });
  });
}

/**
 * Detect running dev servers on common ports.
 *
 * @param {number[]} [customPorts] - Additional ports to check.
 * @returns {Promise<Array<{port: number, url: string, status: number}>>}
 */
async function detectDevServers(customPorts = []) {
  const ports = [...new Set([...DEFAULT_PORTS, ...customPorts])];
  const results = await Promise.all(ports.map((p) => checkPort(p)));
  return results.filter(Boolean);
}

/**
 * Convert a route path to a safe filename segment.
 *
 * @param {string} route - The route path (e.g. '/dashboard/settings').
 * @returns {string} Safe filename segment (e.g. 'dashboard-settings').
 */
function routeToFilename(route) {
  if (route === '/') return 'home';
  return route
    .replace(/^\//, '')
    .replace(/\//g, '-')
    .replace(/[^a-zA-Z0-9-_]/g, '_');
}

/**
 * Build the screenshot filename.
 *
 * @param {string} route
 * @param {string} viewport - e.g. 'desktop', 'mobile', 'tablet'
 * @param {string} mode - e.g. 'light', 'dark'
 * @returns {string}
 */
function buildFilename(route, viewport, mode) {
  return `${routeToFilename(route)}--${viewport}--${mode}.png`;
}

/**
 * Attempt to dismiss common cookie/consent banners.
 *
 * @param {import('playwright').Page} page
 * @param {number} [timeout=3000]
 */
async function dismissCookieBanner(page, timeout = 3000) {
  const selectors = [
    '[data-testid="cookie-accept"]',
    '[data-testid="accept-cookies"]',
    'button:has-text("Accept")',
    'button:has-text("Accept all")',
    'button:has-text("Accept All")',
    'button:has-text("Got it")',
    'button:has-text("I agree")',
    'button:has-text("OK")',
    '.cookie-banner button',
    '#cookie-consent button',
    '[class*="cookie"] button',
    '[class*="consent"] button',
  ];

  for (const selector of selectors) {
    try {
      const el = await page.waitForSelector(selector, { timeout });
      if (el) {
        await el.click();
        await page.waitForTimeout(300);
        return true;
      }
    } catch {
      // Selector not found, try next
    }
  }
  return false;
}

/**
 * Wait for a page to be fully ready (network idle + optional delay).
 *
 * @param {import('playwright').Page} page
 * @param {object} [options]
 * @param {number} [options.settleDelay=500] - Extra ms to wait after network idle.
 * @param {number} [options.timeout=30000] - Navigation timeout in ms.
 */
async function waitForPageReady(page, options = {}) {
  const { settleDelay = 500, timeout = 30000 } = options;
  await page.waitForLoadState('networkidle', { timeout });
  await page.waitForTimeout(settleDelay);
}

module.exports = {
  DEFAULT_PORTS,
  VIEWPORTS,
  COLOUR_MODES,
  detectDevServers,
  routeToFilename,
  buildFilename,
  dismissCookieBanner,
  waitForPageReady,
  checkPort,
};
