#!/usr/bin/env node
import fs from 'fs/promises';
import { existsSync } from 'fs';
import path from 'path';
import { fileURLToPath, pathToFileURL } from 'url';

let chromium;
try {
  ({ chromium } = await import('playwright'));
} catch (error) {
  console.error('Playwright is required for materials-html-deck strict verification.');
  console.error('Install it in the materials deck environment, for example: npm install playwright');
  process.exit(2);
}

function parseArgs() {
  const args = process.argv.slice(2);
  const options = {
    htmlDir: null,
    screenshots: null,
    reportJson: null,
    reportMd: null
  };
  for (let i = 0; i < args.length; i += 1) {
    const arg = args[i];
    if (arg === '--html-dir') options.htmlDir = args[++i];
    else if (arg === '--screenshots') options.screenshots = args[++i];
    else if (arg === '--report-json') options.reportJson = args[++i];
    else if (arg === '--report-md') options.reportMd = args[++i];
    else if (arg === '--help' || arg === '-h') {
      console.log('Usage: node verify_deck_html.mjs --html-dir deck_html --screenshots deck_html/screenshots [--report-json path] [--report-md path]');
      process.exit(0);
    }
  }
  if (!options.htmlDir) throw new Error('--html-dir is required');
  options.htmlDir = path.resolve(options.htmlDir);
  options.screenshots = path.resolve(options.screenshots || path.join(options.htmlDir, 'screenshots'));
  options.reportJson = options.reportJson ? path.resolve(options.reportJson) : null;
  options.reportMd = options.reportMd ? path.resolve(options.reportMd) : null;
  return options;
}

async function slideFiles(htmlDir) {
  const slidesDir = path.join(htmlDir, 'slides');
  const entries = await fs.readdir(slidesDir);
  return entries
    .filter((entry) => entry.toLowerCase().endsWith('.html'))
    .sort((a, b) => a.localeCompare(b))
    .map((entry) => path.join(slidesDir, entry));
}

function localMediaRefs(html, slidePath) {
  const refs = [];
  const pattern = /\b(?:src|href)=["']([^"']+)["']/gi;
  for (const match of html.matchAll(pattern)) {
    const raw = match[1];
    if (!raw || raw.startsWith('http:') || raw.startsWith('https:') || raw.startsWith('data:') || raw.startsWith('#')) {
      continue;
    }
    if (raw.startsWith('file:')) {
      refs.push({ raw, path: fileURLToPath(raw) });
    } else {
      refs.push({ raw, path: path.resolve(path.dirname(slidePath), raw) });
    }
  }
  return refs;
}

async function verifySlide(browser, slidePath, index, screenshotsDir) {
  const errors = [];
  const html = await fs.readFile(slidePath, 'utf8');
  for (const ref of localMediaRefs(html, slidePath)) {
    if (!existsSync(ref.path)) {
      errors.push(`missing media: ${ref.raw}`);
    }
  }

  const page = await browser.newPage({ viewport: { width: 1920, height: 1080 }, deviceScaleFactor: 1 });
  page.on('pageerror', (error) => errors.push(`pageerror: ${error.message}`));
  page.on('console', (message) => {
    if (message.type() === 'error') errors.push(`console error: ${message.text()}`);
  });

  await page.goto(pathToFileURL(slidePath).href, { waitUntil: 'networkidle' });
  const visible = await page.evaluate(() => {
    const body = document.body;
    if (!body) return { ok: false, reason: 'missing body' };
    const style = getComputedStyle(body);
    const rect = body.getBoundingClientRect();
    const text = body.innerText || '';
    const media = body.querySelectorAll('img,svg,canvas,video').length;
    if (style.visibility === 'hidden' || style.display === 'none') return { ok: false, reason: 'hidden body' };
    if (rect.width < 100 || rect.height < 100) return { ok: false, reason: 'body too small' };
    if (text.trim().length < 3 && media === 0) return { ok: false, reason: 'blank body content' };
    return { ok: true, reason: '' };
  });
  if (!visible.ok) errors.push(visible.reason);

  const screenshotPath = path.join(screenshotsDir, `slide_${String(index + 1).padStart(3, '0')}.png`);
  const screenshot = await page.screenshot({ path: screenshotPath, fullPage: false });
  if (screenshot.length < 2000) errors.push('blank screenshot');
  await page.close();

  return {
    slide: path.basename(slidePath),
    screenshot: screenshotPath,
    ok: errors.length === 0,
    errors
  };
}

function markdownReport(results) {
  const lines = ['# HTML Deck QA Report', ''];
  lines.push(`Slides checked: ${results.length}`);
  lines.push(`Failures: ${results.filter((item) => !item.ok).length}`);
  lines.push('');
  for (const result of results) {
    lines.push(`## ${result.slide}`);
    lines.push(`- status: ${result.ok ? 'pass' : 'fail'}`);
    lines.push(`- screenshot: ${result.screenshot}`);
    for (const error of result.errors) lines.push(`- error: ${error}`);
    lines.push('');
  }
  return `${lines.join('\n')}\n`;
}

async function main() {
  try {
    const options = parseArgs();
    await fs.mkdir(options.screenshots, { recursive: true });
    const slides = await slideFiles(options.htmlDir);
    if (slides.length === 0) throw new Error(`No slide HTML files found in ${path.join(options.htmlDir, 'slides')}`);

    const browser = await chromium.launch({ headless: true });
    const results = [];
    for (let index = 0; index < slides.length; index += 1) {
      results.push(await verifySlide(browser, slides[index], index, options.screenshots));
    }
    await browser.close();

    if (options.reportJson) {
      await fs.writeFile(options.reportJson, JSON.stringify({ slides: results }, null, 2), 'utf8');
    }
    if (options.reportMd) {
      await fs.writeFile(options.reportMd, markdownReport(results), 'utf8');
    }

    const failures = results.filter((result) => !result.ok);
    if (failures.length > 0) {
      for (const failure of failures) {
        console.error(`${failure.slide}: ${failure.errors.join('; ')}`);
      }
      process.exit(1);
    }
    console.log(`Verified ${results.length} HTML slides with Playwright.`);
  } catch (error) {
    console.error(error.message);
    process.exit(1);
  }
}

main();
