#!/usr/bin/env node
/**
 * HTML to PDF (Hi-Res Raster)
 *
 * Screenshots each page element at high DPR and embeds PNGs full-bleed
 * into a fresh PDF. Output is pixel-identical to what Chrome renders,
 * independent of the viewer's font-rendering.
 */

const fs = require('fs');
const path = require('path');
const os = require('os');

const puppeteer = require('puppeteer');

// Page formats in mm (width x height, portrait)
const FORMATS = {
  A3: [297, 420],
  A4: [210, 297],
  A5: [148, 210],
  Letter: [215.9, 279.4],
  Legal: [215.9, 355.6],
};

// Parse CLI args
function parseArgs(argv) {
  const args = {
    input: null,
    output: null,
    dpr: 3,
    format: 'A4',
    landscape: false,
    selector: '.page',
    wait: 2500,
    activateClass: null,
    activateDelay: 400,
  };
  const positional = [];
  for (const a of argv.slice(2)) {
    if (a.startsWith('--dpr=')) args.dpr = parseFloat(a.slice(6));
    else if (a.startsWith('--format=')) args.format = a.slice(9);
    else if (a === '--landscape') args.landscape = true;
    else if (a.startsWith('--selector=')) args.selector = a.slice(11);
    else if (a.startsWith('--wait=')) args.wait = parseInt(a.slice(7), 10);
    else if (a.startsWith('--activate-class=')) args.activateClass = a.slice(17);
    else if (a.startsWith('--activate-delay=')) args.activateDelay = parseInt(a.slice(17), 10);
    else if (a.startsWith('--')) {
      console.error(`Unknown flag: ${a}`);
      process.exit(2);
    } else positional.push(a);
  }
  args.input = positional[0];
  args.output = positional[1];
  return args;
}

function usage() {
  console.error(
    'Usage: convert.js <input.html|URL> <output.pdf> ' +
      '[--dpr=3] [--format=A4] [--landscape] [--selector=".page"] [--wait=2500] ' +
      '[--activate-class=<name>] [--activate-delay=400]',
  );
  process.exit(1);
}

// Resolve input to a URL that puppeteer can load
function resolveInput(input) {
  if (/^https?:\/\//i.test(input) || /^file:\/\//i.test(input)) return input;
  const abs = path.resolve(input);
  if (!fs.existsSync(abs)) {
    console.error(`Input not found: ${abs}`);
    process.exit(1);
  }
  // file:// URL — on Windows, path.resolve returns C:\foo\bar; convert to /C:/foo/bar
  const normalized = abs.replace(/\\/g, '/');
  return 'file:///' + normalized.replace(/^\/+/, '');
}

// Convert mm to CSS pixels at 96dpi
const mmToPx = (mm) => Math.round((mm * 96) / 25.4);

async function run() {
  const args = parseArgs(process.argv);
  if (!args.input || !args.output) usage();

  const fmt = FORMATS[args.format];
  if (!fmt) {
    console.error(`Unknown format: ${args.format}. Supported: ${Object.keys(FORMATS).join(', ')}`);
    process.exit(2);
  }
  const [wMm, hMm] = args.landscape ? [fmt[1], fmt[0]] : fmt;
  const viewportW = mmToPx(wMm);
  const viewportH = mmToPx(hMm);

  const inputUrl = resolveInput(args.input);
  const outputPath = path.resolve(args.output);

  // --- Phase 1: render source HTML, screenshot each page element ---
  const browser = await puppeteer.launch({
    headless: 'new',
    args: [
      '--no-sandbox',
      '--disable-setuid-sandbox',
      '--font-render-hinting=none',
      '--disable-font-subpixel-positioning',
      '--force-color-profile=srgb',
    ],
  });
  const page = await browser.newPage();
  await page.setViewport({ width: viewportW, height: viewportH, deviceScaleFactor: args.dpr });
  await page.goto(inputUrl, { waitUntil: ['load', 'networkidle0'] });
  await page.evaluateHandle('document.fonts.ready');
  await new Promise((r) => setTimeout(r, args.wait));

  let handles = await page.$$(args.selector);
  let shots;
  if (handles.length === 0) {
    console.error(
      `Selector "${args.selector}" matched 0 elements — falling back to full-page screenshot.`,
    );
    const buf = await page.screenshot({ type: 'png', fullPage: true });
    shots = [buf.toString('base64')];
  } else if (args.activateClass) {
    // Slide-style decks: only the element carrying `activateClass` is visible
    // (typically via opacity + position:absolute). Cycle the class across
    // matches and screenshot the viewport each time.
    await page.addStyleTag({
      content: `*,*::before,*::after{transition:none!important;animation:none!important;}`,
    });
    shots = [];
    for (let i = 0; i < handles.length; i++) {
      await page.evaluate(
        (sel, cls, idx) => {
          document.querySelectorAll(sel).forEach((el, j) => {
            el.classList.toggle(cls, j === idx);
          });
        },
        args.selector,
        args.activateClass,
        i,
      );
      await new Promise((r) => setTimeout(r, args.activateDelay));
      const buf = await page.screenshot({ type: 'png', fullPage: false });
      shots.push(buf.toString('base64'));
    }
  } else {
    shots = [];
    for (const h of handles) {
      const buf = await h.screenshot({ type: 'png', omitBackground: false });
      shots.push(buf.toString('base64'));
    }
  }
  await browser.close();

  // --- Phase 2: compose HTML with full-bleed PNGs and print to final PDF ---
  const composed = `<!DOCTYPE html><html><head><meta charset="utf-8"><style>
    @page { size: ${wMm}mm ${hMm}mm; margin: 0; }
    *, *::before, *::after { margin: 0; padding: 0; box-sizing: border-box; }
    html, body { background: #fff; }
    .sheet {
      width: ${wMm}mm; height: ${hMm}mm;
      page-break-after: always;
      overflow: hidden;
      display: block;
    }
    .sheet:last-child { page-break-after: auto; }
    .sheet img {
      width: ${wMm}mm; height: ${hMm}mm;
      display: block;
      image-rendering: -webkit-optimize-contrast;
    }
  </style></head><body>${shots
    .map((b64) => `<div class="sheet"><img src="data:image/png;base64,${b64}"></div>`)
    .join('')}</body></html>`;

  const tmpHtml = path.join(os.tmpdir(), `html-to-pdf-hires-${process.pid}.html`);
  fs.writeFileSync(tmpHtml, composed);

  try {
    const b2 = await puppeteer.launch({
      headless: 'new',
      args: ['--no-sandbox', '--disable-setuid-sandbox'],
    });
    const p2 = await b2.newPage();
    const tmpUrl = 'file:///' + tmpHtml.replace(/\\/g, '/').replace(/^\/+/, '');
    await p2.goto(tmpUrl, { waitUntil: ['load', 'networkidle0'] });
    await p2.pdf({
      path: outputPath,
      width: `${wMm}mm`,
      height: `${hMm}mm`,
      printBackground: true,
      preferCSSPageSize: true,
      margin: { top: '0', right: '0', bottom: '0', left: '0' },
      scale: 1,
    });
    await b2.close();
  } finally {
    try {
      fs.unlinkSync(tmpHtml);
    } catch {}
  }

  const bytes = fs.statSync(outputPath).size;
  console.log(
    `Wrote ${outputPath} — ${shots.length} page(s), ${(bytes / 1024).toFixed(1)} KB ` +
      `@ dpr=${args.dpr}, ${wMm}×${hMm}mm`,
  );
}

run().catch((err) => {
  console.error(err.stack || err.message || err);
  process.exit(1);
});
