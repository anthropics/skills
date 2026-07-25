#!/usr/bin/env node
// full-page-screenshot.mjs — Standalone full-page screenshot tool via Chrome CDP
//
// Modes:
//   --check                          Check environment (Node.js 22+, Chrome debugging port)
//   --list                           List open browser tabs as JSON
//   --url <URL> [output] [options]   Screenshot a URL (create tab → wait → capture → close)
//   <targetId>  [output] [options]   Screenshot an existing tab by target ID
//
// Options:
//   --width N    Viewport width in CSS pixels (default: 1200)
//   --dpr N      Device pixel ratio (default: 1)
//   --wait N     Page load timeout in ms, --url mode only (default: 15000)
//
// Requires: Node.js 22+, Chrome with remote debugging enabled

import fs from 'fs';
import net from 'net';
import path from 'path';
import { platform, homedir } from 'os';

// ─── Argument parsing ───────────────────────────────────────────────────────

const args = process.argv.slice(2);
const flags = {};
const positional = [];
const boolFlags = new Set(['check', 'list']);

for (let i = 0; i < args.length; i++) {
  if (args[i].startsWith('--')) {
    const key = args[i].slice(2);
    if (boolFlags.has(key)) {
      flags[key] = true;
    } else if (i + 1 < args.length) {
      flags[key] = args[++i];
    }
  } else {
    positional.push(args[i]);
  }
}

const vpWidth = parseInt(flags.width || '1200', 10);
const dpr = parseInt(flags.dpr || '1', 10);
const loadTimeout = parseInt(flags.wait || '15000', 10);
const customCss = flags.css || '';

// ─── Chrome discovery ───────────────────────────────────────────────────────

function getDevToolsActivePortPaths() {
  const home = homedir();
  if (platform() === 'darwin') {
    return [
      path.join(home, 'Library/Application Support/Google/Chrome/DevToolsActivePort'),
      path.join(home, 'Library/Application Support/Google/Chrome Canary/DevToolsActivePort'),
      path.join(home, 'Library/Application Support/Chromium/DevToolsActivePort'),
    ];
  } else if (platform() === 'linux') {
    return [
      path.join(home, '.config/google-chrome/DevToolsActivePort'),
      path.join(home, '.config/chromium/DevToolsActivePort'),
    ];
  } else if (platform() === 'win32') {
    const local = process.env.LOCALAPPDATA || '';
    return [
      path.join(local, 'Google/Chrome/User Data/DevToolsActivePort'),
      path.join(local, 'Chromium/User Data/DevToolsActivePort'),
    ];
  }
  return [];
}

function checkPort(port) {
  return new Promise((resolve) => {
    const socket = net.createConnection(port, '127.0.0.1');
    const timer = setTimeout(() => { socket.destroy(); resolve(false); }, 2000);
    socket.once('connect', () => { clearTimeout(timer); socket.destroy(); resolve(true); });
    socket.once('error', () => { clearTimeout(timer); resolve(false); });
  });
}

async function discoverChrome() {
  // 1. Try DevToolsActivePort file
  for (const p of getDevToolsActivePortPaths()) {
    try {
      const lines = fs.readFileSync(p, 'utf-8').trim().split('\n');
      const port = parseInt(lines[0], 10);
      if (port > 0 && port < 65536) {
        const ok = await checkPort(port);
        if (ok) {
          const wsPath = lines[1] || '/devtools/browser';
          return { port, wsUrl: `ws://127.0.0.1:${port}${wsPath}` };
        }
      }
    } catch { /* try next */ }
  }

  // 2. Fallback: probe common debugging ports
  for (const port of [9222, 9229, 9333]) {
    const ok = await checkPort(port);
    if (ok) {
      return { port, wsUrl: `ws://127.0.0.1:${port}/devtools/browser` };
    }
  }

  return null;
}

// ─── CDP WebSocket helpers ──────────────────────────────────────────────────

let msgId = 0;
const pending = new Map();
let ws;

function send(method, params = {}, sessionId = null, timeoutMs = 60000) {
  return new Promise((resolve, reject) => {
    const id = ++msgId;
    const msg = { id, method, params };
    if (sessionId) msg.sessionId = sessionId;
    pending.set(id, resolve);
    ws.send(JSON.stringify(msg));
    setTimeout(() => {
      if (pending.has(id)) {
        pending.delete(id);
        reject(new Error(`CDP timeout (${timeoutMs}ms): ${method}`));
      }
    }, timeoutMs);
  });
}

const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

async function connectChrome() {
  const chrome = await discoverChrome();
  if (!chrome) {
    console.error('Cannot find Chrome debugging port.');
    console.error('Open chrome://inspect/#remote-debugging and enable "Allow remote debugging for this browser instance".');
    process.exit(1);
  }

  ws = new WebSocket(chrome.wsUrl);

  ws.onmessage = (evt) => {
    const msg = JSON.parse(typeof evt.data === 'string' ? evt.data : evt.data.toString());
    if (msg.id !== undefined && pending.has(msg.id)) {
      pending.get(msg.id)(msg);
      pending.delete(msg.id);
    }
  };

  await new Promise((resolve, reject) => {
    const timer = setTimeout(() => {
      ws.close();
      reject(new Error('WebSocket connection timeout (10s) — browser WebSocket may be held by proxy'));
    }, 10000);
    ws.onopen = () => { clearTimeout(timer); resolve(); };
    ws.onerror = () => { clearTimeout(timer); reject(new Error('WebSocket connection to Chrome failed')); };
  });

  return chrome;
}

function closeWs() {
  try { ws?.close(); } catch {}
}

// ─── Wait for page load ─────────────────────────────────────────────────────

async function waitForLoad(sid, timeoutMs) {
  const start = Date.now();

  // Phase 1: wait for readyState=complete
  while (Date.now() - start < timeoutMs) {
    try {
      const resp = await send('Runtime.evaluate', {
        expression: 'document.readyState',
        returnByValue: true,
      }, sid, 5000);
      if (resp.result?.result?.value === 'complete') break;
    } catch { /* retry */ }
    await sleep(500);
  }

  // Phase 2: wait for DOM to stabilize (SPA content rendering)
  // SPAs load shell HTML instantly, then fetch data and render dynamically.
  // We detect stability by checking if DOM element count stops changing.
  const stabilityTimeout = Math.min(15000, Math.max(0, timeoutMs - (Date.now() - start)));
  if (stabilityTimeout > 0) {
    console.log('Waiting for DOM to stabilize...');
    let lastCount = 0;
    let stableRounds = 0;
    const stableThreshold = 3; // need 3 consecutive stable checks (1.5s)
    const checkStart = Date.now();
    while (Date.now() - checkStart < stabilityTimeout) {
      try {
        const resp = await send('Runtime.evaluate', {
          expression: 'document.querySelectorAll("*").length',
          returnByValue: true,
        }, sid, 5000);
        const count = resp.result?.result?.value || 0;
        if (count === lastCount && count > 0) {
          stableRounds++;
          if (stableRounds >= stableThreshold) {
            console.log(`DOM stable at ${count} elements`);
            return true;
          }
        } else {
          stableRounds = 0;
          lastCount = count;
        }
      } catch { /* retry */ }
      await sleep(500);
    }
    console.log(`DOM stability timeout (last count: ${lastCount}), proceeding`);
  }

  return true;
}

// ─── Core screenshot logic ──────────────────────────────────────────────────

async function captureFullPage({ sid, outputFile, width, devicePixelRatio, css }) {
  // Set target width with a short viewport to measure content height
  await send('Emulation.setDeviceMetricsOverride', {
    width, height: 800, deviceScaleFactor: devicePixelRatio, mobile: false,
  }, sid);
  await sleep(2000);

  // Inject custom CSS if provided (e.g. hide sidebars, adjust layout)
  if (css) {
    await send('Runtime.evaluate', {
      expression: `(() => {
        const s = document.createElement('style');
        s.textContent = ${JSON.stringify(css)};
        document.head.appendChild(s);
      })()`,
      returnByValue: true,
    }, sid);
    await sleep(500);
  }

  // Expand internal scroll containers so their full content is visible in the screenshot.
  // Many SPAs use overflow-y:auto/scroll on inner divs instead of document-level scrolling.
  // We detect these, scroll through them to trigger lazy-loading, then remove overflow constraints.
  const expandResult = await send('Runtime.evaluate', {
    expression: `(async () => {
      const containers = [];
      for (const el of document.querySelectorAll('*')) {
        const style = getComputedStyle(el);
        const overflowY = style.overflowY;
        if ((overflowY === 'auto' || overflowY === 'scroll') &&
            el.scrollHeight > el.clientHeight + 50 &&
            el.clientHeight >= 100) {
          containers.push(el);
        }
      }
      if (containers.length === 0) return { found: 0 };

      // Scroll each container to trigger lazy loading inside it
      for (const el of containers) {
        const step = 800;
        for (let y = 0; y < el.scrollHeight; y += step) {
          el.scrollTop = y;
          await new Promise(r => setTimeout(r, 150));
        }
        el.scrollTop = 0;
      }

      // Expand containers: remove overflow and fixed-height constraints
      // Use !important to override CSS class-based constraints (e.g. Tailwind h-[calc(...)])
      function expandEl(el) {
        el.style.setProperty('overflow', 'visible', 'important');
        el.style.setProperty('overflow-y', 'visible', 'important');
        el.style.setProperty('max-height', 'none', 'important');
        // Override computed height if it constrains content
        const computed = getComputedStyle(el);
        const computedH = parseFloat(computed.height);
        if (computedH < el.scrollHeight - 10) {
          el.style.setProperty('height', 'auto', 'important');
        }
      }

      let expanded = 0;
      for (const el of containers) {
        if (el.scrollHeight > el.clientHeight + 50) {
          expandEl(el);
          // Walk up the parent chain and expand anything that clips
          let parent = el.parentElement;
          for (let i = 0; i < 10 && parent && parent !== document.body; i++) {
            const ps = getComputedStyle(parent);
            if (ps.overflow !== 'visible' || ps.overflowY !== 'visible' ||
                parseFloat(ps.height) < parent.scrollHeight - 10) {
              expandEl(parent);
            }
            parent = parent.parentElement;
          }
          expanded++;
        }
      }
      return { found: containers.length, expanded };
    })()`,
    returnByValue: true, awaitPromise: true,
  }, sid, 60000);

  const expInfo = expandResult.result?.result?.value;
  if (expInfo && expInfo.expanded > 0) {
    console.log(`Expanded ${expInfo.expanded} scroll container(s)`);
    await sleep(1000);
  }

  // Measure content height after expansion
  const m1 = await send('Page.getLayoutMetrics', {}, sid);
  const contentH = Math.ceil(m1.result.cssContentSize.height);
  console.log(`Content: ${width}x${contentH} @ ${devicePixelRatio}x`);

  // Set viewport height — cap at 8000px to avoid Chrome memory issues on very tall pages.
  // captureBeyondViewport: true will still capture the full page content.
  const vpHeight = Math.min(contentH, 8000);
  await send('Emulation.setDeviceMetricsOverride', {
    width, height: vpHeight, deviceScaleFactor: devicePixelRatio, mobile: false,
  }, sid);
  await sleep(2000);

  // Scroll through page slowly to trigger window-level lazy loading
  // Non-fatal: if this times out (common on very tall expanded pages), we skip it
  try {
    await send('Runtime.evaluate', {
      expression: `(async()=>{
        const h = document.documentElement.scrollHeight;
        const step = 800;
        const maxSteps = Math.ceil(h / step);
        const deadline = Date.now() + 15000;
        for(let i=0; i<maxSteps; i++){
          if(Date.now()>deadline) break;
          window.scrollTo(0, i * step);
          await new Promise(r=>setTimeout(r, 200));
        }
        window.scrollTo(0, document.documentElement.scrollHeight);
        await new Promise(r=>setTimeout(r, 300));
        window.scrollTo(0, 0);
      })()`,
      returnByValue: true, awaitPromise: true,
    }, sid, 20000);
  } catch (e) {
    console.warn(`Scroll lazy-load skipped (${e.message})`);
  }

  // Wait for all images to finish loading (non-fatal timeout)
  try {
    const imgResult = await send('Runtime.evaluate', {
      expression: `(async()=>{
        const deadline = Date.now() + 10000;
        while (Date.now() < deadline) {
          const imgs = Array.from(document.querySelectorAll('img'));
          const pending = imgs.filter(i => !i.complete && i.src && !i.src.startsWith('data:'));
          if (pending.length === 0) return { loaded: imgs.length, waited: false };
          await new Promise(r => setTimeout(r, 500));
        }
        const imgs = Array.from(document.querySelectorAll('img'));
        const still = imgs.filter(i => !i.complete && i.src && !i.src.startsWith('data:'));
        return { loaded: imgs.length - still.length, pending: still.length, timeout: true };
      })()`,
      returnByValue: true, awaitPromise: true,
    }, sid, 15000);

    const imgInfo = imgResult.result?.result?.value;
    if (imgInfo) {
      if (imgInfo.timeout) {
        console.warn(`Warning: ${imgInfo.pending} image(s) still loading after 10s timeout`);
      } else {
        console.log(`Images loaded: ${imgInfo.loaded}`);
      }
    }
  } catch (e) {
    console.warn(`Image wait skipped (${e.message})`);
  }

  // Final measure (content may have grown after lazy-load)
  const m2 = await send('Page.getLayoutMetrics', {}, sid);
  const finalH = Math.ceil(m2.result.cssContentSize.height);
  if (finalH !== contentH) {
    console.log(`Height adjusted: ${contentH} → ${finalH}`);
    const newVpH = Math.min(finalH, 8000);
    await send('Emulation.setDeviceMetricsOverride', {
      width, height: newVpH, deviceScaleFactor: devicePixelRatio, mobile: false,
    }, sid);
    await sleep(1000);
  }

  // Capture — for very tall pages (>16000px), use tiled capture to avoid Chrome timeout
  const TILE_THRESHOLD = 16000;
  if (finalH <= TILE_THRESHOLD) {
    // Single capture
    console.log(`Capturing ${width}x${finalH}...`);
    const shot = await send('Page.captureScreenshot', {
      format: 'png',
      captureBeyondViewport: true,
      clip: { x: 0, y: 0, width, height: finalH, scale: 1 },
    }, sid, 120000);

    if (shot.error) {
      throw new Error(`Screenshot failed: ${JSON.stringify(shot.error)}`);
    }

    const buf = Buffer.from(shot.result.data, 'base64');
    fs.writeFileSync(outputFile, buf);
    const mb = (buf.length / 1024 / 1024).toFixed(2);
    console.log(`Saved: ${outputFile} (${width * devicePixelRatio}x${finalH * devicePixelRatio}px, ${mb} MB)`);
  } else {
    // Tiled capture for very tall pages
    const tileH = 8000;
    const tiles = [];
    for (let y = 0; y < finalH; y += tileH) {
      const h = Math.min(tileH, finalH - y);
      console.log(`Capturing tile ${tiles.length + 1}: y=${y}, h=${h}...`);
      const shot = await send('Page.captureScreenshot', {
        format: 'png',
        captureBeyondViewport: true,
        clip: { x: 0, y, width, height: h, scale: 1 },
      }, sid, 120000);
      if (shot.error) {
        throw new Error(`Tile screenshot failed: ${JSON.stringify(shot.error)}`);
      }
      const tilePath = outputFile.replace(/\.png$/, `_tile${tiles.length}.png`);
      fs.writeFileSync(tilePath, Buffer.from(shot.result.data, 'base64'));
      tiles.push({ path: tilePath, y, h });
    }

    // Stitch tiles using Python PIL (available on macOS)
    console.log(`Stitching ${tiles.length} tiles (${width}x${finalH})...`);
    const { execSync } = await import('child_process');
    const stitchScriptPath = outputFile.replace(/\.png$/, '_stitch.py');
    const stitchScript = [
      'from PIL import Image',
      `tiles = [${tiles.map(t => `("${t.path}", ${t.y})`).join(',')}]`,
      `out = Image.new("RGB", (${width * devicePixelRatio}, ${finalH * devicePixelRatio}))`,
      'for path, y in tiles:',
      '    tile = Image.open(path)',
      `    out.paste(tile, (0, y * ${devicePixelRatio}))`,
      '    tile.close()',
      `out.save("${outputFile}")`,
      'print(f"Stitched: {out.size[0]}x{out.size[1]}")',
    ].join('\n');
    fs.writeFileSync(stitchScriptPath, stitchScript);
    try {
      const result = execSync(`python3 "${stitchScriptPath}"`, { encoding: 'utf-8', timeout: 60000 });
      console.log(result.trim());
    } catch (e) {
      // Fallback: if Python/PIL not available, keep tiles as separate files
      console.warn('PIL not available for stitching. Tiles saved as separate files:');
      for (const t of tiles) console.log(`  ${t.path}`);
      // Copy first tile as the output for basic functionality
      fs.copyFileSync(tiles[0].path, outputFile);
    }
    try { fs.unlinkSync(stitchScriptPath); } catch {}

    // Clean up tile files
    for (const t of tiles) {
      try { fs.unlinkSync(t.path); } catch {}
    }

    const stat = fs.statSync(outputFile);
    const mb = (stat.size / 1024 / 1024).toFixed(2);
    console.log(`Saved: ${outputFile} (${width * devicePixelRatio}x${finalH * devicePixelRatio}px, ${mb} MB)`);
  }
}

// ─── Mode: --check ──────────────────────────────────────────────────────────

async function modeCheck() {
  // Check Node.js version
  const nodeVer = process.versions.node;
  const major = parseInt(nodeVer.split('.')[0], 10);
  if (major >= 22) {
    console.log(`node: ok (v${nodeVer})`);
  } else {
    console.log(`node: FAIL (v${nodeVer}, need 22+)`);
    process.exit(1);
  }

  // Check Chrome debugging port (TCP only, no WebSocket to avoid auth popup)
  const chrome = await discoverChrome();
  if (chrome) {
    console.log(`chrome: ok (port ${chrome.port})`);
  } else {
    console.log('chrome: FAIL');
    console.error('Open chrome://inspect/#remote-debugging and enable "Allow remote debugging for this browser instance".');
    process.exit(1);
  }
}

// ─── Mode: --list ───────────────────────────────────────────────────────────

async function modeList() {
  // Try direct CDP first, fall back to proxy API
  try {
    await connectChrome();
    try {
      const resp = await send('Target.getTargets');
      const pages = resp.result.targetInfos
        .filter((t) => t.type === 'page')
        .map(({ targetId, title, url }) => ({ targetId, title, url }));
      console.log(JSON.stringify(pages, null, 2));
    } finally {
      closeWs();
    }
  } catch {
    // Direct connection failed — try proxy
    const proxyUp = await isProxyRunning();
    if (!proxyUp) {
      console.error('Cannot connect to Chrome and no proxy running.');
      process.exit(1);
    }
    const resp = await fetch(`${PROXY_URL}/targets`, { signal: AbortSignal.timeout(10000) });
    const targets = await resp.json();
    const pages = targets
      .filter((t) => t.type === 'page')
      .map(({ targetId, title, url }) => ({ targetId, title, url }));
    console.log(JSON.stringify(pages, null, 2));
  }
}

// ─── Mode: --url ────────────────────────────────────────────────────────────

async function modeUrl() {
  const url = flags.url;
  const outputFile = positional[0] || '/tmp/screenshot.png';

  // Try direct CDP first
  let connected = false;
  try {
    await connectChrome();
    connected = true;
  } catch {
    // Browser WebSocket held by proxy
  }

  if (connected) {
    let createdTargetId = null;
    let sid = null;

    try {
      // Create background tab
      const create = await send('Target.createTarget', { url, background: true });
      if (create.error) {
        throw new Error(`Failed to create tab: ${JSON.stringify(create.error)}`);
      }
      createdTargetId = create.result.targetId;
      console.log(`Tab created: ${createdTargetId.slice(0, 16)}...`);

      // Attach
      const attach = await send('Target.attachToTarget', { targetId: createdTargetId, flatten: true });
      if (attach.error) {
        throw new Error(`Attach failed: ${JSON.stringify(attach.error)}`);
      }
      sid = attach.result.sessionId;

      // Wait for page load
      await send('Page.enable', {}, sid);
      await waitForLoad(sid, loadTimeout);

      // Screenshot
      await captureFullPage({ sid, outputFile, width: vpWidth, devicePixelRatio: dpr, css: customCss });

    } finally {
      if (sid) {
        try { await send('Emulation.clearDeviceMetricsOverride', {}, sid); } catch {}
        try { await send('Target.detachFromTarget', { sessionId: sid }); } catch {}
      }
      if (createdTargetId) {
        try { await send('Target.closeTarget', { targetId: createdTargetId }); } catch {}
      }
      closeWs();
    }
    return;
  }

  // Fallback: use proxy to create tab and screenshot
  const proxyUp = await isProxyRunning();
  if (!proxyUp) {
    console.error('Cannot connect to Chrome and no proxy running.');
    process.exit(1);
  }

  console.log('Using proxy to create tab...');
  const newResp = await fetch(`${PROXY_URL}/new?url=${encodeURIComponent(url)}`, {
    signal: AbortSignal.timeout(loadTimeout + 5000),
  });
  const newTab = await newResp.json();
  const targetId = newTab.targetId;
  console.log(`Tab created via proxy: ${targetId.slice(0, 16)}...`);

  // Wait for DOM to stabilize (SPA rendering)
  console.log('Waiting for DOM to stabilize...');
  let lastCount = 0, stableRounds = 0;
  const stabilityDeadline = Date.now() + 15000;
  while (Date.now() < stabilityDeadline) {
    const count = await proxyEval(targetId, 'document.querySelectorAll("*").length');
    if (count === lastCount && count > 0) {
      stableRounds++;
      if (stableRounds >= 3) { console.log(`DOM stable at ${count} elements`); break; }
    } else { stableRounds = 0; lastCount = count; }
    await sleep(500);
  }

  try {
    await captureViaProxy(targetId, outputFile, vpWidth, dpr);
  } finally {
    // Close the tab we created
    try { await fetch(`${PROXY_URL}/close?target=${targetId}`, { signal: AbortSignal.timeout(5000) }); } catch {}
  }
}

// ─── CDP Proxy helpers (used when proxy is running) ─────────────────────────

const PROXY_URL = 'http://localhost:3456';

async function isProxyRunning() {
  try {
    const resp = await fetch(`${PROXY_URL}/health`, { signal: AbortSignal.timeout(1000) });
    const data = await resp.json();
    return data.status === 'ok';
  } catch { return false; }
}

async function proxyEval(targetId, expr) {
  const resp = await fetch(`${PROXY_URL}/eval?target=${targetId}`, {
    method: 'POST', body: expr, signal: AbortSignal.timeout(60000),
  });
  return (await resp.json()).value;
}

async function proxyScreenshot(targetId, filePath) {
  const resp = await fetch(`${PROXY_URL}/screenshot?target=${targetId}&file=${encodeURIComponent(filePath)}`, {
    signal: AbortSignal.timeout(30000),
  });
  return await resp.json();
}

async function proxyScroll(targetId, y) {
  await fetch(`${PROXY_URL}/scroll?target=${targetId}&y=${y}`, {
    signal: AbortSignal.timeout(10000),
  });
}

// Full-page screenshot using proxy API (tiled viewport captures)
async function captureViaProxy(targetId, outputFile, width, devicePixelRatio) {
  console.log('Using proxy API for full-page capture...');

  // Detect scroll containers WITHOUT expanding them (expansion causes issues with proxy)
  const containerInfo = await proxyEval(targetId, `(() => {
    const containers = [];
    for (const el of document.querySelectorAll('*')) {
      const style = getComputedStyle(el);
      const overflowY = style.overflowY;
      if ((overflowY === 'auto' || overflowY === 'scroll') &&
          el.scrollHeight > el.clientHeight + 50 &&
          el.clientHeight >= 100) {
        // Find a unique selector for this element
        let selector = el.tagName.toLowerCase();
        if (el.id) selector = '#' + el.id;
        else if (el.className) {
          const cls = el.className.trim().split(/\\s+/).filter(c => !c.includes('[')).slice(0, 3).join('.');
          if (cls) selector = el.tagName.toLowerCase() + '.' + cls;
        }
        containers.push({
          selector,
          scrollHeight: el.scrollHeight,
          clientHeight: el.clientHeight,
          index: containers.length
        });
      }
    }
    return containers;
  })()`);

  const pageInfo = await proxyEval(targetId, `({
    scrollHeight: Math.max(document.body.scrollHeight, document.documentElement.scrollHeight),
    viewportHeight: window.innerHeight,
    viewportWidth: window.innerWidth
  })`);

  const vpH = pageInfo.viewportHeight;
  console.log(`Page viewport: ${pageInfo.viewportWidth}x${vpH}`);

  // Determine capture strategy
  const mainContainer = containerInfo && containerInfo.length > 0
    ? containerInfo.reduce((a, b) => a.scrollHeight > b.scrollHeight ? a : b)
    : null;

  if (mainContainer && mainContainer.scrollHeight > vpH) {
    // SPA with internal scroll container — scroll the container, capture tiles
    console.log(`Scroll container: ${mainContainer.selector} (${mainContainer.scrollHeight}px content in ${mainContainer.clientHeight}px view)`);

    // First, scroll through container to trigger lazy loading
    await proxyEval(targetId, `(async () => {
      const containers = [];
      for (const el of document.querySelectorAll('*')) {
        const style = getComputedStyle(el);
        if ((style.overflowY === 'auto' || style.overflowY === 'scroll') &&
            el.scrollHeight > el.clientHeight + 50 && el.clientHeight >= 100) {
          containers.push(el);
        }
      }
      const el = containers[${mainContainer.index}];
      if (!el) return;
      const step = 800;
      for (let y = 0; y < el.scrollHeight; y += step) {
        el.scrollTop = y;
        await new Promise(r => setTimeout(r, 150));
      }
      el.scrollTop = 0;
    })()`);

    // Wait for images
    await proxyEval(targetId, `(async () => {
      const deadline = Date.now() + 8000;
      while (Date.now() < deadline) {
        const imgs = Array.from(document.querySelectorAll('img'));
        const pending = imgs.filter(i => !i.complete && i.src && !i.src.startsWith('data:'));
        if (pending.length === 0) return;
        await new Promise(r => setTimeout(r, 500));
      }
    })()`);

    // Capture tiles by scrolling the container
    const containerH = mainContainer.clientHeight;
    const totalScrollH = mainContainer.scrollHeight;
    const overlap = 20;
    const stepH = containerH - overlap;
    const tiles = [];

    for (let scrollY = 0; scrollY < totalScrollH; scrollY += stepH) {
      await proxyEval(targetId, `(() => {
        const containers = [];
        for (const el of document.querySelectorAll('*')) {
          const style = getComputedStyle(el);
          if ((style.overflowY === 'auto' || style.overflowY === 'scroll') &&
              el.scrollHeight > el.clientHeight + 50 && el.clientHeight >= 100) {
            containers.push(el);
          }
        }
        const el = containers[${mainContainer.index}];
        if (el) el.scrollTop = ${scrollY};
      })()`);
      await sleep(300);

      const tilePath = outputFile.replace(/\.png$/, `_tile${tiles.length}.png`);
      await proxyScreenshot(targetId, tilePath);
      tiles.push({ path: tilePath, scrollY });
      console.log(`Tile ${tiles.length}: scrollY=${scrollY}`);
    }

    // Reset scroll position
    await proxyEval(targetId, `(() => {
      const containers = [];
      for (const el of document.querySelectorAll('*')) {
        const style = getComputedStyle(el);
        if ((style.overflowY === 'auto' || style.overflowY === 'scroll') &&
            el.scrollHeight > el.clientHeight + 50 && el.clientHeight >= 100) {
          containers.push(el);
        }
      }
      const el = containers[${mainContainer.index}];
      if (el) el.scrollTop = 0;
    })()`);

    if (tiles.length === 1) {
      fs.renameSync(tiles[0].path, outputFile);
    } else {
      // Stitch tiles
      console.log(`Stitching ${tiles.length} tiles...`);
      const { execSync } = await import('child_process');

      const sipsOut = execSync(`sips -g pixelWidth -g pixelHeight "${tiles[0].path}"`, { encoding: 'utf-8' });
      const pxW = parseInt(sipsOut.match(/pixelWidth:\s*(\d+)/)?.[1] || '0');
      const pxH = parseInt(sipsOut.match(/pixelHeight:\s*(\d+)/)?.[1] || '0');
      const dpr = pxH / vpH;

      // Calculate the pixel offset of the container within the viewport
      const containerOffset = await proxyEval(targetId, `(() => {
        const containers = [];
        for (const el of document.querySelectorAll('*')) {
          const style = getComputedStyle(el);
          if ((style.overflowY === 'auto' || style.overflowY === 'scroll') &&
              el.scrollHeight > el.clientHeight + 50 && el.clientHeight >= 100) {
            containers.push(el);
          }
        }
        const el = containers[${mainContainer.index}];
        if (!el) return 0;
        const rect = el.getBoundingClientRect();
        return rect.top;
      })()`);

      const pxContainerTop = Math.round((containerOffset || 0) * dpr);
      const pxContainerH = Math.round(containerH * dpr);
      const pxStepH = Math.round(stepH * dpr);
      const pxTotalContentH = Math.round(totalScrollH * dpr);

      // Stitch: header (top of first tile) + container content strips from each tile + footer (bottom of last tile)
      const stitchScriptPath = outputFile.replace(/\.png$/, '_stitch.py');
      const stitchLines = [
        'from PIL import Image',
        `tiles = [${tiles.map(t => `"${t.path}"`).join(',')}]`,
        'imgs = [Image.open(p) for p in tiles]',
        'tile_w, tile_h = imgs[0].size',
        `container_top = ${pxContainerTop}`,
        `container_h = ${pxContainerH}`,
        `step_h = ${pxStepH}`,
        `total_content_h = ${pxTotalContentH}`,
        'header_h = container_top',
        'footer_h = tile_h - container_top - container_h',
        'out_h = header_h + total_content_h + footer_h',
        'out = Image.new("RGB", (tile_w, out_h))',
        'if header_h > 0:',
        '    header = imgs[0].crop((0, 0, tile_w, header_h))',
        '    out.paste(header, (0, 0))',
        'for i, img in enumerate(imgs):',
        '    content_strip = img.crop((0, container_top, tile_w, container_top + container_h))',
        '    y = header_h + i * step_h',
        '    paste_h = min(container_h, out_h - footer_h - y)',
        '    if paste_h < container_h:',
        '        content_strip = content_strip.crop((0, 0, tile_w, paste_h))',
        '    if paste_h > 0:',
        '        out.paste(content_strip, (0, y))',
        'if footer_h > 0:',
        '    footer = imgs[-1].crop((0, tile_h - footer_h, tile_w, tile_h))',
        '    out.paste(footer, (0, out_h - footer_h))',
        'for img in imgs:',
        '    img.close()',
        `out.save("${outputFile}")`,
        'print(f"Stitched: {out.size[0]}x{out.size[1]}")',
      ];
      fs.writeFileSync(stitchScriptPath, stitchLines.join('\n'));
      try {
        const result = execSync(`python3 "${stitchScriptPath}"`, { encoding: 'utf-8', timeout: 60000 });
        console.log(result.trim());
      } catch (e) {
        console.warn('Stitching failed:', e.message?.slice(0, 200));
        fs.copyFileSync(tiles[0].path, outputFile);
      }

      // Clean up tiles and stitch script
      try { fs.unlinkSync(stitchScriptPath); } catch {}
      for (const t of tiles) { try { fs.unlinkSync(t.path); } catch {} }
    }

  } else {
    // Normal page or small page — single viewport screenshot
    // Scroll through to trigger lazy loading first
    await proxyEval(targetId, `(async () => {
      const h = document.documentElement.scrollHeight;
      const step = 800;
      for (let y = 0; y < h; y += step) {
        window.scrollTo(0, y);
        await new Promise(r => setTimeout(r, 200));
      }
      window.scrollTo(0, 0);
    })()`);

    await proxyScreenshot(targetId, outputFile);
  }

  const stat = fs.statSync(outputFile);
  const mb = (stat.size / 1024 / 1024).toFixed(2);
  console.log(`Saved: ${outputFile} (${mb} MB)`);
}

// ─── Mode: targetId (existing tab) ─────────────────────────────────────────

async function modeTarget() {
  const targetId = positional[0];
  const outputFile = positional[1] || '/tmp/screenshot.png';

  if (!targetId) {
    console.error('Usage:');
    console.error('  node full-page-screenshot.mjs --check');
    console.error('  node full-page-screenshot.mjs --list');
    console.error('  node full-page-screenshot.mjs --url <URL> [output] [--width N] [--dpr N]');
    console.error('  node full-page-screenshot.mjs <targetId> [output] [--width N] [--dpr N]');
    process.exit(1);
  }

  // Try direct CDP first. If browser WebSocket is held by proxy, fall back to proxy API.
  let connected = false;
  try {
    await connectChrome();
    connected = true;
  } catch {
    // Browser WebSocket likely held by proxy
  }

  if (connected) {
    let sid = null;
    try {
      const attach = await send('Target.attachToTarget', { targetId, flatten: true });
      if (attach.error) {
        console.error(`Attach failed: ${JSON.stringify(attach.error)}`);
        console.error('Run with --list to see available targets.');
        process.exit(1);
      }
      sid = attach.result.sessionId;

      // Test with Page.enable — if times out, proxy may be interfering
      try {
        await send('Page.enable', {}, sid, 10000);
      } catch {
        console.warn('Direct session timed out, falling back to proxy...');
        try { await send('Target.detachFromTarget', { sessionId: sid }); } catch {}
        sid = null;
        closeWs();
        connected = false;
      }

      if (sid) {
        await captureFullPage({ sid, outputFile, width: vpWidth, devicePixelRatio: dpr, css: customCss });
      }
    } finally {
      if (sid) {
        try { await send('Emulation.clearDeviceMetricsOverride', {}, sid); } catch {}
        try { await send('Target.detachFromTarget', { sessionId: sid }); } catch {}
      }
      if (connected) closeWs();
    }
  }

  // Fallback to proxy API
  if (!connected) {
    const proxyUp = await isProxyRunning();
    if (!proxyUp) {
      console.error('Cannot connect to Chrome (browser WebSocket unavailable) and no proxy running.');
      process.exit(1);
    }
    await captureViaProxy(targetId, outputFile, vpWidth, dpr);
  }
}

// ─── Dispatch ───────────────────────────────────────────────────────────────

async function main() {
  if (flags.check) return modeCheck();
  if (flags.list) return modeList();
  if (flags.url) return modeUrl();
  return modeTarget();
}

main().catch((e) => {
  console.error('Error:', e.message || e);
  closeWs();
  process.exit(1);
});
