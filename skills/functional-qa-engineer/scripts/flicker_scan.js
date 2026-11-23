// Flicker / visual-instability scan for Playwright MCP: browser_run_code_unsafe with { filename: <copy of this file> }.
// DOM checks miss flicker (a node can stay mounted while it repaints blank, an image reloads, or a layer flashes).
// This compares real screenshots: it grabs a frame every ~STEP_MS of a region, diffs each frame against the previous
// one in an in-page canvas, and flags "blinks": A -> B -> back to ~A within a few frames (what a person sees as flicker).
// Steady change (new nodes appearing, a timer ticking) shows as one step, not a blink.
// Verified with a positive control (graph hidden 150 ms every 1.2 s): blinks detected. Limits: a full-viewport screenshot
// takes ~200-300 ms, so flashes shorter than the frame interval can fall between frames; set `region` to the element
// under test (smaller = faster frames, bigger signal). Always run a positive control on a new page before trusting a 0.
async (page) => {
  const CONFIG = {
    url: null,                  // set to navigate first, or null to use the current page
    region: null,               // {x,y,width,height} in CSS px, e.g. the graph canvas; null = full viewport
    frames: 120, STEP_MS: 100,  // ~12 s of samples; run it while the thing that flickers is happening (live run, polling)
    diffThreshold: 0.01,        // fraction of sampled pixels that changed to count as a "different" frame
    outDir: '.playwright-mcp/flicker/', saveBlinks: true,
  };
  Object.assign(CONFIG, page.context().__qaArgs || {});  // per-run overrides (used by the self-test)
  if (CONFIG.url) { await page.goto(CONFIG.url); await page.waitForTimeout(4000); }
  const shots = [];
  for (let i = 0; i < CONFIG.frames; i++) {
    const buf = await page.screenshot(CONFIG.region ? { clip: CONFIG.region, type: 'jpeg', quality: 60 } : { type: 'jpeg', quality: 60 });
    shots.push(buf.toString('base64'));
    await page.waitForTimeout(CONFIG.STEP_MS);
  }
  // diff consecutive frames in the page (no image libs needed)
  const diffs = await page.evaluate(async (b64s) => {
    const load = src => new Promise(r => { const im = new Image(); im.onload = () => r(im); im.src = 'data:image/jpeg;base64,' + src; });
    const W = 320; let prev = null; const out = []; const keep = [];
    for (const s of b64s) {
      const im = await load(s); const H = Math.round(im.height * W / im.width);
      const c = document.createElement('canvas'); c.width = W; c.height = H; const x = c.getContext('2d'); x.drawImage(im, 0, 0, W, H);
      const d = x.getImageData(0, 0, W, H).data; keep.push(d);
      if (prev) { let ch = 0, n = 0; for (let i = 0; i < d.length; i += 16) { n++; if (Math.abs(d[i] - prev[i]) + Math.abs(d[i + 1] - prev[i + 1]) + Math.abs(d[i + 2] - prev[i + 2]) > 60) ch++; } out.push(ch / n); } else out.push(0);
      prev = d;
    }
    // blink = frame i differs from i-1, but frame i+k (k<=3) is back close to i-1
    const close = (a, b) => { let ch = 0, n = 0; for (let i = 0; i < a.length; i += 16) { n++; if (Math.abs(a[i] - b[i]) + Math.abs(a[i + 1] - b[i + 1]) + Math.abs(a[i + 2] - b[i + 2]) > 60) ch++; } return ch / n; };
    const blinks = [];
    for (let i = 1; i < keep.length - 1; i++) {
      if (out[i] < 0.01) continue;
      for (let k = 1; k <= 3 && i + k < keep.length; k++) { if (close(keep[i - 1], keep[i + k]) < 0.01) { blinks.push({ frame: i, back: i + k, changed: +out[i].toFixed(3) }); break; } }
    }
    return { perFrame: out.map(v => +v.toFixed(3)), blinks };
  }, shots);
  if (CONFIG.saveBlinks) for (const b of diffs.blinks.slice(0, 5)) {
    for (const f of [b.frame - 1, b.frame, b.back]) await require_free_write(page, CONFIG.outDir + `blink_${b.frame}_f${f}.jpg`, shots[f]);
  }
  const changed = diffs.perFrame.filter(v => v >= CONFIG.diffThreshold).length;
  return { frames: CONFIG.frames, msPerFrame: CONFIG.STEP_MS, framesThatChanged: changed, blinks: diffs.blinks.slice(0, 20), maxChange: Math.max(...diffs.perFrame) };

  // write a frame using the page's download path (no fs in this sandbox): re-screenshot is not possible, so re-encode via canvas
  async function require_free_write(pg, path, b64) {
    const p2 = await pg.context().newPage();
    await p2.setContent(`<img src="data:image/jpeg;base64,${b64}" style="display:block">`);
    const box = await p2.locator('img').boundingBox();
    await p2.screenshot({ path, clip: { x: 0, y: 0, width: Math.max(1, box.width), height: Math.max(1, box.height) } });
    await p2.close();
  }
}
