// Loading-state sweep for Playwright MCP: browser_run_code_unsafe with { filename: <copy of this file> }.
// Copy this file next to your workspace, edit CONFIG, run it. It samples what is VISIBLE every STEP_MS
// for each entry path, on fast and throttled network, and saves frames so you can look at them.
// A frame is CONTENT when READY is visible, otherwise BLANK. Look at the BLANK frames yourself:
// a DOM "loader" can exist without being visible, so judge from the screenshots.
async (page) => {
  const CONFIG = {
    outDir: '.playwright-mcp/ls/',           // must exist (mkdir -p first)
    ready: { role: 'button', name: /Save|Run|Get started/ }, // something only present when content is shown
    windowMs: 12000, slowWindowMs: 25000, STEP_MS: 500,
    scenarios: [
      // kind: 'click' = load `from`, then click the `tab` role element; 'url' = direct load; 'reload' = reload current
      { name: 'tab_click', kind: 'click', from: 'https://example.com/projects/ID/test-cases', tab: /Dashboard/ },
      { name: 'direct_url', kind: 'url', url: 'https://example.com/projects/ID/dashboard' },
      { name: 'reload', kind: 'reload' },
    ],
    throttle: { offline: false, latency: 400, downloadThroughput: 200000, uploadThroughput: 100000 },
  };
  Object.assign(CONFIG, page.context().__qaArgs || {});  // per-run overrides (used by the self-test)
  const readyLoc = () => page.getByRole(CONFIG.ready.role, { name: CONFIG.ready.name }).first();
  const sample = async (name, totalMs) => {
    const t0 = Date.now(); let firstReady = null, blank = 0, i = 0;
    while (Date.now() - t0 < totalMs) {
      const t = ((Date.now() - t0) / 1000).toFixed(1);
      const ok = await readyLoc().isVisible().catch(() => false);
      if (ok && firstReady === null) firstReady = t;
      if (!ok) blank++;
      if (i % 2 === 0 || (ok && firstReady === t)) await page.screenshot({ path: `${CONFIG.outDir}${name}_${t}s.png` }).catch(() => {});
      if (ok && i > 2) break;
      i++; await page.waitForTimeout(CONFIG.STEP_MS);
    }
    return { name, contentAt: firstReady ? firstReady + 's' : `never within ${totalMs / 1000}s`, blankFrames: blank };
  };
  const cdp = await page.context().newCDPSession(page);
  await cdp.send('Network.enable');
  const out = [];
  for (const slow of [false, true]) {
    await cdp.send('Network.emulateNetworkConditions', slow ? CONFIG.throttle : { offline: false, latency: 0, downloadThroughput: -1, uploadThroughput: -1 });
    const win = slow ? CONFIG.slowWindowMs : CONFIG.windowMs;
    for (const s of CONFIG.scenarios) {
      const name = `${slow ? 'slow' : 'fast'}_${s.name}`;
      if (s.kind === 'click') {
        await page.goto(s.from); const tab = page.getByRole('tab', { name: s.tab }).first();
        await tab.waitFor({ timeout: 60000 }); await page.waitForTimeout(1000); await tab.click();
      } else if (s.kind === 'url') { await page.goto('about:blank'); page.goto(s.url).catch(() => {}); }
      else { page.reload().catch(() => {}); }
      out.push(await sample(name, win));
    }
  }
  await cdp.send('Network.emulateNetworkConditions', { offline: false, latency: 0, downloadThroughput: -1, uploadThroughput: -1 });
  return out; // then Read the BLANK frames; repeat the first scenario after ~15 min idle to catch cold starts
}
