// CTA destination check (oracle 17). Playwright MCP: browser_run_code_unsafe with { filename }.
// Clicks every link/button in scope (skipping destructive ones), records where it lands, and flags:
//   BLANK   landing page has almost no text, or an HTTP error
//   MISMATCH none of the label's meaningful words appear in the landing URL, title or first heading
// Run it on every state that has CTAs (empty, failed, warnings, Needs Attention, toasts, drawers).
// Override config per run: page.context().__qaArgs = { root: '...', startUrl: '...', ready: { role: 'button', name: /Run/ } }
// Before filing a flag, confirm it with a real mouse click after full load (check verify-probe): early clicks and hidden
// duplicates are the classic false alarms of this probe.
async (page) => {
  const CONFIG = { root: 'main', startUrl: null, max: 40, ready: null, skip: /delete|remove|stop|cancel|logout|log out|sign out|discard|reset|archive|revoke|unpublish/i };
  Object.assign(CONFIG, page.context().__qaArgs || {});
  const start = CONFIG.startUrl || page.url();
  const STOP = new Set(['open', 'view', 'go', 'to', 'the', 'a', 'an', 'and', 'of', 'in', 'on', 'see', 'show', 'more', 'all', 'your', 'for', 'click', 'here', 'now']);
  // wait until the page is really ready (a visible element that only exists once content loaded), else networkidle;
  // clicking during load or on hidden duplicates (collapsed headers, href="#") gives false MISMATCH/BLANK results
  const settle = async () => { if (CONFIG.ready) await page.getByRole(CONFIG.ready.role, { name: CONFIG.ready.name }).first().waitFor({ state: 'visible', timeout: 60000 }).catch(() => {}); else await page.waitForLoadState('networkidle').catch(() => {}); await page.waitForTimeout(600); };
  await page.goto(start); await settle();
  const labels = await page.evaluate(({ root }) => {
    const R = document.querySelector(root) || document.body;
    return [...R.querySelectorAll('a[href],button,[role=button],[role=link]')].filter(e => { const r = e.getBoundingClientRect(); return r.width > 0 && r.height > 0; })
      .map(e => (e.getAttribute('aria-label') || e.innerText || '').trim().replace(/\s+/g, ' ')).filter(Boolean);
  }, { root: CONFIG.root });
  const uniq = [...new Set(labels)].filter(l => !CONFIG.skip.test(l)).slice(0, CONFIG.max);
  const results = [];
  for (const label of uniq) {
    await page.goto(start); await settle();
    const el = page.locator(CONFIG.root).getByText(label, { exact: true }).locator('visible=true').first();
    if (!(await el.count())) continue;
    const before = page.url(); let status = null; let target = page;
    const popup = page.context().waitForEvent('page', { timeout: 2500 }).catch(() => null);
    const resp = page.waitForResponse(r => r.request().isNavigationRequest(), { timeout: 2500 }).catch(() => null);
    await el.click({ timeout: 3000 }).catch(() => {});
    const np = await popup; if (np) { target = np; await np.waitForLoadState().catch(() => {}); }
    const r = await resp; if (r) status = r.status();
    await target.waitForTimeout(1200);
    const land = await target.evaluate(() => ({ url: location.href, title: document.title, h1: ([...document.querySelectorAll('h1,h2,[role=heading]')].find(h => { const r = h.getBoundingClientRect(); return r.width > 0 && r.height > 0 && getComputedStyle(h).visibility !== 'hidden'; }) || {}).innerText || '', text: (document.body.innerText || '').trim().length })).catch(() => ({}));
    if (np) await np.close().catch(() => {});
    const moved = land.url !== before || !!np;
    const words = label.toLowerCase().split(/[^a-z0-9]+/).filter(w => w.length > 2 && !STOP.has(w));
    const hay = ((land.url || '') + ' ' + (land.title || '') + ' ' + (land.h1 || '')).toLowerCase();
    const flags = [];
    if (moved && ((land.text || 0) < 30 || (status && status >= 400))) flags.push('BLANK');
    if (moved && words.length && !words.some(w => hay.includes(w))) flags.push('MISMATCH');
    results.push({ label, moved, newTab: !!np, status, landing: (land.url || '').slice(0, 120), heading: (land.h1 || '').slice(0, 60), textChars: land.text, flags });
  }
  await page.goto(start).catch(() => {});
  return { start, checked: results.length, flagged: results.filter(r => r.flags.length), all: results };
}
