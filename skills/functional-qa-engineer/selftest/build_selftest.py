#!/usr/bin/env python3
"""Build .playwright-mcp/qa/selftest.js: one Playwright MCP script that embeds the skill's own browser scripts
(so the test exercises exactly the code the skill uses) and runs each learned lesson against its fixture.
Run from the project root after selftest.sh has started the fixture server on :3101.
"""
import os, re, sys
SKILL = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
S = os.path.join(SKILL, 'scripts')
OUT = sys.argv[1] if len(sys.argv) > 1 else '.playwright-mcp/qa/selftest.js'

def fn(name):
    src = open(os.path.join(S, name)).read()
    body = '\n'.join(l for l in src.splitlines() if not l.lstrip().startswith('//')).strip()
    return body.rstrip(';')

harness = r'''async (page) => {
  const BASE = 'http://127.0.0.1:3101/';
  const X = {
    cta: %(cta)s,
    raw: %(raw)s,
    inventory: %(inventory)s,
    loading: %(loading)s,
    flicker: %(flicker)s,
    sentinelStart: %(sstart)s,
    sentinelReport: %(sreport)s,
  };
  const contrast = %(contrast)s;
  const results = [];
  const args = a => { page.context().__qaArgs = a; };
  const t = async (lesson, miss, fnc) => { try { const r = await fnc(); results.push({ lesson, miss, pass: !!r.pass, detail: r.detail }); } catch (e) { results.push({ lesson, miss, pass: false, detail: 'error: ' + String(e.message || e).slice(0, 160) }); } finally { page.context().__qaArgs = {}; } };

  await t('every-cta-destination', 'M16 Open Secrets → blank page', async () => {
    args({ root: 'main', startUrl: BASE + 'cta.html' });
    const r = await X.cta(page); const f = r.flagged.map(x => x.label + ':' + x.flags.join('+'));
    return { pass: f.some(x => x.startsWith('Open Secrets:') && x.includes('BLANK')) && !f.some(x => x.startsWith('Open Docs')), detail: f };
  });
  await t('hidden-options-on', 'M17 hidden Priority column shows 3/2/0', async () => {
    await page.goto(BASE + 'columns.html'); args({ root: 'main', openMenus: true });
    await X.inventory(page); const inv = await page.evaluate(() => window.__qaInventory);
    const sawOption = inv.items.some(i => /priority/i.test(i.label) && i.via);
    await page.goto(BASE + 'columns.html'); args({ root: 'main', enableHidden: true });
    const r = await X.raw(page); const raw = r.findings.filter(f => f.kind === 'raw-number-in-category-column');
    return { pass: sawOption && raw.length > 0, detail: { inventoryFoundHiddenPriority: sawOption, enabled: r.enabledHiddenOptions, raw } };
  });
  await t('loading-frames', 'M18 blank page with a divider line', async () => {
    args({ outDir: '.playwright-mcp/qa/out/', ready: { role: 'button', name: /Ready/ }, windowMs: 6500, slowWindowMs: 6500, STEP_MS: 500,
      scenarios: [{ name: 'fixture_url', kind: 'url', url: BASE + 'slowload.html' }] });
    const r = await X.loading(page); const fast = r.find(x => x.name === 'fast_fixture_url');
    return { pass: fast && fast.blankFrames >= 4, detail: r };
  });
  await t('frame-diff-flicker', 'M20 graph flicker (positive + negative control)', async () => {
    await page.goto(BASE + 'flicker.html'); await page.waitForTimeout(500);
    args({ url: null, frames: 30, STEP_MS: 80, region: { x: 0, y: 0, width: 640, height: 340 }, saveBlinks: false });
    const pos = await X.flicker(page);
    await page.goto(BASE + 'static.html'); await page.waitForTimeout(500);
    args({ url: null, frames: 20, STEP_MS: 80, region: { x: 0, y: 0, width: 640, height: 340 }, saveBlinks: false });
    const neg = await X.flicker(page);
    return { pass: pos.blinks.length > 0 && neg.blinks.length === 0, detail: { flickerBlinks: pos.blinks.length, staticBlinks: neg.blinks.length } };
  });
  await t('sentinel-triaged', 'sentinel: failed API call + console.error + page crash unnoticed', async () => {
    await X.sentinelStart(page); page.context().__qaSentinel.state = 'selftest/signals';
    await page.goto(BASE + 'signals.html'); await page.waitForTimeout(1500);
    const r = await X.sentinelReport(page); const mine = r.signals.filter(s => s.states.includes('selftest/signals'));
    const kinds = new Set(mine.map(s => s.kind));
    page.context().__qaSentinel.state = 'unlabelled';
    return { pass: kinds.has('pageerror') && kinds.has('http.404') && kinds.has('console.error'), detail: [...kinds] };
  });
  await t('dark-contrast', 'contrast: invisible avatar initials in dark mode', async () => {
    await page.goto(BASE + 'contrast.html'); await page.waitForTimeout(300);
    const r = await page.evaluate(contrast);
    return { pass: /LOWCONTRAST [1-9]/.test(r) && /"AK"/.test(r), detail: r.split('\n').slice(0, 3) };
  });
  return { passed: results.filter(r => r.pass).length, failed: results.filter(r => !r.pass).length, results };
}'''
code = harness % {
    'cta': fn('cta_destinations.js'), 'raw': fn('raw_values.js'), 'inventory': fn('surface_inventory.js'),
    'loading': fn('loading_sweep.js'), 'flicker': fn('flicker_scan.js'), 'sstart': fn('sentinel_start.js'),
    'sreport': fn('sentinel_report.js'), 'contrast': fn('contrast_scan.js'),
}
os.makedirs(os.path.dirname(OUT), exist_ok=True)
open(OUT, 'w').write(code)
print('built', OUT, len(code), 'chars')
