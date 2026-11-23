// Raw-value scan (oracles 14 + 18). Playwright MCP: browser_run_code_unsafe with { filename }.
// 1) Optionally turns ON every hidden option first (Columns / view menus: ticks every unchecked checkbox, Apply),
// 2) scans visible text for things users should never see: placeholders ({n}, %s), CLI flags (--deny), raw codes
//    (Sync_failed, SNAKE_CASE), undefined/null/NaN/[object Object], and numbers-only cells in columns whose header
//    names a category (Priority, Status, Severity, Type, State, Level, Kind).
// Override config per run: page.context().__qaArgs = { root: '...', enableHidden: true }
async (page) => {
  const CONFIG = { root: 'main', enableHidden: true, menuTrigger: /^(columns|view|display|fields)\b/i };
  Object.assign(CONFIG, page.context().__qaArgs || {});
  const enabled = [];
  if (CONFIG.enableHidden) {
    const btns = page.locator(CONFIG.root).locator('button, [role=button]');
    const n = await btns.count();
    for (let i = 0; i < n; i++) {
      const b = btns.nth(i); const tx = ((await b.getAttribute('aria-label')) || (await b.innerText().catch(() => '')) || '').trim();
      if (!CONFIG.menuTrigger.test(tx)) continue;
      await b.click().catch(() => {}); await page.waitForTimeout(400);
      const boxes = page.locator('[role=menu] input[type=checkbox], [role=dialog] input[type=checkbox], [role=menu] [role=menuitemcheckbox], [class*=Overlay] input[type=checkbox], [role=menu] [role=checkbox], [role=dialog] [role=checkbox]');
      const m = await boxes.count();
      for (let j = 0; j < m; j++) {
        const x = boxes.nth(j);
        const on = await x.evaluate(e => e.checked === true || e.getAttribute('aria-checked') === 'true').catch(() => true);
        if (!on) { const lab = await x.evaluate(e => (e.closest('label') || e.parentElement || e).innerText.trim().slice(0, 40)).catch(() => '?'); await x.click({ force: true }).catch(() => {}); enabled.push(tx + ' → ' + lab); }
      }
      const apply = page.getByRole('button', { name: /^(apply|done|save)$/i }).last();
      if (await apply.count()) await apply.click().catch(() => {}); else await page.keyboard.press('Escape');
      await page.waitForTimeout(500);
    }
  }
  const findings = await page.evaluate(({ root }) => {
    const R = document.querySelector(root) || document.body; const out = [];
    const vis = e => { const r = e.getBoundingClientRect(); return r.width > 0 && r.height > 0; };
    const pats = [
      [/\{[a-z_]{1,12}\}|%[sd]\b|\{\{\s*[A-Za-z_.]+\s*\}\}/, 'placeholder'],
      [/(^|\s)--[a-z][a-z-]{2,}/, 'cli-flag'],
      [/\b(undefined|NaN|\[object Object\])\b|(^|\s)null(\s|$)/, 'js-artefact'],
      [/\b[A-Z][a-z]+_[a-z_]+\b|\b[A-Z]{2,}_[A-Z_]{2,}\b/, 'raw-code'],
    ];
    const walker = document.createTreeWalker(R, NodeFilter.SHOW_TEXT);
    while (walker.nextNode()) {
      const t = walker.currentNode.textContent.trim(); const el = walker.currentNode.parentElement;
      if (!t || !el || !vis(el) || el.closest('code,pre,textarea,input,[contenteditable]')) continue;
      for (const [re, kind] of pats) if (re.test(t)) out.push({ kind, text: t.slice(0, 80) });
    }
    // numbers-only values under category-like column headers
    const CAT = /^(priority|status|severity|type|state|level|kind|category)$/i;
    for (const table of R.querySelectorAll('table, [role=table], [role=grid]')) {
      const heads = [...table.querySelectorAll('th, [role=columnheader]')].map(h => h.innerText.trim());
      heads.forEach((h, idx) => {
        if (!CAT.test(h)) return;
        const cells = [...table.querySelectorAll('tbody tr, [role=row]')].map(r => r.querySelectorAll('td, [role=cell], [role=gridcell]')[idx]).filter(Boolean).map(c => c.innerText.trim());
        const nums = cells.filter(v => /^-?\d+(\.\d+)?$/.test(v));
        if (cells.length && nums.length / cells.length > 0.5) out.push({ kind: 'raw-number-in-category-column', text: `${h}: ${[...new Set(nums)].slice(0, 6).join(', ')}` });
      });
    }
    const seen = new Set(); return out.filter(f => { const k = f.kind + f.text; if (seen.has(k)) return false; seen.add(k); return true; });
  }, { root: CONFIG.root });
  return { enabledHiddenOptions: enabled, findings };
}
