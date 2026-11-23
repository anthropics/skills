// Surface inventory for Playwright MCP: browser_run_code_unsafe with { filename: <copy of this file> }.
// Lists every interactive thing on the current page, including what's hidden behind menus, so coverage is measured
// against what the product actually offers, not against memory. Run it on every page AND every state
// (empty, queued, running, stopped, failed, drawer open, dark mode...), save the JSON, and feed it to
//   coverage.py add-inventory <feature> inventory.json --page <page> --state <state>
async (page) => {
  const CONFIG = {
    root: 'main',                 // scope; use 'body' to include header/nav
    openMenus: true,              // click "more"/"Columns"/kebab/dropdown triggers to reveal hidden items, then close
    menuTriggers: /^(more actions|columns|filter|sort|group( by)?|severity|kind|status|labels?|business area|type|priority|view)\b/i,
  };
  Object.assign(CONFIG, page.context().__qaArgs || {});  // per-run overrides (used by the self-test)
  const grab = async () => page.evaluate((root) => {
    const R = document.querySelector(root) || document.body;
    const vis = e => { const r = e.getBoundingClientRect(); const s = getComputedStyle(e); return r.width > 0 && r.height > 0 && s.visibility !== 'hidden' && s.display !== 'none'; };
    const roleOf = e => e.getAttribute('role') || ({ A: 'link', BUTTON: 'button', SELECT: 'combobox', TEXTAREA: 'textarea' }[e.tagName]) ||
      (e.tagName === 'INPUT' ? ({ checkbox: 'checkbox', radio: 'radio', number: 'spinbutton', search: 'searchbox' }[e.type] || 'textbox') : null);
    const nameOf = e => (e.getAttribute('aria-label') || e.innerText || e.value || e.placeholder || e.title || '').trim().replace(/\s+/g, ' ').slice(0, 80);
    const sel = 'a[href],button,input,select,textarea,[role=button],[role=link],[role=tab],[role=menuitem],[role=menuitemcheckbox],[role=menuitemradio],[role=checkbox],[role=switch],[role=option],[role=combobox]';
    const seen = new Set(); const out = []; const rows = {};
    for (const e of R.querySelectorAll(sel)) {
      if (!vis(e)) continue;
      const kind = roleOf(e) || 'button'; const label = nameOf(e);
      // collapse repeated data rows (same link pattern) into one row-type item: test a sample, not every record
      const href = e.getAttribute('href') || '';
      const rowKey = (href.match(/[?&](finding|screen|flow|run|item|id|case)=/) || [])[1];
      if (rowKey) { rows[rowKey] = (rows[rowKey] || 0) + 1; continue; }
      const key = kind + '|' + label; if (seen.has(key)) continue; seen.add(key);
      out.push({ kind, label, disabled: !!(e.disabled || e.getAttribute('aria-disabled') === 'true'), href: e.getAttribute('href') || null });
    }
    for (const [k, n] of Object.entries(rows)) out.push({ kind: 'row', label: `${k} rows (${n} on this page; test a sample of 3 incl. first/last)`, disabled: false, href: null });
    return out;
  }, CONFIG.root);
  const base = await grab();
  const hidden = [];
  if (CONFIG.openMenus) {
    const all0 = page.locator(CONFIG.root).locator('button, [role=button]');
    const cnt = await all0.count(); const idx = [];
    for (let i = 0; i < cnt && idx.length < 15; i++) { const b = all0.nth(i); const hp = await b.getAttribute('aria-haspopup'); const tx = ((await b.getAttribute('aria-label')) || (await b.innerText().catch(() => '')) || '').trim(); if (hp || CONFIG.menuTriggers.test(tx)) idx.push(i); }
    const triggers = { nth: i => all0.nth(idx[i]) }; const n = idx.length;
    for (let i = 0; i < n; i++) {
      const t = triggers.nth(i); const label = ((await t.getAttribute('aria-label')) || (await t.innerText().catch(() => '')) || '').trim();
      try {
        await t.click({ timeout: 2000 }); await page.waitForTimeout(500);
        const items = await page.evaluate(() => {
          const vis = e => { const r = e.getBoundingClientRect(); return r.width > 0 && r.height > 0; };
          // ARIA menus/listboxes/dialogs AND plain overlay panels (many design systems render filters as a div overlay)
          const pops = [...document.querySelectorAll('[role=menu],[role=listbox],[role=dialog],[popover],[class*=Overlay],[class*=Popover],[class*=SelectPanel]')].filter(vis);
          const seen = new Set(); const res = [];
          for (const p of pops) for (const e of p.querySelectorAll('[role^=menuitem],[role=option],[role=checkbox],[role=radio],input,button')) {
            if (!vis(e) && !(e.tagName === 'INPUT' && (e.type === 'checkbox' || e.type === 'radio'))) continue;
            const lab = (e.getAttribute('aria-label') || (e.id && document.querySelector(`label[for="${e.id}"]`)?.innerText) || e.closest('label')?.innerText || e.parentElement?.innerText || e.innerText || e.placeholder || '').trim().replace(/\s+/g, ' ').slice(0, 80);
            const kind = e.getAttribute('role') || (e.tagName === 'INPUT' ? (e.type === 'checkbox' ? 'checkbox' : e.type === 'radio' ? 'radio' : 'textbox') : 'button');
            const k = kind + '|' + lab; if (!lab || seen.has(k)) continue; seen.add(k);
            res.push({ kind, label: lab, disabled: e.getAttribute('aria-disabled') === 'true' || !!e.disabled });
          }
          return res;
        });
        items.forEach(it => hidden.push({ ...it, via: label || 'menu' }));
        await page.keyboard.press('Escape'); await page.waitForTimeout(300);
      } catch (e) { await page.keyboard.press('Escape').catch(() => {}); }
    }
  }
  const all = base.concat(hidden);
  const result = { url: page.url(), count: all.length, visible: base.length, behindMenus: hidden.length, items: all };
  // stash for saving: then call browser_evaluate with function `() => window.__qaInventory` and filename `inv_<page>_<state>.json`
  await page.evaluate(r => { window.__qaInventory = r; }, result);
  return { url: result.url, count: result.count, visible: result.visible, behindMenus: result.behindMenus };
}
