// Console & network sentinel — START. Playwright MCP: browser_run_code_unsafe with { filename: <this file> }.
// Attach once at the start of a session. From then on every console error/warning, uncaught page error,
// HTTP 4xx/5xx response and failed request on ANY page in this browser context is recorded with the URL and
// the current "state" label. A human tester keeps DevTools open; this is that, for the whole session.
// Label what you're doing so each signal maps to a coverage item:
//   browser_run_code_unsafe code: async (page) => { page.context().__qaSentinel.state = 'findings/drawer-open'; }
// Read with scripts/sentinel_report.js. Every recorded signal must be triaged before sign-off (check: sentinel-triaged).
async (page) => {
  const ctx = page.context();
  if (ctx.__qaSentinel && ctx.__qaSentinel.attached) return { already: true, events: ctx.__qaSentinel.events.length, state: ctx.__qaSentinel.state };
  const S = ctx.__qaSentinel = { attached: true, state: 'unlabelled', events: [], startedAt: new Date().toISOString(),
    ignore: [/favicon\.ico/, /google-analytics|googletagmanager|amplitude|hotjar|sentry\.io|clarity\.ms|doubleclick/i] };
  const push = (p, e) => {
    const url = e.url || ''; if (S.ignore.some(r => r.test(url))) return;
    S.events.push({ t: new Date().toISOString().slice(11, 19), state: S.state, page: (p.url() || '').replace(/^https?:\/\/[^/]+/, '').slice(0, 120), ...e });
  };
  const watch = p => {
    p.on('console', m => { const ty = m.type(); if (ty === 'error' || ty === 'warning') push(p, { kind: 'console.' + ty, text: m.text().slice(0, 300), url: (m.location() || {}).url || '' }); });
    p.on('pageerror', err => push(p, { kind: 'pageerror', text: String(err && err.message || err).slice(0, 300) }));
    p.on('response', r => { const st = r.status(); if (st >= 400) { const rq = r.request(); push(p, { kind: 'http.' + st, method: rq.method(), url: r.url().slice(0, 200), resourceType: rq.resourceType() }); } });
    p.on('requestfailed', rq => { const f = rq.failure(); if (f && /ERR_ABORTED/.test(f.errorText)) return; push(p, { kind: 'requestfailed', method: rq.method(), url: rq.url().slice(0, 200), text: f && f.errorText, resourceType: rq.resourceType() }); });
  };
  for (const p of ctx.pages()) watch(p);
  ctx.on('page', watch);
  return { attached: true, pages: ctx.pages().length };
}
