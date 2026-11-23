// Console & network sentinel — REPORT. Playwright MCP: browser_run_code_unsafe with { filename: <this file> }.
// Returns what the sentinel recorded since start (or since the last report with CLEAR=true), grouped so repeated
// signals show once with a count, ordered errors first. Triage each group: file a bug (with the state and page it
// came from), mark it known (existing bug id), or expected-with-reason. Untriaged groups block sign-off.
async (page) => {
  const CLEAR = false;          // true = empty the buffer after reading (e.g. between features)
  const S = page.context().__qaSentinel;
  if (!S) return { error: 'sentinel not started: run scripts/sentinel_start.js first' };
  const norm = s => (s || '').replace(/[0-9a-f]{8}-[0-9a-f-]{27,}/gi, '<uuid>').replace(/\b[0-9A-Z]{26}\b/g, '<ulid>').replace(/\d{3,}/g, '<n>').replace(/\?.*$/, '?…');
  const groups = {};
  for (const e of S.events) {
    const key = e.kind + ' ' + (e.method || '') + ' ' + norm(e.url) + ' ' + norm(e.text).slice(0, 120);
    const g = groups[key] || (groups[key] = { kind: e.kind, method: e.method, sample: e.url || e.text, text: e.text, count: 0, states: new Set(), pages: new Set(), first: e.t });
    g.count++; g.states.add(e.state); g.pages.add(e.page);
  }
  const rank = k => k.startsWith('pageerror') ? 0 : k.startsWith('http.5') ? 1 : k.startsWith('console.error') ? 2 : k.startsWith('http.4') ? 3 : k.startsWith('requestfailed') ? 4 : 5;
  const out = Object.values(groups).sort((a, b) => rank(a.kind) - rank(b.kind) || b.count - a.count)
    .map(g => ({ kind: g.kind, method: g.method, sample: (g.sample || '').slice(0, 160), text: g.text && g.text !== g.sample ? g.text.slice(0, 160) : undefined, count: g.count, states: [...g.states].slice(0, 6), pages: [...g.pages].slice(0, 4), first: g.first }));
  const total = S.events.length;
  if (CLEAR) S.events = [];
  return { since: S.startedAt, currentState: S.state, totalEvents: total, groups: out.length, signals: out };
}
