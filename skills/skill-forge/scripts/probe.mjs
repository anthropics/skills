/* probe.mjs — 接口探查器：把录制里"像数据源"的请求复现一遍，判断能不能接口化
 * 用法：
 *   node scripts/probe.mjs --recording <rec.json> [--index 2] [--url 关键字] [--port 18802]
 *                          [--param wd=品牌A] [--minimize] [--go]
 * 安全：默认只发 GET/HEAD/OPTIONS；POST/PUT/DELETE 必须加 --go（有写数据风险）
 * 产出：evidence/<...>/探查报告.md（或 --out 指定目录）
 *
 * 判定口径：
 *   2xx + 字段对得上 + 行数>0  → 能接口化
 *   2xx 但字段/行数为空        → 接口在但不是数据源（或要换参数）
 *   401/403/非 2xx             → 需要额外鉴权（写清缺什么，别猜）
 */
import path from 'node:path';
import fs from 'node:fs';
import { fileURLToPath } from 'node:url';
import { ensureChrome, Cdp, findPage, sleep } from './lib-cdp.mjs';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const arg = (k, d) => { const i = process.argv.indexOf('--' + k); return i >= 0 ? process.argv[i + 1] : d; };
const flag = k => process.argv.includes('--' + k);

const recFile = arg('recording');
if (!recFile) { console.error('用法：node scripts/probe.mjs --recording <rec.json> [--index N|--url 关键字] [--param k=v] [--minimize] [--go]'); process.exit(1); }
const rec = JSON.parse(fs.readFileSync(recFile, 'utf8'));
const port = Number(arg('port', '18802'));
const outDir = arg('out') ? path.resolve(arg('out')) : path.join(ROOT, 'evidence', 'probe_' + new Date().toISOString().slice(0, 19).replace(/[-:T]/g, ''));
fs.mkdirSync(outDir, { recursive: true });

const reqs = (rec.network || []).filter(r => r.url);
const byUrl = arg('url');
const idx = Number(arg('index', '0'));
const target = byUrl ? reqs.find(r => r.url.includes(byUrl)) : reqs[idx];
if (!target) { console.error(`录到的请求里没找到目标（共 ${reqs.length} 条）。用 --index 0..${reqs.length - 1} 或 --url 关键字`); process.exit(1); }

const SAFE = ['GET', 'HEAD', 'OPTIONS'];
if (!SAFE.includes(String(target.method || 'GET').toUpperCase()) && !flag('go')) {
  console.error(`拒绝：${target.method} 可能写数据。确认要试就加 --go`);
  process.exit(2);
}

/* 参数覆盖：--param wd=品牌A （可多次） */
const overrides = [];
for (let i = 0; i < process.argv.length; i++) if (process.argv[i] === '--param' && process.argv[i + 1]) overrides.push(process.argv[i + 1]);
const applyParams = url => {
  const u = new URL(url);
  for (const kv of overrides) { const [k, ...v] = kv.split('='); u.searchParams.set(k, decodeURIComponent(v.join('='))); }
  return u.toString();
};

const host = (() => { try { return new URL(target.url).host; } catch { return ''; } })();
if (!host) { console.error('目标请求 URL 解析失败'); process.exit(3); }

await ensureChrome({ port, mode: 'watch' });
/* 优先复用已打开的同站点标签（登录态在里面），没有才新开一个，不动别人的页面 */
const list = await (await fetch(`http://127.0.0.1:${port}/json/list`)).json();
let page = list.find(t => t.type === 'page' && String(t.url || '').includes(host));
if (!page) {
  const r = await fetch(`http://127.0.0.1:${port}/json/new?${encodeURIComponent('https://' + host + '/')}`, { method: 'PUT' });
  page = await r.json();
  await sleep(2000);
}
const cdp = await Cdp.attach({ port, urlPart: host });
await cdp.enableSession();

const hdrs = { ...(target.headers || {}) };
delete hdrs['content-type'];

async function callUrl(url) {
  const expr = `(async () => {
    try {
      const opt = { method: ${JSON.stringify(target.method || 'GET')}, credentials: 'include'
        ${Object.keys(hdrs).length ? `, headers: ${JSON.stringify(hdrs)}` : ''}
        ${target.body ? `, body: ${JSON.stringify(target.body)}` : ''} };
      const r = await fetch(${JSON.stringify(url)}, opt);
      const t = await r.text();
      return JSON.stringify({ ok: true, status: r.status, ct: r.headers.get('content-type') || '', len: t.length, body: t.slice(0, 200000) });
    } catch (e) { return JSON.stringify({ ok: false, err: String(e && e.message || e) }); }
  })()`;
  const raw = await cdp.evalJs(expr, { awaitPromise: true }).catch(e => JSON.stringify({ ok: false, err: String(e.message || e) }));
  let r; try { r = typeof raw === 'string' ? JSON.parse(raw) : raw; } catch { r = { ok: false, err: '页面返回不可解析' }; }
  if (r.ok && typeof r.body === 'string') {
    try { r.json = JSON.parse(r.body); } catch { /* 非 JSON */ }
  }
  return r;
}

function summarize(j) {
  if (!j) return { fields: null, rows: null, path: null };
  const walk = (o, d = 0, trail = []) => {
    if (!o || typeof o !== 'object' || d > 3) return null;
    for (const [k, v] of Object.entries(o)) {
      if (Array.isArray(v) && v.length && typeof v[0] === 'object') return { arr: v, path: [...trail, k].join('.') };
      const g = walk(v, d + 1, [...trail, k]); if (g) return g;
    }
    return null;
  };
  const hit = Array.isArray(j) ? { arr: j, path: '' } : walk(j);
  if (hit && hit.arr.length) return { fields: Object.keys(hit.arr[0]), rows: hit.arr.length, path: hit.path };
  if (!Array.isArray(j)) return { fields: Object.keys(j), rows: null, path: null };
  return { fields: null, rows: null, path: null };
}

console.log(`目标：${target.method} ${target.url.slice(0, 120)}`);
const url0 = applyParams(target.url);
const t0 = Date.now();
const res = await callUrl(url0);
const ms = Date.now() - t0;
const sum = summarize(res.json);
const sameFields = target.fields?.length && sum.fields?.length
  ? target.fields.filter(f => sum.fields.includes(f)).length + '/' + target.fields.length
  : '—';
console.log(`复现：状态 ${res.status ?? res.err}，${ms}ms，字段 ${sum.fields?.length ?? 0}，行 ${sum.rows ?? '—'}`);
console.log(`与录制比对：录制字段 ${target.fields?.length ?? 0} 个，命中 ${sameFields}；录制行 ${target.rows ?? '—'} / 现在 ${sum.rows ?? '—'}`);

/* 最小参数集：逐个删 query 参数看是否还能拿到数据 */
let minResult = null;
if (flag('minimize') && res.ok) {
  const u = new URL(url0);
  const keys = [...u.searchParams.keys()];
  const keep = [];
  for (const k of keys) {
    const test = new URL(url0); test.searchParams.delete(k);
    const r = await callUrl(test.toString());
    const s = summarize(r.json);
    const is2xx = r.ok && r.status >= 200 && r.status < 300;
    // 首次复现有几行数据，删参数后必须还有同样形态的数据；只变空壳不算过
    const stillOk = is2xx && (sum.rows != null ? (s.rows != null && s.rows > 0) : !!s.fields);
    console.log(`  删 ${k} → ${r.status ?? r.err}，行 ${s.rows ?? '—'} ${stillOk ? '（可删）' : '（必需）'}`);
    if (!stillOk) keep.push(k);
    await sleep(300);
  }
  minResult = { all: keys, required: keep };
}

const verdict = !res.ok ? `失败：${res.err}`
  : res.status === 401 || res.status === 403 ? `需要额外鉴权（HTTP ${res.status}）：录制时的登录态在这里不成立，得先解决登录/令牌`
    : res.status >= 200 && res.status < 300 && sum.rows !== null && sum.rows > 0 ? '能接口化：状态正常、字段和行数都拿得到'
      : res.status >= 200 && res.status < 300 ? '接口通，但这次没解析出多行数据（可能参数不对，或它不是列表接口）'
        : `状态 ${res.status}，先看是不是参数/权限问题`;

const md = `# 探查报告：${path.basename(recFile)}

- 目标请求：\`${target.method} ${target.url}\`
- 复现时间：${new Date().toLocaleString('zh-CN')}｜耗时 ${ms}ms
- 浏览器端口：${port}（沿用录制时的登录态）

## 结果

| 项 | 录制时 | 复现时 |
|---|---|---|
| 状态 | ${target.status ?? '—'} | ${res.status ?? res.err ?? '—'} |
| 返回字段 | ${target.fields?.length ?? 0} | ${sum.fields?.length ?? 0}（命中 ${sameFields}） |
| 数据行 | ${target.rows ?? '—'} | ${sum.rows ?? '—'} |

**判定：${verdict}**

${minResult ? `### 最小参数集\n\n- 原有参数：${minResult.all.join(', ') || '（无）'}\n- 必需参数：${minResult.required.join(', ') || '（都不必需）'}\n` : ''}

## 样例响应（前 600 字）

\`\`\`
${(res.body || res.err || '').slice(0, 600)}
\`\`\`

## 下一步

${verdict.startsWith('能接口化')
    ? '1. 把「URL 模板 + 必需参数 + 字段映射」写进技能配置；\n2. 用 `--param` 换一组参数再验一次（换日期/账户），确认不是只有这一条数据能出；\n3. 跟用户确认后生成接口版技能包。'
    : '1. 先把失败原因说清楚（登录态？参数？频率限制？），别硬试；\n2. 确认走 UI 自动化更稳妥的话，退回录制回放路线。'}
`;
fs.writeFileSync(path.join(outDir, '探查报告.md'), md, 'utf8');
/* 给 build_skill --type api 用的草稿：用户确认后才拿去生成技能包 */
const apiDraft = {
  name: path.basename(recFile).replace(/_\d+\.rec\.json$/, ''),
  verdict,
  request: {
    method: String(target.method || 'GET').toUpperCase(),
    url: url0,
    /* 铁律：body 必须是录制原文整段（不做任何改写）。参数位由 diffrec 标成 {{k}} 后再替换 */
    body: target.body || '',
    bodyTemplate: target.body || '',
    bodySource: target.body ? 'recording' : 'none'
  },
  dataPath: sum.path || null,
  fields: sum.fields || [],
  params: Object.fromEntries(new URL(url0).searchParams.entries()),
  requiredParams: minResult?.required ?? null,
  sampleRows: sum.rows ?? null,
  sourceRecording: path.basename(recFile),
  probedAt: new Date().toISOString()
};
fs.writeFileSync(path.join(outDir, '接口配置草稿.json'), JSON.stringify(apiDraft, null, 1), 'utf8');
fs.writeFileSync(path.join(outDir, 'probe.json'), JSON.stringify({
  target, result: { status: res.status, ms, fields: sum.fields, rows: sum.rows, ok: res.ok, err: res.err }, sameFields, minimize: minResult, verdict
}, null, 1), 'utf8');
console.log(`\n判定：${verdict}`);
console.log(`报告：${path.join(outDir, '探查报告.md')}`);
cdp.close();
