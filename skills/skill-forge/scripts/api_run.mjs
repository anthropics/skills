/* api_run.mjs — 接口版执行器（由 skill-forge 生成，进入子技能包）
 * 用法：
 *   node scripts/api_run.mjs --config 配置 [--param date=2026-11-03] [--out 结果.csv] [--port 18802] [--go]
 *                            [--profile <专属 user-data-dir>] [--bg] [--allow-fields]
 *                            [--allow-write --ack "上限=…｜批准=…"]
 * 说明：
 *   - 走「已登录浏览器页面内 fetch」：同源带 cookie，不用另外搞 token
 *   - 独立登录态：先 `scripts/login.mjs` 存好 profile，这里 `--profile` 指同一个目录即可无人值守
 *   - body 用「模板替换法」：模板来自录制原文，只换 {{变量}}，其余一个字符都不改
 *   - 默认预览（只打印，不写文件）；--go 才落 CSV；--bg 屏幕外跑
 *   - 写接口（POST/PUT/PATCH/DELETE）必须再加 --allow-write，否则拒跑（防误改后台真实数据）
 *   - 校验不过直接非 0 退出，绝不静默返回空表
 * 退出码：0 通过 / 2 校验不过 / 3 浏览器或请求失败 / 4 配置有问题或写闸门拦下 / 5 写闸门确认没写清
 */
import path from 'node:path';
import fs from 'node:fs';
import { fileURLToPath } from 'node:url';
import { ensureChrome, Cdp, sleep, closeChromeSmart, farmPreWriteSnapshot } from './lib-cdp.mjs';
import { normMethod, writeGate, isWrite } from './lib-guard.mjs';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const arg = (k, d) => { const i = process.argv.indexOf('--' + k); return i >= 0 ? process.argv[i + 1] : d; };
const flag = k => process.argv.includes('--' + k);

const cfgDir = arg('config', path.join(ROOT, '配置'));
const cfgFile = path.join(cfgDir, '接口.json');
if (!fs.existsSync(cfgFile)) { console.error(`配置缺失：${cfgFile}`); process.exit(4); }
const cfg = JSON.parse(fs.readFileSync(cfgFile, 'utf8'));
const method = normMethod(cfg.request?.method || 'GET');
const port = Number(arg('port', String(cfg.port || 18802)));
/* 收尾（全局规则）：跑完按端口关掉自己开的浏览器；--keep-open / KEEP_BROWSER=1 才留
 * 农场档位（--port 指的农场口）自动识别、只连不关——档位归农场总管管 */
const done = async code => {
  if (!flag('keep-open') && process.env.KEEP_BROWSER !== '1') {
    try { await closeChromeSmart(port, { log: () => {} }); } catch { /* 关不掉不影响结果 */ }
  }
  process.exit(code);
};

/* ---- 参数：配置默认值 ← --param 覆盖 ---- */
const params = { ...(cfg.params || {}) };
for (let i = 0; i < process.argv.length; i++) {
  if (process.argv[i] === '--param' && process.argv[i + 1]) {
    const [k, ...v] = process.argv[i + 1].split('=');
    params[k] = decodeURIComponent(v.join('='));
  }
}
for (const k of cfg.requiredParams || []) {
  if (params[k] == null || params[k] === '') { console.error(`必需参数缺失：${k}（用 --param ${k}=... 传）`); process.exit(4); }
}

/* ---- URL 渲染：${k} 占位 + 只把 queryParams 合并进 query（body 专用参数不塞 URL） ---- */
let url = String(cfg.request?.url || '');
if (!url) { console.error('接口.json 缺 request.url'); process.exit(4); }
url = url.replace(/\$\{(\w+)\}/g, (_, k) => encodeURIComponent(params[k] ?? ''));
const u = new URL(url);
const qKeys = Array.isArray(cfg.queryParams) ? cfg.queryParams : Object.keys(params);
for (const k of qKeys) if (params[k] != null) u.searchParams.set(k, String(params[k]));
url = u.toString();

/* ---- body 渲染：模板替换法（只换 {{k}}，其余字符原样，禁止重写） ---- */
function renderBody(tpl, p) {
  const t = String(tpl || '');
  if (!t) return '';
  const isJson = /^\s*[[{]/.test(t);
  const isForm = !isJson && /^[^=&\s]+=[^&]*(&|$)/.test(t);
  const out = t.replace(/\{\{(\w+)\}\}/g, (_, k) => {
    const v = p[k];
    if (v == null || v === '') { console.error(`body 模板变量缺值：${k}（用 --param ${k}=... 传）`); process.exit(4); }
    const s = String(v);
    return isJson ? JSON.stringify(s).slice(1, -1) : (isForm ? encodeURIComponent(s) : s);
  });
  const left = out.match(/\{\{\w+\}\}/);
  if (left) { console.error(`body 模板还有未替换占位：${left[0]}`); process.exit(4); }
  return out;
}
const bodyTemplate = cfg.request?.bodyTemplate || (cfg.request?.bodyMode === 'template' ? cfg.request?.body : '');
const body = bodyTemplate ? renderBody(bodyTemplate, params) : String(cfg.request?.body || '');
if (flag('debug')) { console.log('URL:', url); if (body) console.log('BODY:', body.slice(0, 500)); }
/* --dry：只渲染 URL/BODY 就退出，不碰浏览器（验模板替换对不对、核对参数用） */
if (flag('dry')) {
  console.log(JSON.stringify({ url, method, params, bodyTemplate: bodyTemplate || null, body }, null, 1));
  process.exit(0);
}

/* ---- 写接口闸门：非 GET 必须显式 --allow-write（合规要求，见 lib-guard.mjs） ---- */
const ACK = arg('ack') || '';
const gate = writeGate({ method, allowWrite: flag('allow-write'), ack: ACK });
if (!gate.ok) {
  console.error(gate.msg);
  process.exit(gate.code);
}
/* ---- 写操作留痕：确认原文进 logs/写操作确认.log（出事能查） ---- */
if (isWrite(method)) {
  try {
    const logDir = path.join(ROOT, 'logs');
    fs.mkdirSync(logDir, { recursive: true });
    fs.appendFileSync(path.join(logDir, '写操作确认.log'),
      `[${new Date().toISOString()}] ${method} ${cfg.request?.url || ''} | ack=${ACK}
`, 'utf8');
  } catch (e) { console.error('写确认日志没写成（不影响执行）：' + e.message); }
/* ---- 写前快照（跑在农场档位上时）：出事能整档回滚；快照打不上=带病写，默认不写 ---- */
  try {
    const snap = await farmPreWriteSnapshot(port, `写前快照 ${cfg.name || ''} ${method}`);
    if (snap) console.error(`[农场] 已打写前快照（档 ${snap.slot.id}${snap.slot.note ? ' ' + snap.slot.note : ''}）——出事可整档回滚`);
  } catch (e) {
    if (flag('no-snap')) console.error(`⚠️ 写前快照失败但 --no-snap 硬跑（出事没有回滚点）：${e.message}`);
    else { console.error(`写前快照失败，本次不写（快照是写操作最后的回滚保险）：${e.message}\n  确认不需要回滚再硬跑：加 --no-snap`); process.exit(4); }
  }
}

/* ---- 取数组：dataPath 支持 a.b.c，空则自动找 ---- */
function pickArray(json) {
  const p = cfg.dataPath;
  if (p) {
    let cur = json;
    for (const seg of p.split('.')) { if (cur == null) break; cur = cur[seg]; }
    if (Array.isArray(cur)) return cur;
  }
  const walk = (o, d = 0) => {
    if (!o || typeof o !== 'object' || d > 3) return null;
    for (const v of Object.values(o)) {
      if (Array.isArray(v) && v.length && typeof v[0] === 'object') return v;
      const g = walk(v, d + 1); if (g) return g;
    }
    return null;
  };
  return Array.isArray(json) ? json : (walk(json) || []);
}

const host = new URL(url).host;
/* 独立登录态：--profile 指 login.mjs 存好的那个 user-data-dir；--bg 屏幕外跑（无人值守） */
const profile = arg('profile', cfg.profile || '');
console.error('自检：数据归属=自己的后台｜权限=账号内可见｜频率=人工级（一次一请求）｜平台协议=你确认过吗（不确定就先问，别默认可以）');
await ensureChrome({ port, mode: flag('bg') ? 'bg' : 'watch', profile: profile || undefined });
const list = await (await fetch(`http://127.0.0.1:${port}/json/list`)).json();
let page = list.find(t => t.type === 'page' && String(t.url || '').includes(host));
if (!page) {
  const r = await fetch(`http://127.0.0.1:${port}/json/new?${encodeURIComponent('https://' + host + '/')}`, { method: 'PUT' });
  page = await r.json();
  await sleep(2000);
}
const cdp = await Cdp.attach({ port, urlPart: host });
await cdp.enableSession();

const expr = `(async () => {
  try {
    const opt = { method: ${JSON.stringify(method)}, credentials: 'include'
      ${cfg.request.headers && Object.keys(cfg.request.headers).length ? `, headers: ${JSON.stringify(cfg.request.headers)}` : ''}
      ${body ? `, body: ${JSON.stringify(body)}` : ''} };
    const r = await fetch(${JSON.stringify(url)}, opt);
    const t = await r.text();
    return JSON.stringify({ ok: true, status: r.status, body: t.slice(0, 2000000) });
  } catch (e) { return JSON.stringify({ ok: false, err: String(e && e.message || e) }); }
})()`;

const raw = await cdp.evalJs(expr, { awaitPromise: true }).catch(e => JSON.stringify({ ok: false, err: String(e.message || e) }));
cdp.close();
let res; try { res = typeof raw === 'string' ? JSON.parse(raw) : raw; } catch { res = { ok: false, err: '响应不可解析' }; }
if (!res.ok) { console.error(`请求失败：${res.err}`); await done(3); }
if (res.status < 200 || res.status >= 300) { console.error(`HTTP ${res.status}（登录态失效或参数不对）`); await done(3); }

let json; try { json = JSON.parse(res.body); } catch { console.error('返回不是 JSON'); await done(3); }
const rows = pickArray(json);
const fields = (cfg.fields && cfg.fields.length ? cfg.fields : (rows[0] ? Object.keys(rows[0]) : []));

/* ---- 校验：行数 + 必需字段 + 字段数（少字段 = 静默少数据） ---- */
const minRows = Number(cfg.校验?.minRows ?? 1);
const need = cfg.校验?.requiredFields || [];
const expectFields = Number(cfg.校验?.fieldCount ?? 0);
const problems = [];
if (rows.length < minRows) problems.push(`行数 ${rows.length} < 期望 ${minRows}`);
for (const f of need) if (rows[0] && rows[0][f] == null) problems.push(`必需字段缺失：${f}`);
if (expectFields > 0 && rows[0]) {
  const got = Object.keys(rows[0]).length;
  if (got !== expectFields) {
    if (flag('allow-fields')) console.warn(`⚠️ 字段数 ${got} ≠ 期望 ${expectFields}（--allow-fields 本次放行；确认接口是不是改版了）`);
    else problems.push(`字段数 ${got} ≠ 期望 ${expectFields}（配置字段 ${(cfg.fields || []).length} 个；少字段就是少数据，确认无误加 --allow-fields）`);
  }
}

if (problems.length) {
  console.error('校验不过：' + problems.join('；'));
  await done(2);
}

console.log(`接口：${method} ${host}${u.pathname}`);
console.log(`参数：${JSON.stringify(params)}`);
console.log(`返回：${rows.length} 行 × ${fields.length} 字段（校验通过）`);

/* ---- 输出 ---- */
const out = arg('out');
const lines = [fields.join(',')];
for (const r of rows) lines.push(fields.map(f => {
  const v = r[f] == null ? '' : String(r[f]);
  return /[",\n]/.test(v) ? '"' + v.replace(/"/g, '""') + '"' : v;
}).join(','));
const csv = lines.join('\r\n');

if (!flag('go') || !out) {
  console.log('\n—— 预览（前 5 行）——');
  for (const l of lines.slice(0, 6)) console.log(l);
  if (!out) console.log('\n（没给 --out，只预览不落盘）');
  else console.log('\n（预览模式：加 --go 才写文件）');
} else {
  fs.mkdirSync(path.dirname(path.resolve(out)), { recursive: true });
  fs.writeFileSync(path.resolve(out), '\uFEFF' + csv, 'utf8');
  console.log(`\n已写出：${path.resolve(out)}（${rows.length} 行）`);
}

await done(0);
