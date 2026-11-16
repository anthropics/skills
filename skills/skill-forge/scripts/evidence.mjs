/* evidence.mjs — 录制产物 → 链路证据包（给 agent 看「人怎么走的」，并挑出可替代的接口）
 * 用法：
 *   node scripts/evidence.mjs --recording recordings/xxx.rec.json [--out evidence] [--name 链路名]
 * 产出：
 *   evidence/<名>_<时间>/证据包.md      ← agent 读这份判断更短路径
 *   evidence/<名>_<时间>/证据包.html    ← 人看
 *   evidence/<名>_<时间>/timeline.json  ← 机读（动作+请求按时间合并）
 *
 * 判断口径（写死在提示里，避免 agent 自由发挥）：
 *   - 响应里有字段 且 有行数（rows>0）→ 数据源强候选
 *   - URL/body 里出现 date|start|end|page|size|id 这类 → 可参数化
 *   - 状态非 2xx / 没有响应体 → 存疑，别当数据源
 */
import path from 'node:path';
import fs from 'node:fs';
import { fileURLToPath } from 'node:url';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const arg = (k, d) => { const i = process.argv.indexOf('--' + k); return i >= 0 ? process.argv[i + 1] : d; };

const recFile = arg('recording');
if (!recFile) { console.error('用法：node scripts/evidence.mjs --recording <rec.json> [--out evidence] [--name 名]'); process.exit(1); }
const rec = JSON.parse(fs.readFileSync(recFile, 'utf8'));
const name = arg('name') || rec.meta?.name || path.basename(recFile, '.rec.json');
const outRoot = path.resolve(ROOT, arg('out', 'evidence'));
const stamp = new Date().toISOString().slice(0, 19).replace(/[-:T]/g, '');
const outDir = path.join(outRoot, `${name}_${stamp}`);
fs.mkdirSync(outDir, { recursive: true });

const actions = (rec.actions || []).map(a => ({ ...a, at: a.at || 0 }));
const requests = (rec.network || []).map(r => ({ ...r }));

/* 时间戳有两种形态：录制器给 "HH:MM:SS"，探查/接口给 ISO 串——统一换成秒再算差值 */
const SEC = v => {
  if (v == null || v === '') return NaN;
  if (typeof v === 'number') return v / 1000;
  const t = String(v);
  const m = t.match(/^(\d{2}):(\d{2}):(\d{2})$/);
  if (m) return (+m[1]) * 3600 + (+m[2]) * 60 + (+m[3]);
  const p = Date.parse(t);
  return isNaN(p) ? NaN : Math.round(p / 1000);
};

const all = [
  ...actions.map(a => ({ kind: 'act', at: a.at, a })),
  ...requests.map(r => ({ kind: 'req', at: r.at, r }))
].sort((x, y) => SEC(x.at) - SEC(y.at));

const t0 = all.length ? SEC(all[0].at) : SEC(Date.now());
const fmt = v => {
  const s1 = SEC(v == null ? (all.length ? all[0].at : Date.now()) : v);
  if (!isFinite(s1) || !isFinite(t0)) return '—';
  const d = Math.round(s1 - t0);
  const sign = d < 0 ? '-' : '';
  const a = Math.abs(d);
  return `${sign}${String(Math.floor(a / 60)).padStart(2, '0')}:${String(a % 60).padStart(2, '0')}`;
};
const esc = s => String(s ?? '').replace(/\|/g, '\\|').replace(/\r?\n/g, ' ⏎ ').slice(0, 160);
const host = u => { try { return new URL(u).host; } catch { return ''; } };
const short = u => { try { const x = new URL(u); return x.pathname + (x.search ? x.search.slice(0, 90) : ''); } catch { return String(u || '').slice(0, 110); } };

/* ---------- 一、动作时间线 ---------- */
const actRows = actions.map((a, i) => {
  const loc = a.locator?.best || a.locator?.L4_text || a.selector || '';
  const detail = a.type === 'paste' ? `贴 ${a.rows || '?'} 行 × ${a.cols || '?'} 列`
    : a.type === 'fill' ? `填「${esc(a.value)}」`
      : a.type === 'download' ? `下载 ${esc(a.filename || '')}`
        : a.type === 'copy' ? `复制「${esc(String(a.value || '').slice(0, 40))}」`
          : `点「${esc(a.text || '')}」`;
  return `| ${i + 1} | ${fmt(a.at)} | ${a.type} | ${esc(detail)} | ${esc(host(a.page || a.url || ''))} | \`${esc(loc)}\` | ${esc(a.note || '')} |`;
}).join('\n');

/* ---------- 二、页面轨迹 ---------- */
const trail = [];
for (const a of actions) {
  const u = a.page || a.url;
  if (u && trail[trail.length - 1] !== u) trail.push(u);
}

/* ---------- 三、接口候选 ---------- */
const scored = requests.map(r => {
  let score = 0; const why = [];
  if (r.status >= 200 && r.status < 300) { score += 2; why.push('2xx'); }
  if (r.fields?.length) { score += 3; why.push(`返回 ${r.fields.length} 字段`); }
  if (r.rows) { score += 3; why.push(`${r.rows} 行数据`); }
  if (/date|start|end|page|size|limit|id=|month|day/i.test(r.url + ' ' + (r.body || ''))) { score += 2; why.push('含可参数化字段'); }
  if (/export|download|report|list|query|detail|data/i.test(r.url)) { score += 1; why.push('URL 像取数'); }
  if (/\.js|\.css|\.png|\.jpg|\.svg|\.woff/i.test(r.url)) score -= 4;
  return { ...r, score, why };
}).sort((a, b) => b.score - a.score);

const apiRows = scored.slice(0, 30).map((r, i) => {
  const f = r.fields?.length ? r.fields.slice(0, 12).join(', ') + (r.fields.length > 12 ? ' …' : '') : '—';
  return `| ${i + 1} | ${r.score} | ${r.method} | ${r.status ?? '—'} | ${r.ms != null ? r.ms + 'ms' : '—'} | ${esc(host(r.url))} | \`${esc(short(r.url))}\` | ${r.rows ?? '—'} | ${esc(f)} |`;
}).join('\n');

const top = scored.filter(r => r.score >= 6).slice(0, 5);
const probeList = top.length
  ? top.map((r, i) => `${i + 1}. \`${r.method} ${short(r.url)}\` — 状态 ${r.status}，返回 ${r.fields?.length || 0} 字段 / ${r.rows ?? '?'} 行；入参：\`${esc(r.body || '(无 body)').slice(0, 120)}\``).join('\n')
  : '（本次录制没抓到像数据源的 XHR/Fetch：可能是服务端渲染，或数据在页面 HTML 里 → 走 UI 路径或换判据）';

const md = `# 链路证据包：${name}

- 录制文件：\`${path.basename(recFile)}\`
- 生成时间：${new Date().toLocaleString('zh-CN')}
- 时长：${fmt(all.length ? all[all.length - 1].at : t0)}；动作 ${actions.length} 条；XHR/Fetch ${requests.length} 条
- 起止：${rec.meta?.url || '—'}

> 这份是**给 agent 看的证据**，不是重放脚本。目标是据此判断：这条链路有没有更短的走法（直接调接口 / 少点几步 / 换入口）。

## 一、人是怎么走的

| # | 时刻 | 动作 | 具体 | 页面 | 定位 | 这步干什么 / 规则 |
|---|---|---|---|---|---|---|
${actRows || '| — | — | — | 本次没录到动作 | — | — |'}

## 二、页面跳转轨迹

${trail.length ? trail.map((u, i) => `${i + 1}. \`${esc(u)}\``).join('\n') : '（没有跨页）'}

## 三、接口候选（按「像不像数据源」排）

| # | 分 | 方法 | 状态 | 耗时 | Host | 路径 | 行数 | 返回字段 |
|---|---|---|---|---|---|---|---|---|
${apiRows || '| — | — | 本次没有 XHR/Fetch | — | — | — | — | — |'}

判据：2xx +2｜有返回字段 +3｜有行数 +3｜含 date/page 等可参数化字段 +2｜URL 像取数 +1｜静态资源 −4。**≥6 分才值得探。**

## 四、下一步探查清单（给 agent）

${probeList}

探的时候按这个顺序判：
1. 用已登录的浏览器上下文复现该请求（同源带 cookie），确认能拿到**同样的字段和行数**；
2. 逐个删参数试最小参数集（只留日期/账户/分页这类必需项）；
3. 得出结论三选一：**能接口化** / **只能 UI 自动化** / **需要额外鉴权（说清缺什么）**；
4. 结论先给用户确认，再生成技能包。
`;

fs.writeFileSync(path.join(outDir, '证据包.md'), md, 'utf8');

/* ---------- HTML（人看，一屏能扫完） ---------- */
const html = `<!doctype html><html lang="zh-CN"><meta charset="utf-8"><title>链路证据包 · ${esc(name)}</title>
<style>
body{font:14px/1.6 -apple-system,"Microsoft YaHei",sans-serif;margin:0;background:#f5f6f8;color:#1a1a1a}
.wrap{max-width:1180px;margin:0 auto;padding:24px}
h1{font-size:20px;margin:0 0 4px}h2{font-size:15px;margin:26px 0 10px;padding-left:9px;border-left:4px solid #2f6feb}
.meta{color:#667;font-size:12px;margin-bottom:6px}
.card{background:#fff;border:1px solid #e6e8ee;border-radius:10px;padding:14px 16px;margin-bottom:14px}
table{width:100%;border-collapse:collapse;font-size:12.5px}
th,td{padding:6px 8px;border-bottom:1px solid #eef0f4;text-align:left;vertical-align:top}
th{background:#fafbfd;font-weight:600;color:#445}
code{background:#f1f3f7;padding:1px 4px;border-radius:3px;font-size:11.5px;word-break:break-all}
.badge{display:inline-block;padding:0 6px;border-radius:9px;font-size:11px;background:#e8f0fe;color:#2f6feb}
.hot{background:#fff8e6}
ul{padding-left:20px;margin:6px 0}
</style><div class="wrap">
<h1>链路证据包 · ${esc(name)}</h1>
<div class="meta">动作 ${actions.length} 条 · XHR/Fetch ${requests.length} 条 · 时长 ${fmt(all.length ? all[all.length - 1].at : t0)} · 起点 <code>${esc(rec.meta?.url || '—')}</code></div>
<div class="card"><b>怎么用</b>：agent 先看「接口候选」，再去浏览器复现高分请求；确认能接口化就按接口生成技能，否则退回 UI 自动化。</div>
<h2>一、人是怎么走的</h2><div class="card"><table><tr><th>#</th><th>时刻</th><th>动作</th><th>具体</th><th>页面</th><th>定位</th><th>这步干什么 / 规则</th></tr>${actions.map((a, i) => {
  const loc = a.locator?.best || a.locator?.L4_text || '';
  const detail = a.type === 'paste' ? `贴 ${a.rows || '?'}×${a.cols || '?'}` : a.type === 'fill' ? `填「${esc(a.value)}」` : a.type === 'download' ? `下载 ${esc(a.filename || '')}` : `点「${esc(a.text || '')}」`;
  return `<tr><td>${i + 1}</td><td>${fmt(a.at)}</td><td>${a.type}</td><td>${esc(detail)}</td><td>${esc(host(a.page || a.url || ''))}</td><td><code>${esc(loc)}</code></td><td>${a.note ? '★ ' + esc(a.note) : ''}</td></tr>`;
}).join('') || '<tr><td colspan="7">本次没录到动作</td></tr>'}</table></div>
<h2>二、页面轨迹</h2><div class="card">${trail.map(u => `<div><code>${esc(u)}</code></div>`).join('') || '（没有跨页）'}</div>
<h2>三、接口候选</h2><div class="card"><table><tr><th>#</th><th>分</th><th>方法</th><th>状态</th><th>耗时</th><th>路径</th><th>行</th><th>字段</th></tr>${scored.slice(0, 30).map((r, i) => `<tr class="${r.score >= 6 ? 'hot' : ''}"><td>${i + 1}</td><td><b>${r.score}</b></td><td>${r.method}</td><td>${r.status ?? '—'}</td><td>${r.ms ?? '—'}</td><td><code>${esc(short(r.url))}</code></td><td>${r.rows ?? '—'}</td><td>${esc((r.fields || []).slice(0, 8).join(', '))}</td></tr>`).join('') || '<tr><td colspan="8">本次没有 XHR/Fetch</td></tr>'}</table></div>
<h2>四、下一步探什么</h2><div class="card"><ul>${top.map(r => `<li><code>${r.method} ${esc(short(r.url))}</code> — ${r.status}，${r.fields?.length || 0} 字段 / ${r.rows ?? '?'} 行</li>`).join('') || '<li>没抓到像数据源的接口</li>'}</ul></div>
</div></html>`;
fs.writeFileSync(path.join(outDir, '证据包.html'), html, 'utf8');

fs.writeFileSync(path.join(outDir, 'timeline.json'), JSON.stringify({
  name, source: path.basename(recFile), generatedAt: new Date().toISOString(),
  counts: { actions: actions.length, requests: requests.length },
  trail, timeline: all, apiCandidates: scored.slice(0, 30)
}, null, 1), 'utf8');

console.log(`✓ 证据包 → ${outDir}`);
console.log(`  动作 ${actions.length} 条 · 请求 ${requests.length} 条 · 轨迹 ${trail.length} 段`);
const good = scored.filter(r => r.score >= 6);
console.log(`  接口候选（≥6 分）${good.length} 条${good.length ? '：' : '（没抓到像数据源的请求）'}`);
for (const r of good.slice(0, 5)) console.log(`    [${r.score}] ${r.method} ${short(r.url)} → ${r.fields?.length || 0} 字段 / ${r.rows ?? '?'} 行`);
console.log(`  下一步：node scripts/probe.mjs --recording "${recFile}" --out "${outDir}"`);
