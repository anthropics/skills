/* record.mjs — 录制会话驱动（多标签版）：起浏览器 → 你自己打开要录的网页 → 浮标挂在每个页面上 → 正常操作 → 收一条完整录制
 * 用法：
 *   node scripts/record.mjs [--url https://xxx] [--name 链路名] [--port 18801] [--minutes 15] [--keep-open] [--drop "3,4"] [--no-copy-text]
 *   --url 可以不写：不写就用你自己已经打开的那个网页（本脚本不拿空白页当录制现场）
 * 结束：浮标上点「停止录制」/ Ctrl+C / 到时 → recordings/<name>_<时间>.rec.json
 * 收尾（全局规则）：录完自动按端口关掉自己开的浏览器（`--keep-open` / KEEP_BROWSER=1 才留）
 *
 * 多标签/多页面（2026-11-10 起）：
 *   - 每个 http(s)/file 标签都单独接一条会话、各自注入 recorder.js；点 A 里的按钮 → 新开 B → B 里再跳 C，
 *     三段的动作全部进同一条录制，动作带 page 网址，收尾时按时间重排序并重新编号。
 *   - 标签关掉自动摘掉会话；剩下任何一个标签点「停止录制」都算收工。
 *   - about:blank / chrome:// 不接（避免把空白页和新标签页当业务页面）。
 */
import path from 'node:path';
import fs from 'node:fs';
import { execFileSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { ensureChrome, Cdp, watchDownloads, watchNetwork, sleep, closeChromeSmart } from './lib-cdp.mjs';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const arg = (k, d) => {
  const i = process.argv.indexOf('--' + k);
  return i >= 0 ? process.argv[i + 1] : d;
};
const flag = k => process.argv.includes('--' + k);
const url = arg('url', '');
const name = arg('name', 'link_' + new Date().toISOString().slice(0, 10).replace(/-/g, ''));
const port = Number(arg('port', '18801'));
const minutes = Number(arg('minutes', '15'));

const recorderPath = path.join(ROOT, 'assets', 'recorder.js');
const dlDir = path.join(ROOT, 'recordings', '_downloads', String(Date.now()));
const merged = new Map();   // key = tabId#injectedAt#seq → 动作（跨标签合并的全量动作流）
const noteSet = new Map();  // key = tabId#injectedAt#at#text → 口述备注
const tabOrder = [];        // 标签接入顺序（排序兜底用）
const tabs = new Map();     // targetId → { id, cdp, net, dl, url, title, injectedAt }

let sessionEnd = false;
let started = false;        // 用户点过「开始录制」才自动拉起新标签的录制（待机态不偷录）
process.on('SIGINT', () => { console.log('\n收到停止信号，正在收尾…'); sessionEnd = true; });

await ensureChrome({ port, mode: 'watch' });

const usableUrl = u => /^(https?|file):\/\//i.test(u || '');
async function listPages() {
  const r = await fetch(`http://127.0.0.1:${port}/json/list`);
  return (await r.json()).filter(t => t.type === 'page');
}
async function openUrl(u) {
  // 新版 Chrome 的 /json/new 只收 PUT（实测坑）
  await fetch(`http://127.0.0.1:${port}/json/new?${encodeURIComponent(u)}`, { method: 'PUT' });
}

let lastWarn = 0;
const warn = (msg) => {
  if (Date.now() - lastWarn > 5000) { console.warn(`  (${msg})`); lastWarn = Date.now(); }
};

/* 一个标签一条 CDP 会话：开 Page/Runtime/Network + 下载落到独立目录 */
async function addTab(t) {
  const c = new Cdp(t.webSocketDebuggerUrl, t);
  await c._open();
  await c.enableSession();
  await c.send('Browser.setDownloadBehavior', { behavior: 'allow', downloadPath: dlDir }).catch(() => {});
  const rec = { id: t.id, cdp: c, net: [], dl: null, url: t.url, title: t.title || '', injectedAt: 0 };
  rec.net = watchNetwork(c);
  rec.dl = watchDownloads(c, dlDir);
  c.on('Page.javascriptDialogOpening', () => { c.send('Page.handleJavaScriptDialog', { accept: true }).catch(() => {}); });
  tabs.set(t.id, rec);
  tabOrder.push(t.id);
  return rec;
}

/* 每轮同步：新标签接上、关掉的摘掉 */
async function syncTabs() {
  let pages = [];
  try { pages = await listPages(); } catch { return; }
  for (const t of pages) {
    const has = tabs.get(t.id);
    if (has) { has.url = t.url || has.url; has.title = t.title || has.title; continue; }
    if (!usableUrl(t.url)) continue;
    try { await addTab(t); console.log(`  ＋ 接入标签：${String(t.url).slice(0, 78)}`); } catch (e) { warn(`接入标签失败：${String(e.message || e).slice(0, 60)}`); }
  }
  for (const id of [...tabs.keys()]) {
    if (pages.find(t => t.id === id)) continue;
    try { tabs.get(id).cdp.close(); } catch { /* 已断 */ }
    tabs.delete(id);
    console.log('  － 标签已关闭');
  }
}

async function inject(rec) {
  try {
    await rec.cdp.injectFile(recorderPath);
    rec.injectedAt = Date.now();
  } catch (e) { warn(`注入失败：${String(e.message || e).slice(0, 80)}`); return; }
  const hud = { name, actions: merged.size };
  await rec.cdp.evalJs(`__SOP_hudSet && __SOP_hudSet(${JSON.stringify(hud)})`, { awaitPromise: false }).catch(() => {});
  if (flag('no-copy-text')) {
    await rec.cdp.evalJs('window.__SOP_CFG = Object.assign(window.__SOP_CFG || {}, { redactCopy: true })', { awaitPromise: false }).catch(() => {});
  }
  if (started) await rec.cdp.evalJs('__SOP_arm(true)', { awaitPromise: false }).catch(() => {});
}

/* 单个标签轮询：读动作/备注/浮标状态；丢了 recorder 就重新注入 */
async function pollTab(rec) {
  let state;
  try {
    state = await rec.cdp.evalJs(`(function () {
    try {
      if (!window.__SOP || !window.__SOP_start) return { missing: true, loading: document.readyState === 'loading' };
      // 注入早于 DOM 就绪时浮标挂不上：每轮自愈补挂，用户才看得到「开始录制」
      if (!document.getElementById('__sop_hud_host') && window.__SOP_hudSet) {
        try { __SOP_hudSet({ name: ${JSON.stringify(name)} }); } catch (e) { /* 页面不让挂就下轮再来 */ }
      }
      // 状态位是 S.on（不是 .recording）；写错会每轮清空已录动作
      if (window.__SOP.armed && !window.__SOP.on && !window.__SOP.pausedByUser && !window.__SOP.stopReq) { __SOP_start(); }
      var hud = window.__SOP_hudState ? JSON.parse(__SOP_hudState()) : null;
      return { dump: __SOP_dump(), hud: hud };
    } catch (e) { return { error: String(e) }; }
  })()`, { awaitPromise: false });
  } catch {
    // 整页跳转瞬间 evaluate 会失败/超时：当成丢了 recorder，下轮重新注入
    state = { missing: true };
  }
  if (!state || state.missing || state.error) {
    // 页面还在 loading（常见于后台新标签：Chrome 会推迟解析）→ 这轮先不注入，等它解析完
    if (state && state.loading) return;
    await inject(rec); return;
  }
  if (state.hud && state.hud.armed) started = true;
  if (state.hud && state.hud.stop) { console.log('\n用户在浮标上点了「停止录制」，开始保存…'); sessionEnd = true; return; }
  if (!state.dump) return;
  let d;
  try { d = JSON.parse(state.dump); } catch { return; }
  for (const a of d.actions || []) {
    const key = `${rec.id}#${d.injectedAt}#${a.seq}`;
    if (!merged.has(key)) {
      merged.set(key, { ...a, page: d.url, pageTitle: d.title, _tab: rec.id, _oseq: a.seq, _at: a.at || '' });
    }
  }
  // 口述备注：同一页多次轮询会重复读到，按 tab+注入批+时间+文本去重
  for (const n of d.notes || []) {
    noteSet.set(`${rec.id}#${d.injectedAt}#${n.at}#${n.text}`, { ...n, page: d.url, _tab: rec.id, _oseq: n.seq });
  }
  // 把权威计数推回浮标（跨页/跨 tab 都是总数，不是本页数）
  const status = state.hud && state.hud.on === false ? 'paused' : 'recording';
  await rec.cdp.evalJs(`__SOP_hudSet(${JSON.stringify({ actions: merged.size, status })})`, { awaitPromise: false }).catch(() => {});
}

/* 起手：给了 --url 就找到/打开它；没给就接用户已经打开的页面（不拿空白页当录制现场） */
if (url) {
  const hostPart = url.replace(/^https?:\/\//, '').split('/')[0];
  let t = (await listPages().catch(() => [])).find(p => (p.url || '').includes(hostPart));
  if (!t) { await openUrl(url); await sleep(1500); }
}
await syncTabs();

if (!tabs.size) {
  console.log('● 等你打开要录的网页（10 分钟内）：任何标签打开 http/https 页面，我都会自动接上并显示浮标');
  for (let i = 0; i < 600 && !tabs.size; i++) { await sleep(1000); await syncTabs(); }
  if (!tabs.size) {
    console.error('✗ 一直没等到可用页面（about:blank / chrome:// 不算），已退出');
    if (!flag('keep-open') && process.env.KEEP_BROWSER !== '1') await closeChromeSmart(port);
    process.exit(2);
  }
}

console.log(`● 录制中：正常操作浏览器即可（${minutes} 分钟后自动收，Ctrl+C 提前收）`);
console.log(`  已接标签 ${tabs.size} 个；之后新开的标签会自动接上、一起录`);
console.log(`  浮标待机中——在你自己的页面上点「开始录制」我才开始记`);

const t0 = Date.now();
while (!sessionEnd && Date.now() - t0 < minutes * 60000) {
  await syncTabs();
  for (const rec of [...tabs.values()]) {
    if (sessionEnd) break;
    await pollTab(rec).catch(() => { /* 单标签异常不影响其它标签 */ });
  }
  await sleep(400); // 400ms 一轮：跳页瞬间最多丢 0.4 秒内的动作
}

for (const rec of [...tabs.values()]) {
  try { await rec.cdp.evalJs('__SOP_stop()', { awaitPromise: false }); } catch { /* 页面可能已关 */ }
}

/* 跨标签合并 → 按真实时间重排序 → 统一编号（每个标签里都是从 1 开始编的，必须重编） */
const raw = [...merged.values()];
const tabIdx = new Map(tabOrder.map((id, i) => [id, i]));
raw.sort((x, y) =>
  String(x._at).localeCompare(String(y._at)) ||
  (tabIdx.get(x._tab) ?? 0) - (tabIdx.get(y._tab) ?? 0) ||
  x._oseq - y._oseq);

const seqMap = new Map(); // tabId#原seq → 新seq
const actions = raw.map((a, i) => {
  const s = i + 1;
  seqMap.set(`${a._tab}#${a._oseq}`, s);
  const { _tab, _oseq, _at, ...rest } = a;
  return { ...rest, seq: s };
});
const notes = [...noteSet.values()].map(n => {
  const s = seqMap.get(`${n._tab}#${n._oseq}`);
  const { _tab, _oseq, ...rest } = n;
  return { ...rest, seq: s ?? n.seq };
});
const downloads = [...tabs.values()].flatMap(r => r.dl?.files || []);
const netReqs = [...tabs.values()].flatMap(r => r.net || []);

/* 误点过滤：--drop "3,4" 直接剔除这几步（序号从 1 开始，按录制顺序） */
const dropArg = arg('drop', '');
const dropped = String(dropArg).split(',').map(s => Number(String(s).trim())).filter(n => n > 0);
let finalActions = actions;
if (dropped.length) {
  finalActions = actions.filter(a => !dropped.includes(a.seq));
  for (const d of dropped) {
    const victim = actions.find(a => a.seq === d);
    if (victim?.note) {
      const prev = [...finalActions].filter(a => a.seq < d).pop();
      if (prev) { prev.note = (prev.note ? prev.note + ' / ' : '') + victim.note; }
    }
  }
  console.log(`  已按 --drop 过滤 ${dropped.join(',')} 这几步`);
}

/* 可疑误点：同元素连点 ≥2 次 / 点击后立刻回到上一页 */
const suspects = [];
for (let i = 0; i < finalActions.length; i++) {
  const a = finalActions[i], p = finalActions[i - 1];
  if (!p) continue;
  const same = a.type === 'click' && p.type === 'click'
    && a.locator && p.locator && a.locator.best && a.locator.best === p.locator.best;
  const backNav = a.type === 'nav' && p.url && a.to && String(a.to).length && String(a.to) !== String(p.url) && String(p.url).startsWith(String(a.to).split('?')[0]);
  if (same) suspects.push({ seq: a.seq, why: `和第${p.seq}步点的是同一个元素（连点）` });
  else if (backNav) suspects.push({ seq: a.seq, why: `点完又退回上一页` });
}

const out = {
  meta: {
    name, url: url || '(用户自己打开的页面)', port, finishedAt: new Date().toISOString(),
    tabs: [...tabs.values()].map(r => ({ url: r.url, title: r.title })),
    copyText: flag('no-copy-text') ? 'redacted(只记行列数)' : 'recorded(最多 8000 字)',
    suspects,
    counts: {
      total: finalActions.length,
      notes: notes.length,
      tabs: tabs.size,
      paste: finalActions.filter(a => a.type === 'paste').length,
      copy: finalActions.filter(a => a.type === 'copy').length,
      download: finalActions.filter(a => a.type === 'download').length,
      click: finalActions.filter(a => a.type === 'click').length,
      fill: finalActions.filter(a => a.type === 'fill').length
    }
  },
  actions: finalActions,
  notes,
  downloads,
  network: netReqs
};

const outFile = path.join(ROOT, 'recordings', `${name}_${Date.now()}.rec.json`);
fs.mkdirSync(path.dirname(outFile), { recursive: true });
fs.writeFileSync(outFile, JSON.stringify(out, null, 1), 'utf8');
for (const rec of [...tabs.values()]) { try { rec.cdp.close(); } catch { /* 已断 */ } }

console.log(`\n✓ 录制完成 → ${outFile}`);
console.log(`  跨 ${out.meta.counts.tabs} 个标签、动作 ${out.meta.counts.total} 条（粘贴 ${out.meta.counts.paste} / 复制 ${out.meta.counts.copy} / 下载 ${out.meta.counts.download} / 点击 ${out.meta.counts.click}）`);
if (notes.length) {
  console.log(`  口述备注 ${notes.length} 条（interview 会自动带出来）：`);
  for (const n of notes.slice(0, 8)) console.log(`    · 第${n.seq}步后 ${n.text}`);
}

/* 每步清单：把用户在浮标里写的「这步干什么 / 规则」一起打出来——后面就不用一条条问了 */
if (finalActions.length) {
  console.log('\n=== 录制步骤（★=写了备注）===');
  for (const a of finalActions) {
    const what = a.text || a.label || (a.type === 'fill' ? `填写「${a.label || ''}」` : a.type);
    console.log(`  ${String(a.seq).padStart(2)}. [${a.type}] ${String(what).slice(0, 46)}${a.note ? '  ★ ' + a.note : ''}`);
  }
}

/* 误点过滤：可疑步列出来让用户拍板（agent 转述这句就行，不用用户自己找） */
if (suspects.length) {
  console.log('\n⚠️ 这几步看起来像误点：');
  for (const s of suspects) console.log(`  第${s.seq}步 —— ${s.why}`);
  console.log(`  要过滤：回我序号（如 ${suspects.map(s => s.seq).join(',')}），或自己跑 node scripts/manage.mjs drop --rec <上面那个文件> --seq "${suspects.map(s => s.seq).join(',')}"`);
} else if (finalActions.length) {
  console.log('\n没有发现明显误点（同元素连点 / 点了又退回）。');
}

/* 提效：同一条链路录第二遍时，自动 diff 出「哪些是变量、哪些写死」——不用人记着再敲一条命令 */
const recDir = path.join(ROOT, 'recordings');
const prevs = fs.readdirSync(recDir)
  .filter(f => f.endsWith('.rec.json') && f.startsWith(`${name}_`) && path.join(recDir, f) !== outFile)
  .sort();
if (prevs.length) {
  const prev = path.join(recDir, prevs[prevs.length - 1]);
  console.log(`\n发现同一条链路的上一份录制（${prevs[prevs.length - 1]}）→ 自动跑二次录制对比`);
  try {
    const r = execFileSync(process.execPath, [path.join(ROOT, 'scripts', 'diffrec.mjs'), '--a', outFile, '--b', prev, '--name', name], { cwd: ROOT, encoding: 'utf8', timeout: 120000 });
    console.log(r.trim().split('\n').map(l => '  ' + l).join('\n'));
    console.log('  ↑ 常量写死、变量参数化，来源是两份数据，不是猜。');
  } catch (e) {
    console.log(`  对比没跑成（不影响录制文件）：${String(e.message).slice(0, 200)}`);
  }
} else {
  console.log('\n下一步建议：同一操作**再录一遍**（同一个 --name），本脚本会自动 diff 出常量/变量；');
  console.log('  也可以先跑探查：node scripts/evidence.mjs --recording "<上面那个文件>"');
}

/* 收尾提醒：产物可能含页面数据，别留在磁盘上（评审要求「使用结束后的清理提醒」） */
console.log(`\n产物：recordings/${path.basename(outFile)}（可能含页面数据：账号/投放/金额）`);
console.log('  用完就清：node scripts/manage.mjs clean --days 0   （清 zip/recordings/evidence）');
console.log('  要留存：先加密（7z a -p -mhe=on），密码别和文件放一起');

/* 收尾：录完就把自己开的浏览器关掉（全局规则；要留着看就 --keep-open）
 * 农场档位（--port 指的农场口）自动识别、只连不关——档位归农场总管管，不越权杀 */
if (!flag('keep-open') && process.env.KEEP_BROWSER !== '1') {
  await closeChromeSmart(port);
} else {
  console.log(`  按 --keep-open 保留浏览器（port=${port}）；用完记得关`);
}
