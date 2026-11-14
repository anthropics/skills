/* run_multitab_test.mjs — 多标签录制回归：A 页点按钮 → 新开 B 标签 → B 跳转到 C → 停止
 * 断言：三个页面的动作都进同一条录制、序号连续唯一、meta.tabs ≥ 2
 * 跑法：node test/run_multitab_test.mjs     （需要本机 Chrome；端口 18991，profile 在 os.tmpdir()）
 */
import path from 'node:path';
import fs from 'node:fs';
import os from 'node:os';
import { spawn } from 'node:child_process';
import http from 'node:http';
import { fileURLToPath } from 'node:url';
import { ensureChrome, Cdp, sleep, closeChromeByPort } from '../scripts/lib-cdp.mjs';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const PORT = 18991;
const TMP = path.join(os.tmpdir(), 'sf_multitab_' + Date.now());
let pass = 0, fail = 0;
const ok = (cond, msg) => { if (cond) { pass++; } else { fail++; console.log('  ✗ ' + msg); } };

fs.mkdirSync(TMP, { recursive: true });
const page = (title, id) => `<!doctype html><meta charset="utf-8"><title>${title}</title>` +
  `<h3>${title}</h3><button id="${id}">${id}</button><a id="lnk_${id}" href="#" onclick="return false">${id}链接</a>`;
fs.writeFileSync(path.join(TMP, 'a.html'), page('A页', 'a1'), 'utf8');
fs.writeFileSync(path.join(TMP, 'b.html'), page('B页', 'b1'), 'utf8');
fs.writeFileSync(path.join(TMP, 'c.html'), page('C页', 'c1'), 'utf8');

/* 用本地 http 起页面：file:// 在新标签里会卡在 readyState=loading（documentElement 一直 null），
   浮标挂不上——2026-11-10 实测的坑，所以回归用 http，和真实业务页面一致 */
const HTTP_PORT = 18997;
const html = {
  'a.html': page('A页', 'a1'),
  'b.html': page('B页', 'b1'),
  'c.html': page('C页', 'c1')
};
const server = http.createServer((req, res) => {
  const key = String(req.url || '').replace(/^\//, '').split('?')[0];
  const body = html[key];
  res.writeHead(body ? 200 : 404, { 'content-type': 'text/html; charset=utf-8' });
  res.end(body || 'not found');
});
await new Promise(r => server.listen(HTTP_PORT, '127.0.0.1', r));
const U = f => `http://127.0.0.1:${HTTP_PORT}/${f}`;

const listPages = async () => (await (await fetch(`http://127.0.0.1:${PORT}/json/list`)).json()).filter(t => t.type === 'page');
/* 新开标签必须切到前台：后台标签 Chrome 会推迟解析（readyState 一直 loading、documentElement 为 null），
   真实场景用户点链接出来的标签是前台，这里用 /json/activate 还原 */
const newTab = async (u) => {
  const r = await fetch(`http://127.0.0.1:${PORT}/json/new?${encodeURIComponent(u)}`, { method: 'PUT' });
  const t = await r.json();
  try { await fetch(`http://127.0.0.1:${PORT}/json/activate/${t.id}`); } catch { /* ignore */ }
  await sleep(900);
};
const hudText = `(function(){var h=document.getElementById('__sop_hud_host');return h&&h.shadowRoot?h.shadowRoot.getElementById('st').textContent:'(无浮标)'})()`;
const hudClick = id => `(function(){var h=document.getElementById('__sop_hud_host');if(!h||!h.shadowRoot)return 'no-hud';var b=h.shadowRoot.getElementById('${id}');if(!b)return 'no-btn';b.click();return 'ok'})()`;

async function attach(urlPart) {
  const c = await Cdp.attach({ port: PORT, urlPart });
  await c.enableSession();
  return c;
}
async function waitHud(urlPart, label) {
  for (let i = 0; i < 30; i++) {
    try {
      const c = await attach(urlPart);
      const t = await c.evalJs(hudText, { awaitPromise: false });
      c.close();
      // 状态文案：待机… / 正在录制… / 已暂停… / 已停止…（录起来后新标签直接是「正在录制」）
      if (typeof t === 'string' && /待机|正在录制|已暂停|已停止/.test(t)) return true;
    } catch { /* 还没注入 */ }
    await sleep(500);
  }
  try {
    const c = await attach(urlPart);
    const d = await c.evalJs(`(function(){var h=document.getElementById('__sop_hud_host');return {href:location.href.slice(-14),rs:document.readyState,de:!!document.documentElement,sop:!!window.__SOP,host:!!h}})()`, { awaitPromise: false });
    console.log(`  (${label} 没浮标：${JSON.stringify(d)})`);
    c.close();
  } catch (e) { console.log(`  (${label} 没浮标且连不上：${String(e.message).slice(0, 60)})`); }
  return false;
}

let child = null;
try {
  await ensureChrome({ port: PORT, profile: path.join(TMP, 'profile'), mode: 'bg' });
  await newTab(U('a.html'));

  child = spawn(process.execPath, [path.join(ROOT, 'scripts', 'record.mjs'),
    '--port', String(PORT), '--name', '_mt', '--minutes', '2', '--keep-open'
  ], { cwd: ROOT, env: { ...process.env, KEEP_BROWSER: '1' }, stdio: ['ignore', 'pipe', 'pipe'] });
  const log = [];
  child.stdout.on('data', b => log.push(String(b)));
  child.stderr.on('data', b => log.push(String(b)));

  // A 页浮标就位 → 点「开始录制」
  ok(await waitHud('a.html', 'A'), 'A 页应该自动挂上浮标');
  let cA = await attach('a.html');
  ok((await cA.evalJs(hudClick('bstop'), { awaitPromise: false })) === 'ok', 'A 页「开始录制」应可点');
  await sleep(600);
  await cA.evalJs(`document.getElementById('a1').click()`, { awaitPromise: false });
  cA.close();
  await sleep(900);

  // 新开 B 标签（模拟「点 A 里的按钮弹新页」）→ 应自动接入并继续录
  await newTab(U('b.html'));
  ok(await waitHud('b.html', 'B'), '新开的 B 标签应该自动挂上浮标');
  let cB = await attach('b.html');
  await cB.evalJs(`document.getElementById('b1').click()`, { awaitPromise: false });
  await sleep(700);

  // B 在同一标签里跳到 C（换页丢 recorder，驱动应重新注入并继续）
  await cB.send('Page.navigate', { url: U('c.html') });
  cB.close();
  await sleep(1200);
  ok(await waitHud('c.html', 'C'), 'C 页（同标签跳转）应该重新注入浮标');
  const cC = await attach('c.html');
  await cC.evalJs(`document.getElementById('c1').click()`, { awaitPromise: false });
  await sleep(700);
  ok((await cC.evalJs(hudClick('bstop'), { awaitPromise: false })) === 'ok', 'C 页「停止录制」应可点');
  cC.close();

  // 等子进程收尾存盘
  const t0 = Date.now();
  while (child.exitCode === null && Date.now() - t0 < 40000) await sleep(500);
  ok(child.exitCode === 0, `record.mjs 应正常退出（实际 ${child.exitCode}）\n    日志：${log.join('').slice(-600)}`);

  const recDir = path.join(ROOT, 'recordings');
  const files = fs.readdirSync(recDir).filter(f => f.startsWith('_mt_') && f.endsWith('.rec.json'))
    .sort((a, b) => fs.statSync(path.join(recDir, b)).mtimeMs - fs.statSync(path.join(recDir, a)).mtimeMs);
  ok(files.length > 0, '应该产出录制文件');
  if (!files.length) throw new Error('没有录制文件，后续断言跳过');
  const rec = JSON.parse(fs.readFileSync(path.join(recDir, files[0]), 'utf8'));
  const pages = rec.actions.map(a => String(a.page || ''));
  const labels = rec.actions.map(a => String(a.label || a.text || ''));
  const seqs = rec.actions.map(a => a.seq);

  ok(rec.meta.counts.tabs >= 2, `meta.tabs 应 ≥2（实际 ${rec.meta.counts.tabs}）`);
  ok(pages.some(p => p.includes('a.html')), 'A 页动作应进录制');
  ok(pages.some(p => p.includes('b.html')), 'B 页（新标签）动作应进录制');
  ok(pages.some(p => p.includes('c.html')), 'C 页（跳转后）动作应进录制');
  ok(labels.some(l => l.includes('a1')) && labels.some(l => l.includes('b1')) && labels.some(l => l.includes('c1')),
    `三个页面的按钮都应该被录到（实际 ${JSON.stringify(labels.slice(0, 12))}）`);
  ok(JSON.stringify(seqs) === JSON.stringify([...Array(seqs.length)].map((_, i) => i + 1)),
    `序号应连续唯一 1..${seqs.length}（实际 ${JSON.stringify(seqs)}）`);

  for (const f of files) fs.unlinkSync(path.join(recDir, f));
} catch (e) {
  fail++; console.log('  ✗ 异常：' + (e && e.message));
} finally {
  try { if (child && child.exitCode === null) child.kill(); } catch { /* ignore */ }
  closeChromeByPort(PORT);
  await sleep(500);
  try { server.close(); } catch { /* ignore */ }
  try { fs.rmSync(TMP, { recursive: true, force: true }); } catch { /* ignore */ }
}

console.log(`\nmultitab test：${pass} 过 / ${fail} 挂`);
process.exit(fail ? 1 : 0);
