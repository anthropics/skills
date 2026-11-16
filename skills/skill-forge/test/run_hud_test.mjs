/* run_hud_test.mjs — 页面内浮标（HUD）真机回归：起一台 headless Chrome，注入录制器，真点两下
 * 验四件事：① 浮标出现并显示链路名 ② 点击/填写后计数与日志有反应 ③ 点浮标自己不会被录进去
 *          ④ 点「结束」后 hudState.stop=true（驱动侧据此收尾）
 * 找不到 Chrome / 端口占用 → 打印 SKIP 并以 0 退出（不阻塞其它测试）
 * 跑法：node test/run_hud_test.mjs [端口，默认 18898]
 */
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { ensureChrome, Cdp, closeChromeByPort, sleep } from '../scripts/lib-cdp.mjs';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const PORT = Number(process.argv[2] || 18898);
let pass = 0, fail = 0;
const ok = (cond, msg, extra = '') => {
  if (cond) { pass++; console.log(`✓ ${msg}`); }
  else { fail++; console.log(`✗ ${msg}${extra ? ' | ' + extra : ''}`); }
};

const pageUrl = pathToFileURL(path.join(ROOT, 'test/_fixture/hud_page.html')).href;
let cdp = null;
try {
  await ensureChrome({ port: PORT, mode: 'bg', profile: path.join(os.tmpdir(), 'sf_hud_profile') });
  cdp = await Cdp.attach({ port: PORT });
  await cdp.enableSession();
  await cdp.send('Page.navigate', { url: pageUrl });
  await sleep(1200);
} catch (e) {
  console.log(`SKIP：起浏览器失败（${String(e.message).slice(0, 80)}）`);
  process.exit(0);
}

const ev = async (expr) => cdp.evalJs(expr);
const shoot = async (name) => {
  if (process.env.SF_NO_SHOT) return;   // 出包验收时别往包里写截图（包里不该有证据）
  try {
    const shot = await cdp.send('Page.captureScreenshot', { format: 'png' });
    const out = path.join(ROOT, 'evidence', name);
    fs.mkdirSync(path.dirname(out), { recursive: true });
    fs.writeFileSync(out, Buffer.from(shot.data, 'base64'));
    console.log(`  截图：${out}`);
  } catch { /* 截图失败不影响断言 */ }
};


try {
  // 1) 注入 → 应停在待机（不点「开始录制」不许开录）
  await cdp.injectFile(path.join(ROOT, 'assets', 'recorder.js'));
  await ev(`__SOP_hudSet(${JSON.stringify({ name: '浮标测试链路', actions: 0, net: 0 })})`);
  await sleep(300);

  const hudTitle = await ev(`(function(){var h=document.getElementById('__sop_hud_host');if(!h||!h.shadowRoot)return '';return h.shadowRoot.getElementById('ttl').textContent})()`);
  ok(/浮标测试链路/.test(hudTitle || ''), '浮标出现并带链路名', hudTitle);

  const stIdle = await ev(`(function(){var h=document.getElementById('__sop_hud_host');return h.shadowRoot.getElementById('st').textContent})()`);
  ok(/待机/.test(stIdle || ''), '注入后是待机态（不自动开录）', stIdle);
  const btnIdle = await ev(`(function(){var h=document.getElementById('__sop_hud_host');return h.shadowRoot.getElementById('bstop').textContent})()`);
  ok(btnIdle === '开始录制', '待机时大按钮写着「开始录制」', btnIdle);
  const nIdle = await ev(`JSON.parse(__SOP_hudState()).armed`);
  ok(nIdle === false, '待机时 armed=false（驱动不会自己开录）');

  // 1.5) 点「开始录制」→ 按钮变「停止录制」，状态变录制中
  await ev(`(function(){var h=document.getElementById('__sop_hud_host');h.shadowRoot.getElementById('bstop').click()})()`);
  await sleep(250);
  const btnRec = await ev(`(function(){var h=document.getElementById('__sop_hud_host');return h.shadowRoot.getElementById('bstop').textContent})()`);
  ok(btnRec === '停止录制', '点「开始录制」后按钮变「停止录制」', btnRec);
  const st0 = await ev(`(function(){var h=document.getElementById('__sop_hud_host');return h.shadowRoot.getElementById('st').textContent})()`);
  ok(/正在录制/.test(st0 || ''), '状态显示「正在录制」', st0);
  ok((await ev(`JSON.parse(__SOP_hudState()).armed`)) === true, '开录后 armed=true');

  // 2) 真操作：点按钮、填输入框
  await ev(`document.getElementById('btn1').click()`);
  await ev(`(function(){var i=document.getElementById('d');i.value='2026-11-06';i.dispatchEvent(new Event('change',{bubbles:true}))})()`);
  await sleep(400);

  const cnt1 = await ev(`(function(){var h=document.getElementById('__sop_hud_host');return h.shadowRoot.getElementById('cnt').textContent})()`);
  ok(/点击 1/.test(cnt1 || ''), '计数区显示点击 1', cnt1);
  ok(/填充 1/.test(cnt1 || ''), '计数区显示填充 1', cnt1);

  // 2.6) 复制内容：默认记原文；--no-copy-text 时只记结构（评审关注点）
  const fireCopy = `(function(){
    var d=document.getElementById('cp')||document.createElement('div');
    d.id='cp'; d.textContent='账户'+String.fromCharCode(9)+'消耗'+String.fromCharCode(10)+'A001'+String.fromCharCode(9)+'1234.56';
    document.body.appendChild(d);
    var r=document.createRange(); r.selectNodeContents(d);
    var s=window.getSelection(); s.removeAllRanges(); s.addRange(r);
    document.dispatchEvent(new ClipboardEvent('copy',{bubbles:true}));
  })()`;
  await ev(fireCopy);
  await sleep(250);
  const dumpA = JSON.parse(await ev('__SOP_dump()'));
  const cA = (dumpA.actions || []).filter(a => a.type === 'copy').pop();
  ok(!!cA && /1234\.56/.test(cA.value || ''), '复制：默认记原文（粘贴能复现）', String(cA && cA.value).slice(0, 40));

  await ev('window.__SOP_CFG = { redactCopy: true }');
  await ev(fireCopy);
  await sleep(250);
  const dumpB = JSON.parse(await ev('__SOP_dump()'));
  const cB = (dumpB.actions || []).filter(a => a.type === 'copy').pop();
  ok(!!cB && cB.redacted === true && !cB.value && Number(cB.chars) > 0, '复制：--no-copy-text 不留原文，只记结构', JSON.stringify(cB || {}).slice(0, 120));

  const logLines = await ev(`(function(){var h=document.getElementById('__sop_hud_host');return h.shadowRoot.getElementById('log').children.length})()`);
  ok(Number(logLines) >= 2, '日志区有记录行', String(logLines));

  // 2.2) 元素快照：改版后能回答「当时那个按钮长什么样」
  const a0 = await ev(`(function(){var d=JSON.parse(__SOP_dump());return d.actions[0]||null})()`);
  const snap = a0 && a0.locator && a0.locator.snapshot;
  ok(!!snap && typeof snap.html === 'string' && snap.html.length > 0 && snap.html.length <= 300, '录到的元素带快照（html ≤300 字）', JSON.stringify(snap && snap.html ? snap.html.slice(0, 60) : snap));
  ok(!!snap && /BUTTON|button/i.test(String(snap.tag || '')) && typeof snap.role === 'string' && typeof snap.name === 'string', '快照里有 tag/role/name', JSON.stringify(snap && { tag: snap.tag, role: snap.role, name: snap.name }));

  await shoot('hud_录制中.png');

  // 2.5) 备注：浮标里写「这步干什么 / 规则」→ 挂到最近一步的 note 上（后面读节点意义就靠它）
  const nBeforeNote = await ev(`JSON.parse(__SOP_hudState()).actions`);
  await ev(`(function(){var h=document.getElementById('__sop_hud_host');var i=h.shadowRoot.getElementById('notein');i.value='只拉当天的数据';h.shadowRoot.getElementById('bnote').click()})()`);
  await sleep(300);
  const acts1 = await ev(`JSON.parse(__SOP_dump()).actions`);
  const lastAct = acts1[acts1.length - 1];
  ok(!!lastAct && /只拉当天的数据/.test(lastAct.note || ''), '备注挂到最后一步（action.note）', JSON.stringify(lastAct && lastAct.note));
  const cntNote = await ev(`(function(){var h=document.getElementById('__sop_hud_host');return h.shadowRoot.getElementById('cnt').textContent})()`);
  ok(/备注 1/.test(cntNote || ''), '计数区显示备注 1', cntNote);
  const nAfterNote = await ev(`JSON.parse(__SOP_hudState()).actions`);
  ok(Number(nAfterNote) === Number(nBeforeNote), '写备注不算一次录制动作', `${nBeforeNote} → ${nAfterNote}`);

  // 2.7) 撤销上一步：误点自救
  const nBeforeUndo = await ev(`JSON.parse(__SOP_hudState()).actions`);
  await ev(`(function(){var h=document.getElementById('__sop_hud_host');h.shadowRoot.getElementById('bundo').click()})()`);
  await sleep(200);
  const nAfterUndo = await ev(`JSON.parse(__SOP_hudState()).actions`);
  ok(Number(nAfterUndo) === Number(nBeforeUndo) - 1, '点「撤销上一步」动作数 -1', `${nBeforeUndo} → ${nAfterUndo}`);
  ok((await ev(`JSON.parse(__SOP_hudState()).stop`)) !== true, '撤销不会把会话结束掉');

  const nBefore = await ev(`JSON.parse(__SOP_hudState()).actions`);

  // 3) 点浮标上的按钮：不能被录进去
  await ev(`(function(){var h=document.getElementById('__sop_hud_host');h.shadowRoot.getElementById('btoggle').click()})()`);
  await sleep(300);
  const nAfterToggle = await ev(`JSON.parse(__SOP_hudState()).actions`);
  ok(Number(nAfterToggle) === Number(nBefore), '点浮标「暂停」不产生录制动作', `${nBefore} → ${nAfterToggle}`);
  const paused = await ev(`JSON.parse(__SOP_hudState()).paused`);
  ok(paused === true, '点「暂停」后状态位 paused=true');
  const ttlPaused = await ev(`(function(){var h=document.getElementById('__sop_hud_host');return h.shadowRoot.getElementById('ttl').textContent})()`);
  ok(/已暂停/.test(ttlPaused || ''), '暂停后标题变「已暂停」', ttlPaused);
  await shoot('hud_已暂停.png');

  // 截图留证（录制中）

  // 4) 点「停止录制」→ 驱动侧能感知
  await ev(`(function(){var h=document.getElementById('__sop_hud_host');h.shadowRoot.getElementById('bstop').click()})()`);
  await sleep(200);
  const st1 = await ev(`JSON.parse(__SOP_hudState()).stop`);
  ok(st1 === true, '点「停止录制」后 hudState.stop=true（驱动侧据此存盘收尾）');
  const nAfterStop = await ev(`JSON.parse(__SOP_hudState()).actions`);
  ok(Number(nAfterStop) === Number(nBefore), '点「停止录制」也不产生录制动作', `${nBefore} → ${nAfterStop}`);
} finally {
  try { cdp.close(); } catch { /* ignore */ }
  closeChromeByPort(PORT, { log: () => {} });
}

console.log(`\nhud test：${pass} 过 / ${fail} 挂`);
process.exit(fail ? 1 : 0);
