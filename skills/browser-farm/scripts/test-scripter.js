// 离线验收（脚本器合并进农场）：本地页面 + 真 Chrome + 总管后台任务，不碰外网。
// 跑法: node test-scripter.js   全绿打印 N/N 断言过
'use strict';
const http = require('http');
const fs = require('fs');
const path = require('path');
const { spawn, execSync } = require('child_process');
const TMP = path.join(__dirname, 'test-home2');
process.env.FARM_HOME = TMP; // 必须在 require 前设：脚本目录走沙盒
const scripter = require('./scripter.js');

const S_PORT = 9312;    // 测试总管口
const BASE = 9541;      // 测试档位端口段
const PAGE_PORT = 9882; // 测试页面服务器

const PAGE = `<!doctype html><html><head><meta charset="utf-8"><title>ws-test</title></head><body>
<button id="b1">刷新</button> <button id="b2">筛选</button> <button id="b3">导出</button>
<button data-name="无ID按钮">无ID按钮</button>
<table border="1"><thead><tr><th>计划</th><th>消费</th><th>状态</th><th>操作</th></tr></thead>
<tbody>
<tr id="r1"><td>计划A</td><td id="spA">150.00</td><td>投放中</td><td><button id="pause1">暂停</button></td></tr>
<tr id="r2"><td>计划B</td><td>120.00</td><td>投放中</td><td><button id="pause2">暂停</button></td></tr>
</tbody></table>
<script>
window.__clicks = [];
document.addEventListener('click', function(e){
  var el = e.target, up = 0;
  while (el.parentElement && el.tagName !== 'BUTTON' && up < 3) { el = el.parentElement; up++; }
  var r = el.getBoundingClientRect();
  window.__clicks.push({ n: el.id || el.getAttribute('data-name') || el.innerText.trim(), x: e.clientX, y: e.clientY,
    rx: r.left, ry: r.top, rw: r.width, rh: r.height });
}, true);
</script></body></html>`;

let pass = 0, total = 0;
function ok(name, cond, extra) {
  total += 1;
  if (cond) { pass += 1; console.log('  ✓ ' + total + ' ' + name); }
  else console.log('  ✗ ' + total + ' ' + name + (extra !== undefined ? '  实际=' + JSON.stringify(extra).slice(0, 160) : ''));
}
const sleep = ms => new Promise(r => setTimeout(r, ms));

function api(method, p, body) {
  return new Promise((resolve, reject) => {
    const data = body ? JSON.stringify(body) : null;
    const req = http.request({ host: '127.0.0.1', port: S_PORT, path: p, method, timeout: 120000, headers: data ? { 'Content-Type': 'application/json' } : {} }, res => {
      let d = '';
      res.on('data', c => d += c);
      res.on('end', () => { try { resolve(JSON.parse(d)); } catch (e) { reject(new Error('非 JSON: ' + d.slice(0, 200))); } });
    });
    req.on('error', reject);
    req.on('timeout', () => req.destroy(new Error('api 超时（2 分钟）'))); // Node24 默认只给 5 秒，停机等主进程退完会超——显式放宽
    if (data) req.write(data);
    req.end();
  });
}
async function waitScript(id, pred, ms) {
  const end = Date.now() + (ms || 20000);
  let last;
  while (Date.now() < end) {
    await sleep(400);
    try { last = await api('GET', '/script/' + id + '/status'); if (pred(last)) return last; } catch (e) { last = { error: e.message }; }
  }
  return last;
}
const evalSlot = code => api('POST', '/slot/01/eval', { code });

let pageServer, sup;
async function cleanup() {
  try {
    const r = await api('GET', '/slots');
    for (const s of (r.slots || [])) { try { await api('POST', '/slot/' + s.id + '/halt', {}); } catch (e) {} } // halt 连脚本带档停，防看护在收尾间隙又拉起档留下僵尸 Chrome
  } catch (e) {}
  if (sup) { try { sup.kill(); } catch (e) {} }
  if (pageServer) { try { pageServer.close(); } catch (e) {} }
  await sleep(1500);
}

(async () => {
  fs.rmSync(TMP, { recursive: true, force: true });
  pageServer = http.createServer((req, res) => {
    res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8' });
    res.end(PAGE);
  });
  await new Promise(r => pageServer.listen(PAGE_PORT, '127.0.0.1', r));
  sup = spawn(process.execPath, [path.join(__dirname, 'supervisor.js')], {
    env: { ...process.env, FARM_HOME: TMP, FARM_PORT: String(S_PORT), FARM_BASE_PORT: String(BASE) },
    stdio: ['ignore', 'pipe', 'pipe'], windowsHide: true,
  });
  sup.stdout.on('data', () => {}); sup.stderr.on('data', d => process.stderr.write('[总管] ' + d));
  let up = false;
  for (let i = 0; i < 40 && !up; i++) { await sleep(300); try { await api('GET', '/health'); up = true; } catch (e) {} }
  ok('总管就绪', up);

  let r = await api('POST', '/slots/add', { note: '脚本档' });
  ok('登记档位01 端口' + BASE, r.ok && r.slot.port === BASE, r);
  r = await api('POST', '/slot/01/start', {});
  ok('档位01无窗口启动', r.ok, r);
  r = await api('POST', '/slot/01/open', { url: 'http://127.0.0.1:' + PAGE_PORT + '/page' });
  ok('开页', r.ok && !!r.targetId, r);

  // ===== 录制（引擎直连档位口，合成真事件点 3 个按钮） =====
  const steps = [];
  const port = BASE;
  const rec = await scripter.recordSession(port, (st, n) => steps.push(st));
  const pageCdp = await scripter.attachPage(port);
  for (const id of ['b1', 'b2', 'b3']) {
    const c = await (async () => {
      const ev = await pageCdp.send('Runtime.evaluate', { expression: `(function(){var r=document.getElementById(${JSON.stringify(id)}).getBoundingClientRect();return {x:Math.round(r.left+r.width/2),y:Math.round(r.top+r.height/2)};})()`, returnByValue: true });
      return ev.result.value;
    })();
    await scripter.humanClick(pageCdp, c);
    await sleep(250);
  }
  await sleep(400);
  rec.stop();
  ok('录制收 3 步', steps.length === 3, steps.map(s => s.selector));
  ok('选择器命中 id', steps.map(s => s.selector).join('|') === '#b1|#b2|#b3', steps.map(s => s.selector));
  pageCdp.close();

  const sc01 = { id: '01', name: '测试路径', type: 'loop', steps: steps.map(s => ({ selector: s.selector, text: s.text, tag: s.tag })), loop: 0, delayMs: 100, jitterMs: 50, clickJitter: 0.4, created: new Date().toISOString() };
  ok('脚本01落盘', fs.existsSync(scripter.saveScript(sc01)));

  // ===== 后台跑 2 轮（先清录制阶段点出的账） =====
  await evalSlot('window.__clicks = []');
  r = await api('POST', '/script/01/start', { slot: '01', loop: 2 });
  ok('后台任务起跑', r.ok && r.state === 'running', r);
  r = await waitScript('01', s => s.state === 'done' || s.state === 'error');
  ok('2轮跑完', r.state === 'done' && r.result.rounds === 2 && r.result.clicks === 6, r);
  const clicks = (await evalSlot('window.__clicks')).result;
  ok('顺序不乱', clicks.map(c => c.n).join(',') === 'b1,b2,b3,b1,b2,b3', clicks.map(c => c.n));
  ok('点击全落在按钮内', clicks.every(c => c.x >= c.rx + 1 && c.x <= c.rx + c.rw - 1 && c.y >= c.ry + 1 && c.y <= c.ry + c.rh - 1));
  const b1s = clicks.filter(c => c.n === 'b1');
  ok('同按钮坐标不同（随机偏移）', b1s.some(c => c.x !== b1s[0].x || c.y !== b1s[0].y), b1s);

  // ===== text= 选择器 =====
  await evalSlot('window.__clicks = []');
  scripter.saveScript({ ...sc01, id: '02', name: '无id按钮', steps: [{ selector: 'text=无ID按钮', text: '无ID按钮', tag: 'BUTTON' }] });
  await api('POST', '/script/02/start', { slot: '01', loop: 1 });
  r = await waitScript('02', s => s.state === 'done');
  const tc = (await evalSlot('window.__clicks')).result;
  ok('text=选择器点中无id按钮', r.state === 'done' && tc.length === 1 && tc[0].n === '无ID按钮', { r, tc });

  // ===== 找不到元素 → 任务 error 带原因 =====
  scripter.saveScript({ ...sc01, id: '03', name: '坏脚本', steps: [{ selector: '#buCunZai', text: '不存在的', tag: 'BUTTON' }] });
  await api('POST', '/script/03/start', { slot: '01', loop: 1 });
  r = await waitScript('03', s => s.state === 'error' || s.state === 'done');
  ok('找不到元素任务报error', r.state === 'error' && /找不到/.test(r.error || ''), r);

  // ===== 自动开页（v0.1.15）：停档模拟关机重开 → 不手动开档直接启脚本，档位自己拉起、录制页自己开回来点 =====
  const PAGE_URL = 'http://127.0.0.1:' + PAGE_PORT + '/page';
  scripter.saveScript({ ...sc01, id: '04', name: '自动开页', steps: sc01.steps.map(s => ({ ...s, href: PAGE_URL })) });
  await api('POST', '/slot/01/stop', {});
  r = await api('POST', '/script/04/start', { slot: '01', loop: 1 }); // 档位是死的：全靠脚本启动链自己恢复
  ok('停档后直接启脚本（档位自动拉起）', r.ok && r.state === 'running', r);
  r = await waitScript('04', s => s.state === 'done' || s.state === 'error', 30000);
  ok('自动开回录制页并点完 1 轮', r.state === 'done' && r.result.rounds === 1 && r.result.clicks === 3, r);
  const c4 = (await evalSlot('window.__clicks')).result;
  ok('自动开页点的还是录的那三个按钮', c4.map(x => x.n).join(',') === 'b1,b2,b3', c4.map(x => x.n));
  const pages04 = (await scripter.jget(BASE, '/json/list', 2500)).filter(t => t.type === 'page');
  ok('录制页真开着（带 ? 参数也算同一页）', pages04.some(t => scripter.samePage(t.url, PAGE_URL + '?from=test')), pages04.map(t => t.url));

  // ===== 抓包跟新开页面（v0.1.19）：抓包开着的档位新开 tab，1.5 秒内轮询器自动挂上，接口不漏 =====
  r = await api('POST', '/slot/01/sniff', { action: 'start' });
  ok('抓包开启', r.ok && r.sniffing === true, r);
  await api('POST', '/slot/01/open', { url: 'http://127.0.0.1:' + PAGE_PORT + '/page2' });
  await sleep(2200); // 等轮询器一拍把新页挂上（1.5s 一拍）
  await evalSlot("fetch('/probe-new-tab-api').catch(function(){}); return 1");
  await sleep(700);
  r = await api('POST', '/slot/01/sniff', { action: 'stop' });
  ok('新开页面的接口也抓到了', r.ok && (r.requests || []).some(x => x.url.includes('probe-new-tab-api')), (r.requests || []).map(x => x.url).slice(0, 5));

  // ===== 档位重启存活（v0.1.16）：跑着的时候重启档位（=GUI 点启动/后台跑那套先停再起），脚本不断，等档回来开回页面接着跑完 =====
  scripter.saveScript({ ...sc01, id: '05', name: '重启存活', steps: sc01.steps.map(s => ({ ...s, href: PAGE_URL })), delayMs: 400, jitterMs: 100 });
  await api('POST', '/slot/01/stop', {}); // 干净起点：档位死的，全靠脚本启动链自己拉起
  r = await api('POST', '/script/05/start', { slot: '01', loop: 3 });
  ok('重启存活脚本起跑', r.ok && r.state === 'running', r);
  await sleep(1500); // 正跑着第 1 轮
  await api('POST', '/slot/01/restart', {}); // 断它：先停再起，页面全关——以前这下手里的脚本就 error 了
  r = await waitScript('05', s => s.state === 'done' || s.state === 'error', 60000);
  ok('档位重启脚本活着跑完 3 轮', r.state === 'done' && r.result.rounds === 3 && r.result.clicks === 9, r);
  const c5 = (await evalSlot('window.__clicks')).result;
  ok('重启后接着点的还是录的那三个按钮', c5.length >= 3 && c5.every(x => ['b1', 'b2', 'b3'].includes(x.n)), c5.map(x => x.n));

  // ===== 看护拉回 + halt 真停（v0.1.16）：档被硬停（=整个浏览器死了），跑着的脚本引总管看护自动拉回档接着跑；halt 连脚本带档一起真停 =====
  scripter.saveScript({ ...sc01, id: '06', name: '看护拉回', steps: sc01.steps.map(s => ({ ...s, href: PAGE_URL })), delayMs: 100, jitterMs: 50 });
  await api('POST', '/slot/01/stop', {}); // 干净起点：档位死的，全靠脚本启动链自己拉起
  r = await api('POST', '/script/06/start', { slot: '01' });
  ok('看护脚本起跑', r.ok && r.state === 'running', r);
  r = await waitScript('06', s => s.state === 'running' && /第1轮/.test(s.lastMsg || ''), 30000);
  ok('看护脚本真点上了第 1 轮', r.state === 'running', r);
  await api('POST', '/slot/01/stop', {}); // 硬停浏览器、脚本不停：脚本掉进重连窗（=「网页全关了/浏览器死了」的实况）
  let alive06 = false;
  for (let i = 0; i < 45 && !alive06; i++) { await sleep(1000); try { alive06 = !!(await api('GET', '/slot/01')).alive; } catch (e) {} }
  r = await api('GET', '/script/06/status');
  ok('档死了看护自动拉回，脚本还活着', alive06 === true && r.state === 'running', { alive06, state: r.state, lastMsg: r.lastMsg });
  r = await api('POST', '/slot/01/halt', {});
  ok('halt 连脚本带档受理', r.ok && r.stoppedScripts >= 1, r);
  r = await waitScript('06', s => s.state === 'done' || s.state === 'error', 30000);
  ok('halt 后脚本真收住', r.state === 'done', r);
  await api('POST', '/slot/01/start', {}); // halt 把档和测试页都带走了：夹具重建，给后面盯表测试
  await api('POST', '/slot/01/open', { url: PAGE_URL });

  // ===== newscript（v0.1.17）：agent 写的步骤 json 交上来，校验落盘自动编号，跟人录的同待遇 =====
  const countBefore = (await api('GET', '/scripts')).scripts.length;
  r = await api('POST', '/script/new', { name: 'agent写的', loop: 1, delayMs: 50, jitterMs: 20, clickJitter: 0.4,
    steps: [{ selector: '#b2', text: '乙', tag: 'BUTTON', href: PAGE_URL }] });
  ok('newscript 收下落盘自动编号', r.ok && /^\d+$/.test(r.id) && fs.existsSync(path.join(TMP, 'scripts', r.file)), r);
  const newId = r.id; // start 响应里叫 scriptId 不叫 id，编号先存住
  r = await api('POST', '/script/' + newId + '/start', { slot: '01' });
  r = await waitScript(newId, s => s.state === 'done' || s.state === 'error', 30000);
  ok('agent 脚本跑完 1 轮（自动开页+点中）', r.state === 'done' && r.result && r.result.clicks === 1, r);
  let rBad = await api('POST', '/script/new', { name: '没selector', steps: [{ tag: 'BUTTON' }] });
  ok('步骤没 selector/text 当场拒收', rBad.ok === false && /selector/.test(rBad.error || ''), rBad);
  rBad = await api('POST', '/script/new', { name: '空步骤', steps: [] });
  ok('空 steps 拒收且没落盘', rBad.ok === false && /steps/.test(rBad.error || '')
    && (await api('GET', '/scripts')).scripts.length === countBefore + 1, rBad);

  // ===== 绑定档位（v0.1.19）：newscript 带 bindSlot，启动不带 slot 就用绑定的档 =====
  const rBindNew = await api('POST', '/script/new', { name: '绑定脚本', loop: 1, delayMs: 50, jitterMs: 20,
    steps: sc01.steps, bindSlot: '01', desc: '探绑定用的' });
  ok('newscript 带 bindSlot+desc 落盘', rBindNew.ok && rBindNew.id, rBindNew);
  const boundList = (await api('GET', '/scripts')).scripts.find(s => s.id === rBindNew.id);
  ok('落盘的脚本带绑定和说明', boundList && boundList.bindSlot === '01' && boundList.desc === '探绑定用的', boundList);
  await evalSlot('window.__clicks = []');
  r = await api('POST', '/script/' + rBindNew.id + '/start', { loop: 1 }); // 故意不带 slot：走绑定
  ok('没给档位走绑定的档起跑', r.ok && r.state === 'running' && r.slotId === '01', r);
  r = await waitScript(rBindNew.id, s => s.state === 'done' || s.state === 'error', 30000);
  ok('绑定脚本在绑的档上跑完', r.state === 'done' && r.result && r.result.clicks === 3, r);

  // ===== 配置导出/导入（v0.1.16）：一份 json 搬走档位登记+全部脚本，另一台电脑导入即用 =====
  r = await api('GET', '/config/export');
  ok('导出配置带档位和脚本', r.ok && r.payload.farm === 'browser-farm' && r.payload.slots.length >= 1 && r.payload.scripts.length >= 6
    && r.payload.scripts.every(s => s.steps || s.watch),
    r.payload && { slots: r.payload.slots.length, scripts: r.payload.scripts.length });
  const beforeCount = (await api('GET', '/scripts')).scripts.length;
  const imp = await api('POST', '/config/import', r.payload); // 原样导回自己：编号全占→全改号，端口全占→跳过
  ok('原样导回：档位跳过、脚本自动改号不覆盖', imp.ok && imp.addedSlots === 0 && imp.skippedSlots === 1
    && imp.addedScripts === beforeCount && imp.renamedScripts === beforeCount, imp);
  const afterCount = (await api('GET', '/scripts')).scripts.length;
  ok('导入后脚本翻倍且都读得出来', afterCount === beforeCount * 2, { beforeCount, afterCount });

  // ===== watch：未达标不点 =====
  const watchSc = { id: '90', name: '消费300停计划A', type: 'watch', clickJitter: 0.4,
    watch: { mode: 'cell', rowText: '计划A', columnHeader: '消费', op: '>=', value: 300, clickText: '暂停', intervalMs: 400, cooldownMs: 300 } };
  scripter.saveScript(watchSc);
  await evalSlot('window.__clicks = []');
  await api('POST', '/script/90/start', { slot: '01', once: true, timeoutMs: 2500 });
  r = await waitScript('90', s => s.state === 'done');
  let wc = (await evalSlot('window.__clicks')).result;
  ok('未达标不点（超时退出）', r.result.hits === 0 && r.result.timeout === true && wc.length === 0, { r, wc });

  // ===== watch：达标只点该行 =====
  await evalSlot('document.getElementById("spA").textContent = "356.20"');
  await api('POST', '/script/90/start', { slot: '01', once: true });
  r = await waitScript('90', s => s.state === 'done');
  wc = (await evalSlot('window.__clicks')).result;
  ok('达标点中A行暂停', r.result.hits === 1 && wc.some(c => c.n === 'pause1'), { r, wc });
  ok('只点A行（B行没动）', !wc.some(c => c.n === 'pause2'), wc);

  // ===== watch：回落再涨二次触发 + stopscript 真能停 =====
  await evalSlot('window.__clicks = []; document.getElementById("spA").textContent = "150.00"');
  await sleep(200);
  r = await api('POST', '/script/90/start', { slot: '01' });
  ok('常驻盯表起跑', r.ok && r.state === 'running', r);
  await sleep(1500); await evalSlot('document.getElementById("spA").textContent = "402.50"');   // 第1次
  await sleep(2500); await evalSlot('document.getElementById("spA").textContent = "150.00"');   // 回落重新武装
  await sleep(1500); await evalSlot('document.getElementById("spA").textContent = "411.00"');   // 第2次
  await sleep(1500);
  r = await api('POST', '/script/90/stop', {});
  ok('停止指令受理', r.ok && r.state === 'stopping', r);
  r = await waitScript('90', s => s.state === 'done');
  wc = (await evalSlot('window.__clicks')).result;
  ok('回落再涨二次触发后停住', r.state === 'done' && r.result.hits === 2 && wc.filter(c => c.n === 'pause1').length === 2, { r, n: wc.length });

  // ===== CLI 冒烟 =====
  const cli = execSync('node farm.js scripts', {
    cwd: __dirname, encoding: 'utf8',
    env: { ...process.env, FARM_HOME: TMP, FARM_PORT: String(S_PORT), FARM_BASE_PORT: String(BASE) },
  });
  ok('CLI scripts 可见 01/90', cli.includes('01') && cli.includes('数据触发') && cli.includes('90'), cli.slice(0, 120));

  // ===== 存 Agent 笔记（录制收工的另一条出口：不建脚本，落 md 给 agent 读） =====
  const NOTE_DIR = path.join(TMP, 'agent-notes');
  const noteSteps = [
    { selector: '#b1', text: '刷新', tag: 'BUTTON', href: 'http://127.0.0.1:9882/x' },
    { selector: null, text: '无ID按钮', tag: 'BUTTON', href: null },
  ];
  const noteApis = [
    { url: 'https://h/api/list', method: 'POST', status: 200, count: 7, tsUTC: '00:00:01', postData: null },
    { url: 'https://h/api/who', method: 'GET', status: 403, count: 1, tsUTC: '00:00:02', postData: null },
  ];
  const n1 = scripter.saveAgentNote(NOTE_DIR, '巡检流程/日', { slotId: '01', note: '商城-主号' }, noteSteps, noteApis);
  const n2 = scripter.saveAgentNote(NOTE_DIR, '巡检流程/日', { slotId: '01' }, noteSteps, null); // 同名同秒：不覆盖
  const md1 = fs.readFileSync(n1, 'utf8');
  ok('Agent 笔记落盘且内容齐（步骤表/接口表/原始 JSON/用法说明）',
    md1.includes('# 录制笔记：巡检流程日') && md1.includes('| 1 | 刷新 | `#b1` | http://127.0.0.1:9882/x |')
    && md1.includes('POST | 200 | 7 | https://h/api/list') && md1.includes('"selector": "#b1"')
    && md1.includes('不是农场脚本，不会自动跑'),
    n1);
  ok('文件名消毒+同名同秒不覆盖', /[\\/:*?"<>|]/.test(path.basename(n1)) === false && n1 !== n2 && fs.existsSync(n2), { n1, n2 });

  // ===== 农场录制 → forge rec.json（桥的转换器：字段契约按 forge evidence.mjs 读取面） =====
  const fApi = [
    { url: 'https://h/api/list', method: 'POST', status: 200, count: 3, tsUTC: '00:00:05', postData: '{"wd":1}' },
    { url: 'https://h/api/who', method: 'GET', status: 403, count: 1, tsUTC: '00:00:06', postData: null },
  ];
  const frec = scripter.toForgeRec(noteSteps, fApi, '巡检流程/日', { slotId: '01' });
  const fa = frec.actions[0], fn = frec.network[0];
  ok('toForgeRec 契约齐（actions: seq/type/at/text/selector/locator/page；network: at/method/url/status/body；count 展开）',
    frec.actions.length === 2 && fa.seq === 1 && fa.type === 'click' && /^\d{2}:\d{2}:\d{2}$/.test(fa.at)
    && fa.text === '刷新' && fa.locator.best === '#b1' && fa.page === 'http://127.0.0.1:9882/x'
    && frec.network.length === 4 && fn.method === 'POST' && fn.status === 200 && fn.body === '{"wd":1}'
    && fn.url === 'https://h/api/list' && frec.meta.from === 'browser-farm 档01',
    { fa, fn });
  ok('动作铺在第一条接口前（时间线不倒挂）+轮询热度保留',
    frec.actions[1].at < frec.network.find(r => r.url.includes('list')).at
    && frec.network.filter(r => r.url.includes('list')).length === 3,
    { lastAct: frec.actions[1].at, firstNet: frec.network[0].at });

  await cleanup();
  fs.rmSync(TMP, { recursive: true, force: true });
  console.log('\n' + pass + '/' + total + ' 断言' + (pass === total ? '全过 ✓' : '有失败 ✗'));
  process.exit(pass === total ? 0 : 1);
})().catch(async e => {
  console.error('测试炸了: ' + (e && e.stack || e));
  await cleanup();
  fs.rmSync(TMP, { recursive: true, force: true });
  process.exit(1);
});
