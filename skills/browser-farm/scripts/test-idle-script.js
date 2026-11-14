// 空闲豁免验收：FARM_IDLE_MIN=1 下，脚本运行中的档不被空闲停杀；脚本停后恢复照杀。
// 跑法: node test-idle-script.js   （全程约 4 分钟，别开别的档位）
'use strict';
const http = require('http');
const fs = require('fs');
const path = require('path');
const { spawn } = require('child_process');
const TMP = path.join(__dirname, 'test-home3');
process.env.FARM_HOME = TMP;

const S_PORT = 9313;    // 测试总管口
const BASE = 9542;      // 测试档位端口段
const PAGE_PORT = 9883; // 测试页面服务器

// 页面只有表（盯表脚本盯它），值永远 150，阈值 99999 永不达标 → 脚本一直跑
const PAGE = `<!doctype html><html><head><meta charset="utf-8"><title>idle-test</title></head><body>
<table border="1"><thead><tr><th>计划</th><th>消费</th><th>操作</th></tr></thead>
<tbody><tr><td>计划A</td><td id="spA">150.00</td><td><button id="pause1">暂停</button></td></tr></tbody></table>
</body></html>`;

let pass = 0, total = 0;
function ok(name, cond, extra) {
  total += 1;
  if (cond) { pass += 1; console.log('  ✓ ' + total + ' ' + name); }
  else console.log('  ✗ ' + total + ' ' + name + (extra !== undefined ? '  实际=' + JSON.stringify(extra).slice(0, 160) : ''));
}
const sleep = ms => new Promise(r => setTimeout(r, ms));
const stamp = () => new Date().toISOString().slice(11, 19);

function api(method, p, body) {
  return new Promise((resolve, reject) => {
    const data = body ? JSON.stringify(body) : null;
    const req = http.request({ host: '127.0.0.1', port: S_PORT, path: p, method, headers: data ? { 'Content-Type': 'application/json' } : {} }, res => {
      let d = '';
      res.on('data', c => d += c);
      res.on('end', () => { try { resolve(JSON.parse(d)); } catch (e) { reject(new Error('非 JSON: ' + d.slice(0, 200))); } });
    });
    req.on('error', reject);
    if (data) req.write(data);
    req.end();
  });
}
const aliveOf = async id => (await api('GET', '/slots')).slots.find(s => s.id === id).alive;

let pageServer, sup;
async function cleanup() {
  try {
    const r = await api('GET', '/slots');
    for (const s of (r.slots || [])) { try { await api('POST', '/slot/' + s.id + '/stop', {}); } catch (e) {} }
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
    env: { ...process.env, FARM_HOME: TMP, FARM_PORT: String(S_PORT), FARM_BASE_PORT: String(BASE), FARM_IDLE_MIN: '1' },
    stdio: ['ignore', 'pipe', 'pipe'], windowsHide: true,
  });
  sup.stdout.on('data', () => {}); sup.stderr.on('data', d => process.stderr.write('[总管] ' + d));
  let up = false;
  for (let i = 0; i < 40 && !up; i++) { await sleep(300); try { await api('GET', '/health'); up = true; } catch (e) {} }
  ok('总管就绪(空闲停=1分钟)', up);

  let r = await api('POST', '/slots/add', { note: '豁免验收档' });
  ok('登记档位01', r.ok && r.slot.port === BASE, r);
  r = await api('POST', '/slot/01/start', {});
  ok('档位01无窗口启动', r.ok, r);
  r = await api('POST', '/slot/01/open', { url: 'http://127.0.0.1:' + PAGE_PORT + '/page' });
  ok('开页', r.ok && !!r.targetId, r);

  // 盯表脚本：10 秒查一次，阈值 99999 永不达标 → 一直跑
  const sc = { id: '80', name: '永跑盯表', type: 'watch', clickJitter: 0.4,
    watch: { mode: 'cell', rowText: '计划A', columnHeader: '消费', op: '>=', value: 99999, clickText: '暂停', intervalMs: 10000, cooldownMs: 3000 } };
  process.env.FARM_HOME = TMP;
  const scripter = require('./scripter.js');
  scripter.saveScript(sc);
  r = await api('POST', '/script/80/start', { slot: '01' });
  ok('盯表脚本起跑', r.ok && r.state === 'running', r);

  // ===== 110 秒完全不发 /slot/01/* 请求（轮询 /slots 和脚本 status 都不算活动）=====
  console.log('[' + stamp() + '] 开始 110 秒放置（只看不动）…');
  let survived = true;
  for (let i = 0; i < 11; i++) {
    await sleep(10000);
    const a = await aliveOf('01');
    const st = await api('GET', '/script/80/status');
    console.log('[' + stamp() + '] ' + (i + 1) * 10 + 's: 档位 alive=' + a + '，脚本 ' + st.state);
    if (!a) { survived = false; break; }
  }
  ok('脚本运行中 110 秒不被空闲停杀（无豁免 60~90s 就死）', survived);

  // ===== 停脚本 → 豁免解除 → 空闲停恢复照杀 =====
  r = await api('POST', '/script/80/stop', {});
  ok('停止指令受理', r.ok && r.state === 'stopping', r);
  let done = null;
  for (let i = 0; i < 20 && !done; i++) { await sleep(500); done = await api('GET', '/script/80/status'); if (done.state !== 'done') done = null; }
  ok('脚本真停了', done && done.state === 'done' && done.result && done.result.hits === 0, done);
  console.log('[' + stamp() + '] 脚本已停，放 80 秒看档位被空闲停收走…');
  let killed = false;
  for (let i = 0; i < 8; i++) {
    await sleep(10000);
    const a = await aliveOf('01');
    console.log('[' + stamp() + '] 停脚本后 ' + (i + 1) * 10 + 's: alive=' + a);
    if (!a) { killed = true; break; }
  }
  ok('停脚本后档位被空闲停收走（豁免解除）', killed);

  const logTxt = fs.existsSync(path.join(TMP, 'farm.log')) ? fs.readFileSync(path.join(TMP, 'farm.log'), 'utf8') : '';
  ok('farm.log 有空闲自动停记录', /空闲.*自动停/.test(logTxt), logTxt.slice(-200));

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
