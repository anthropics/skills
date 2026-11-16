// 离线验收：起本地页面服务器 + 总管 + 真实 Chrome，不碰外网。
// 跑法: node test-farm.js   （全绿打印 N/N 断言过，任何一条红即退出码 1）
'use strict';
const http = require('http');
const fs = require('fs');
const path = require('path');
const os = require('os');
const { spawn, execSync } = require('child_process');

const ROOT = __dirname;
const HOME = path.join(ROOT, 'test-home');
const S_PORT = 9311;        // 测试总管口
const BASE = 9531;          // 测试档位端口段
const PAGE_PORT = 9877;     // 测试页面服务器
const PAGE_URL = 'http://127.0.0.1:' + PAGE_PORT + '/page';

// 1x1 红色 PNG
const PNG = Buffer.from('iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR42mP8z8BQDwAEhQGAhKmMIQAAAABJRU5ErkJggg==', 'base64');

let pass = 0, total = 0;
function ok(name, cond, extra) {
  total += 1;
  if (cond) { pass += 1; console.log('  ✓ ' + total + ' ' + name); }
  else { console.log('  ✗ ' + total + ' ' + name + (extra !== undefined ? '  实际=' + JSON.stringify(extra) : '')); }
}

function api(method, p, body, port) {
  return new Promise((resolve, reject) => {
    const data = body ? JSON.stringify(body) : null;
    const req = http.request({ host: '127.0.0.1', port: port || S_PORT, path: p, method, timeout: 120000, headers: data ? { 'Content-Type': 'application/json' } : {} }, res => {
      let d = '';
      res.on('data', c => d += c);
      res.on('end', () => { try { resolve(JSON.parse(d)); } catch (e) { reject(new Error('非 JSON: ' + d.slice(0, 200))); } });
    });
    req.on('error', reject);
    req.on('timeout', () => req.destroy(new Error('api 超时（2 分钟）'))); // Node24 默认只给 5 秒，停机等主进程退完/快照拷盘都会超——显式放宽
    if (data) req.write(data);
    req.end();
  });
}

async function waitReady() {
  for (let i = 0; i < 40; i++) {
    await new Promise(r => setTimeout(r, 300));
    try { await api('GET', '/health'); return; } catch (e) {}
  }
  throw new Error('测试总管 40 秒起不来');
}

// 轮询 eval 直到断言过或超时（页面加载是异步的）
async function waitEval(id, code, pred, ms) {
  const end = Date.now() + (ms || 12000);
  let last;
  while (Date.now() < end) {
    try {
      const r = await api('POST', '/slot/' + id + '/eval', { code });
      last = r;
      if (r.ok && pred(r.result)) return r;
    } catch (e) { last = { ok: false, error: e.message }; }
    await new Promise(r => setTimeout(r, 500));
  }
  return last;
}

function rmHome() { fs.rmSync(HOME, { recursive: true, force: true }); }
// Chrome 停机后文件锁会拖几秒，删 profile 目录带重试
async function rmDirRetry(p) {
  for (let i = 0; i < 10; i++) {
    try { fs.rmSync(p, { recursive: true, force: true }); } catch (e) {}
    if (!fs.existsSync(p)) return true;
    await new Promise(r => setTimeout(r, 800));
  }
  return false;
}

let pageServer, probeSrv, sup;

async function cleanup() {
  try {
    const r = await api('GET', '/slots');
    for (const s of (r.slots || [])) {
      try { await api('POST', '/slot/' + s.id + '/stop', {}); } catch (e) {}
    }
  } catch (e) {}
  if (sup) { try { sup.kill(); } catch (e) {} }
  if (pageServer) { try { pageServer.close(); } catch (e) {} }
  if (probeSrv) { try { probeSrv.close(); } catch (e) {} }
  await new Promise(r => setTimeout(r, 1500));
}

(async () => {
  rmHome(); // 上次跑剩的档会假阴性，先清干净
  // 效率模式测试用的拦截清单：blocked.example 会被 MAP 到 127.0.0.2
  fs.mkdirSync(HOME, { recursive: true });
  fs.writeFileSync(path.join(HOME, 'blocklist.txt'), 'blocked.example\n');
  // 本地页面服务器（离线，不碰外网）
  const pageHandler = (req, res) => {
    if (req.url === '/img.png') {
      res.writeHead(200, { 'Content-Type': 'image/png', 'Content-Length': PNG.length });
      return res.end(PNG);
    }
    if (req.url === '/probe') { // 命中探针的请求返回这个（效率模式 A/B 断言用）
      res.writeHead(200, { 'Content-Type': 'text/plain' });
      return res.end('probe-ok');
    }
    if (req.url === '/rich') { // 带 og/json-ld/meta 的富信息页（structured 断言用）
      res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8' });
      return res.end('<!doctype html><html lang="zh"><head><title>rich-page</title>'
        + '<meta name="description" content="页面描述X">'
        + '<meta property="og:title" content="OG标题"><meta property="og:type" content="product">'
        + '<meta name="twitter:card" content="summary">'
        + '<link rel="canonical" href="http://127.0.0.1:' + PAGE_PORT + '/canon">'
        + '<script type="application/ld+json">{"@context":"https://schema.org","@type":"Product","name":"产品"}</script>'
        + '</head><body><a href="/a">a</a><a href="/b">b</a></body></html>');
    }
    res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8' });
    res.end('<!doctype html><html><head><title>farm-test-page</title></head><body><img id="im" src="/img.png"><div id="v">0</div></body></html>');
  };
  pageServer = http.createServer(pageHandler);
  await new Promise(r => pageServer.listen(PAGE_PORT, '127.0.0.1', r));
  // 探针镜像：127.0.0.2 上也听一份——效率模式把广告域 MAP 到 127.0.0.2，能连上=映射真的生效
  probeSrv = http.createServer(pageHandler);
  await new Promise((res, rej) => probeSrv.listen(PAGE_PORT, '127.0.0.2', res).once('error', rej));

  sup = spawn(process.execPath, [path.join(ROOT, 'supervisor.js')], {
    env: {
      ...process.env, FARM_HOME: HOME, FARM_PORT: String(S_PORT), FARM_BASE_PORT: String(BASE),
      FARM_CHROME_GUARD_MIN: '1',
      FARM_CHROME_DEFAULT_UDD: path.join(os.tmpdir(), 'guard-fake-default'), // 门卫的「默认目录」指到沙盒，好造活的假小偷
    },
    stdio: ['ignore', 'pipe', 'pipe'], windowsHide: true,
  });
  sup.stdout.on('data', () => {}); sup.stderr.on('data', d => process.stderr.write('[总管] ' + d));
  await waitReady();
  console.log('总管就绪，开始断言：');

  // 1 登记与分配
  let r = await api('GET', '/slots');
  ok('空农场列表', r.ok && r.slots.length === 0, r);
  r = await api('POST', '/slots/add', { note: '测试A' });
  ok('登记档位01 端口' + BASE, r.ok && r.slot.id === '01' && r.slot.port === BASE, r);
  r = await api('POST', '/slots/add', { note: '测试B' });
  ok('登记档位02 端口' + (BASE + 1), r.ok && r.slot.id === '02' && r.slot.port === BASE + 1, r);

  // 2 启动/开页/eval
  r = await api('POST', '/slot/01/start', {});
  ok('档位01无窗口启动', r.ok && r.port === BASE, r);
  r = await api('POST', '/slot/01/open', { url: PAGE_URL });
  ok('开页返回targetId', r.ok && !!r.targetId, r);
  r = await waitEval('01', 'document.title', t => t === 'farm-test-page');
  ok('eval 页面标题回读', r.ok && r.result === 'farm-test-page', r);
  r = await api('POST', '/slot/01/eval', { code: "localStorage.setItem('farm','A'); return localStorage.getItem('farm')" });
  ok('eval 顶层return被IIFE兜住', r.ok && r.result === 'A', r);

  // 3 数据隔离：档位02 同一页面，读不到档位01 的 localStorage
  await api('POST', '/slot/02/open', { url: PAGE_URL });
  r = await waitEval('02', 'localStorage.getItem("farm")', v => v === null);
  ok('两档位数据隔离（02读不到01的存储）', r.ok && r.result === null, r);

  // 4 性能：图片被拦
  r = await waitEval('01', 'document.images[0].naturalWidth', w => w === 0);
  ok('图片拦截生效（naturalWidth=0）', r.ok && r.result === 0, r);

  // 5 报错不吞
  r = await api('POST', '/slot/01/eval', { code: "throw new Error('炸给你看')" });
  ok('eval异常原样上抛', r.ok === false && /炸给你看/.test(r.error || ''), r);

  // 5b 效率模式（v0.1.21）：域名拦截 A/B——blocked.example 不存在于公网，
  // 普通档 fetch 必失败；效率档被 --host-resolver-rules MAP 到 127.0.0.2，
  // 正好命中上面那份探针镜像=拦截映射端到端生效（fetch no-cors 成功即resolve）
  const PROBE = "var c = new AbortController(); setTimeout(function(){ c.abort(); }, 5000);"
    + "return fetch('http://sub.blocked.example:" + PAGE_PORT + "/probe', { mode: 'no-cors', signal: c.signal })"
    + ".then(function(){ return 'fetched' }).catch(function(e){ return 'fail:' + String(e && e.name || e) })";
  r = await api('POST', '/slot/02/eval', { code: PROBE });
  ok('普通档：拦截清单域名请求失败（A 组对照）', r.ok && /^fail:/.test(String(r.result)), r.result);
  await api('POST', '/slot/02/stop', {});
  r = await api('POST', '/slot/02/start', { mode: 'eff' });
  ok('档位02效率启动（mode=eff）', r.ok && r.mode === 'eff', r);
  await api('POST', '/slot/02/open', { url: PAGE_URL });
  await waitEval('02', 'document.title', t => t === 'farm-test-page');
  let d02 = await api('GET', '/slot/02');
  ok('档位详情带 mode=eff', d02.ok && d02.mode === 'eff', d02.mode);
  const lstAll = await api('GET', '/slots');
  ok('/slots 列表带 mode', (lstAll.slots.find(s => s.id === '02') || {}).mode === 'eff', lstAll.slots.map(s => s.id + ':' + s.mode));
  r = await api('POST', '/slot/02/eval', { code: PROBE });
  ok('效率档：域名被 MAP 到 127.0.0.2 命中本地探针（拦截生效）', r.ok && r.result === 'fetched', r.result);

  // 5c structured（v0.1.21）：当前页 og/json-ld/meta 一把抓
  await api('POST', '/slot/02/open', { url: 'http://127.0.0.1:' + PAGE_PORT + '/rich' });
  await waitEval('02', 'document.title', t => t === 'rich-page');
  r = await api('POST', '/slot/02/structured', {});
  const st = r.ok ? r.result : {};
  ok('structured 抓 og/twitter/meta/canonical', r.ok && st.title === 'rich-page' && st.description === '页面描述X'
    && st.og && st.og.title === 'OG标题' && st.og.type === 'product' && st.twitter && st.twitter.card === 'summary'
    && st.canonical && st.canonical.indexOf('/canon') >= 0, st);
  ok('structured json-ld 解析成对象', Array.isArray(st.jsonld) && st.jsonld[0] && st.jsonld[0]['@type'] === 'Product' && st.jsonld[0].name === '产品', st.jsonld);

  // 6 停机干净
  r = await api('POST', '/slot/01/stop', {});
  let alive = true;
  try { await api('GET', '/slots'); const lst = await api('GET', '/slots'); alive = lst.slots.find(s => s.id === '01').alive; } catch (e) {}
  ok('档位01停机且端口关闭', r.ok && alive === false, { r, alive });

  // 7 快照→抹盘→回滚（登录态等价物 = localStorage 标记）
  await api('POST', '/slot/01/start', {});
  await api('POST', '/slot/01/open', { url: PAGE_URL });
  await waitEval('01', 'document.title', t => t === 'farm-test-page');
  await api('POST', '/slot/01/eval', { code: "localStorage.setItem('farm','snapmark'); return 1" });
  // localStorage 写进 leveldb 有 Chromium 自己的提交延迟（实测写完亚秒内停机就丢、
  // "A" 早写几秒就活）——轮询 profile 里的 leveldb 文件，snapmark 字节真出现才算落盘
  const ldbDir = path.join(HOME, 'slots', '01', 'Default', 'Local Storage', 'leveldb');
  const needles = [Buffer.from('snapmark', 'utf8'), Buffer.from('snapmark', 'utf16le'), Buffer.from('snapmark', 'utf16le').swap16()];
  let onDisk = false;
  for (let i = 0; i < 30 && !onDisk; i++) {
    try {
      for (const f of fs.readdirSync(ldbDir)) {
        const buf = fs.readFileSync(path.join(ldbDir, f));
        if (needles.some(n => buf.includes(n))) { onDisk = true; break; }
      }
    } catch (e) {}
    if (!onDisk) await new Promise(r => setTimeout(r, 400));
  }
  ok('snapmark 写进 leveldb（磁盘可见）', onDisk);
  // 停→起读回：钉死"已落盘的登录态等价物，停起不丢"
  await api('POST', '/slot/01/stop', {});
  await api('POST', '/slot/01/start', {});
  await api('POST', '/slot/01/open', { url: PAGE_URL });
  r = await waitEval('01', "localStorage.getItem('farm')", v => v === 'snapmark');
  ok('snapmark 落盘确认（停起读回）', r.ok && r.result === 'snapmark', r);
  r = await api('POST', '/slot/01/snapshot', { name: '备份1' });
  ok('快照落盘', r.ok && fs.existsSync(path.join(HOME, 'snapshots', '01-备份1')), r);
  await rmDirRetry(path.join(HOME, 'slots', '01')); // 手动抹盘，模拟 profile 损坏
  r = await api('POST', '/slot/01/restore', { name: '备份1' });
  await api('POST', '/slot/01/open', { url: PAGE_URL });
  r = await waitEval('01', "localStorage.getItem('farm')", v => v === 'snapmark');
  ok('抹盘后回滚，登录标记还在', r.ok && r.result === 'snapmark', r);

  // 10 新路由：快照列表 + 当前页截图（GUI 详情用）
  r = await api('GET', '/slot/01/snapshots');
  ok('快照列表路由（含备份1）', r.ok && (r.snapshots || []).some(x => x.name === '备份1'), r);
  const shot = await new Promise((resolve, reject) => {
    http.get({ host: '127.0.0.1', port: S_PORT, path: '/slot/01/shot' }, res => {
      const chunks = [];
      res.on('data', c => chunks.push(c));
      res.on('end', () => resolve({ type: res.headers['content-type'], buf: Buffer.concat(chunks) }));
    }).on('error', reject);
  });
  ok('截图路由返回真 JPEG', shot.type === 'image/jpeg' && shot.buf.length > 100 && shot.buf[0] === 0xFF && shot.buf[1] === 0xD8, { type: shot.type, len: shot.buf.length });

  // 11 GUI 注入防护：恶意网页标题在详情里只能显示为纯文本，注入代码不执行
  await api('POST', '/slot/01/eval', { code: 'document.title = \'<img src=x onerror="window.__pwn=1">\'; return document.title' });
  await api('POST', '/slot/02/open', { url: 'http://127.0.0.1:' + S_PORT + '/gui' });
  r = await waitEval('02', "document.querySelectorAll('.slot').length >= 2 ? 'cards' : 'wait'", v => v === 'cards');
  ok('GUI 页面在档02里打开（卡片渲染出来）', r.ok && r.result === 'cards', r);
  await api('POST', '/slot/02/eval', { code: "toggleDetail('01'); return 1" });
  r = await waitEval('02', "document.getElementById('d-01') ? document.getElementById('d-01').innerHTML : ''", h => h.includes('&lt;img'));
  const html = String(r.result || '');
  ok('恶意标题被转义（纯文本显示）', r.ok && html.includes('&lt;img') && !html.includes('<img src=x'), r);
  r = await waitEval('02', 'String(window.__pwn)', v => v === 'undefined');
  ok('注入代码没执行（window.__pwn 未定义）', r.ok && r.result === 'undefined', r);

  // 13 skill 绑定（v0.1.19）：newscript 带绑定/说明、坏绑定拒收、bind 绑解绑、无档无绑人话报错、导入重绑映射
  const stepsB = [{ selector: '#b1' }];
  let rNew = await api('POST', '/script/new', { name: '绑定探针', steps: stepsB, bindSlot: '02', desc: '下载 资源站 的 zip 包' });
  ok('newscript 带 bindSlot+desc 落盘', rNew.ok && rNew.id, rNew);
  const boundSc = (await api('GET', '/scripts')).scripts.find(s => s.id === rNew.id);
  ok('脚本列表带绑定和说明', boundSc && boundSc.bindSlot === '02' && boundSc.desc === '下载 资源站 的 zip 包', boundSc);
  const rBadBind = await api('POST', '/script/new', { name: '坏绑定', steps: stepsB, bindSlot: '99' });
  ok('bindSlot 档位不存在当场拒收', rBadBind.ok === false && /bindSlot/.test(rBadBind.error || ''), rBadBind);
  const rBind = await api('POST', '/script/' + rNew.id + '/bind', { slot: '01', desc: '改成档01了' });
  ok('bind 路由改绑+改说明', rBind.ok && rBind.bindSlot === '01' && rBind.desc === '改成档01了', rBind);
  const rUnbind = await api('POST', '/script/' + rNew.id + '/bind', { slot: '' });
  ok('bind 空串解绑', rUnbind.ok && rUnbind.bindSlot === null, rUnbind);
  const rStartNone = await api('POST', '/script/' + rNew.id + '/start', {});
  ok('无档无绑启动给人话报错', rStartNone.ok === false && /没说在哪个档跑/.test(rStartNone.error || ''), rStartNone);
  // 导入重绑：旧配置档位号 05 → 新机自动编号，脚本绑定要跟过去；对不上的（77）宁可摘绑
  const rImp = await api('POST', '/config/import', {
    farm: 'browser-farm',
    slots: [{ id: '05', note: '搬来的档', port: 9399 }],
    scripts: [
      { id: '90', name: '搬家绑定', type: 'loop', steps: stepsB, bindSlot: '05' },
      { id: '91', name: '搬家丢绑', type: 'loop', steps: stepsB, bindSlot: '77' },
    ],
  });
  const movedSlot = (await api('GET', '/slots')).slots.find(s => s.port === 9399);
  const movedScripts = (await api('GET', '/scripts')).scripts;
  const s90 = movedScripts.find(s => s.id === '90');
  const s91 = movedScripts.find(s => s.id === '91');
  ok('导入重绑：旧档号映射到新档号', rImp.ok && rImp.droppedBinds === 1 && movedSlot && s90 && s90.bindSlot === movedSlot.id, { rImp, movedSlot: movedSlot && movedSlot.id, s90 });
  ok('对不上的绑定宁可摘掉（不绑错账号）', s91 && !s91.bindSlot, s91);

  // 14 Chrome 门卫（v0.1.20）：真起两个无头 Chrome——相对路径目录的=探针小偷（该清），
  //    绝对路径目录的=正经自动化自留地（不该碰）；农场档位全程不能被误伤
  const CHROME_BIN = [
    'C:\\Program Files\\Google\\Chrome\\Application\\chrome.exe',
    'C:\\Program Files (x86)\\Google\\Chrome\\Application\\chrome.exe',
    path.join(os.homedir(), 'AppData\\Local\\Google\\Chrome\\Application\\chrome.exe'),
  ].find(fs.existsSync);
  // 新版 Chrome 不认相对路径目录（一律回落默认目录=小偷的真机制），活的假小偷用「假默认目录」造：
  const FAKE_DEFAULT = path.join(os.tmpdir(), 'guard-fake-default');
  const thief = spawn(CHROME_BIN, ['--headless=new', '--user-data-dir=' + FAKE_DEFAULT, '--no-first-run', 'about:blank'], { cwd: os.tmpdir(), stdio: 'ignore', windowsHide: true });
  const good = spawn(CHROME_BIN, ['--headless=new', '--user-data-dir=' + path.join(HOME, 'guard-good-udd'), '--no-first-run', 'about:blank'], { cwd: HOME, stdio: 'ignore', windowsHide: true });
  await new Promise(r => setTimeout(r, 3000));
  ok('两个无头夹具都起来了', thief.exitCode === null && good.exitCode === null, { t: thief.exitCode, g: good.exitCode });
  const rg = await api('POST', '/chrome/fix', {});
  await new Promise(r => setTimeout(r, 1500));
  const gone = p => { try { process.kill(p, 0); return false; } catch (e) { return true; } };
  ok('门卫清掉相对路径的无头探针（占默认目录那类）', rg.ok && gone(thief.pid), { rg, thief: thief.pid });
  ok('门卫放过了绝对路径的无头（正经自动化的自留地）', !gone(good.pid), { pid: good.pid });
  const slotsAfterGuard = await api('GET', '/slots');
  ok('农场档位的浏览器没被门卫碰', (slotsAfterGuard.slots.find(s => s.id === '01') || {}).alive === true, slotsAfterGuard.slots.map(s => s.id + ':' + s.alive));
  try { execSync('taskkill /F /T /PID ' + good.pid); } catch (e) {} // 自留地是被门卫故意放过的，测试自己收
  try { fs.rmSync(FAKE_DEFAULT, { recursive: true, force: true }); } catch (e) {} // 假默认目录在临时目录，收掉

  // 8 CLI 冒烟
  const cli = execSync('node farm.js slots', {
    cwd: ROOT, encoding: 'utf8',
    env: { ...process.env, FARM_HOME: HOME, FARM_PORT: String(S_PORT), FARM_BASE_PORT: String(BASE) },
  });
  ok('CLI farm.js 冒烟', cli.includes('02') && cli.includes('alive'), cli.slice(0, 80));

  // 9 移除
  r = await api('POST', '/slot/01/remove', { wipe: true });
  ok('移除档位01并清数据', r.ok && r.wiped === true && !fs.existsSync(path.join(HOME, 'slots', '01')), r);

  await cleanup();

  // 12 farm.log 滚动：塞 1.1MB 假日志，阈值调 1MB，再起一个总管看它开机归档
  fs.writeFileSync(path.join(HOME, 'farm.log'), Buffer.alloc(1100 * 1024, 120)); // 120='x'
  const sup2 = spawn(process.execPath, [path.join(ROOT, 'supervisor.js')], {
    env: { ...process.env, FARM_HOME: HOME, FARM_PORT: '9314', FARM_BASE_PORT: '9561', FARM_LOG_MAX_MB: '1' },
    stdio: ['ignore', 'pipe', 'pipe'], windowsHide: true,
  });
  sup2.stdout.on('data', () => {}); sup2.stderr.on('data', d => process.stderr.write('[总管2] ' + d));
  let rotated = false;
  for (let i = 0; i < 40 && !rotated; i++) {
    await new Promise(r2 => setTimeout(r2, 300));
    rotated = fs.existsSync(path.join(HOME, 'farm.log.old')) && fs.existsSync(path.join(HOME, 'farm.log'));
    try { await api('GET', '/health', null, 9314); } catch (e) {}
  }
  const oldSize = fs.existsSync(path.join(HOME, 'farm.log.old')) ? fs.statSync(path.join(HOME, 'farm.log.old')).size : -1;
  const newSize = fs.existsSync(path.join(HOME, 'farm.log')) ? fs.statSync(path.join(HOME, 'farm.log')).size : -1;
  ok('farm.log 超限滚动（旧日志归档成 .old，新日志从零开始）', oldSize > 1048576 && newSize >= 0 && newSize < 100000, { oldSize, newSize });
  sup2.kill();
  await new Promise(r2 => setTimeout(r2, 800));

  if (!(await rmDirRetry(HOME))) console.error('沙盒没删干净（chrome 残进程攥着文件），下次跑前手清: ' + HOME);
  console.log('\n' + pass + '/' + total + ' 断言' + (pass === total ? '全过 ✓' : '有失败 ✗'));
  process.exit(pass === total ? 0 : 1);
})().catch(async e => {
  console.error('测试炸了: ' + e.message);
  await cleanup();
  if (!(await rmDirRetry(HOME))) console.error('沙盒没删干净（chrome 残进程攥着文件），下次跑前手清: ' + HOME);
  process.exit(1);
});
