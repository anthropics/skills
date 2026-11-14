// 浏览器农场总管：一个账号档 = 一个 Chrome 实例 = 一个固定端口 = 一个独立数据目录
// 常驻运行: node supervisor.js   （HTTP 口默认 9300，FARM_PORT 可改；档位端口默认 9331 起，避开常用的 9222）
'use strict';
const http = require('http');
const fs = require('fs');
const path = require('path');
const os = require('os');
const { spawn, exec } = require('child_process');
const scripter = require('./scripter');

const HOME = process.env.FARM_HOME || __dirname;
const PORT = Number(process.env.FARM_PORT || 9300);
const BASE_PORT = Number(process.env.FARM_BASE_PORT || 9331);
// 空闲自动停：headless 档超过 N 分钟没有任何 /slot/:id/* 请求就停（登录态不丢，再 start 即用）。
// 0=关闭。headful（登录窗口）永不自动停——人正在里面操作。
const IDLE_MIN = Number(process.env.FARM_IDLE_MIN || 30);
const SLOTS_FILE = path.join(HOME, 'slots.json');
const DATA_DIR = path.join(HOME, 'slots');
const SNAP_DIR = path.join(HOME, 'snapshots');
const LOG_FILE = path.join(HOME, 'farm.log');

// ---------- 效率模式（eff）：无窗口之上的再省一档 ----------
// 省 resources 的本质是砍掉用不着的：真 Chrome 砍不掉渲染引擎，能砍的是流量和后台服务——
// 广告/埋点域名用 Chrome 原生 --host-resolver-rules 在 DNS 层直接断到 127.0.0.2（请求出不了
// 机器、秒失败、浏览器级生效=新标签页天然全跟得上，不用挂任何会话），远端字体不下载，
// 视频不许自动播，磁盘缓存再砍一档，顺手关 DoH 防安全 DNS 绕过域名映射。
// 清单=工作区根 blocklist.txt（一行一个域名，# 注释，子域自动跟拦）。
// 默认只放国际广告/埋点域名——国内投放平台自己的域一个不碰，要拦自己往清单里加。
const BLOCKLIST_FILE = path.join(HOME, 'blocklist.txt');
function loadBlocklist() {
  let raw;
  try { raw = fs.readFileSync(BLOCKLIST_FILE, 'utf8'); }
  catch (e) { return []; } // 没有清单文件=只省不带拦，不报错
  const hosts = [];
  for (let line of raw.split(/\r?\n/)) {
    line = line.split('#')[0].trim().toLowerCase().replace(/^[\*.]+/, '').replace(/\/.*$/, '');
    if (/^[a-z0-9.-]+$/.test(line) && line.includes('.')) hosts.push(line);
  }
  return [...new Set(hosts)].slice(0, 200); // 命令行长度护栏：超 200 截断
}

// 最近一次 start 的模式：看护/eval/快照这些自动拉回场景保持同款跑法
// （headful 不自动弹窗回来是原行为；eff 拉回仍是 eff，拦截清单才不丢）
const lastMode = new Map(); // slotId -> 'headless' | 'headful' | 'eff'
function reviveOpts(slotId) {
  return lastMode.get(slotId) === 'eff' ? { mode: 'eff' } : {};
}

// ---------- 登记 ----------
function loadCfg() {
  try {
    return JSON.parse(fs.readFileSync(SLOTS_FILE, 'utf8'));
  } catch (e) {
    return { slots: [], nextPort: BASE_PORT, nextId: 1 };
  }
}
function saveCfg(cfg) {
  fs.writeFileSync(SLOTS_FILE, JSON.stringify(cfg, null, 2));
}
function log(msg) {
  const line = `[${new Date().toISOString().replace('T', ' ').slice(0, 19)}] ${msg}`;
  try { fs.appendFileSync(LOG_FILE, line + '\n'); } catch (e) { /* 日志失败不炸主流程 */ }
  console.log(line);
}

// 日志滚动：无限追加一年能滚几百 MB，开机时超过 FARM_LOG_MAX_MB（默认 20）就归档成 farm.log.old（旧档只留一份）
const LOG_MAX_MB = Number(process.env.FARM_LOG_MAX_MB || 20);
try {
  if (fs.statSync(LOG_FILE).size > LOG_MAX_MB * 1024 * 1024) {
    try { fs.unlinkSync(LOG_FILE + '.old'); } catch (e) {}
    fs.renameSync(LOG_FILE, LOG_FILE + '.old');
    log('farm.log 超过 ' + LOG_MAX_MB + 'MB，旧日志归档成 farm.log.old');
  }
} catch (e) { /* 没有日志文件 = 首次开机 */ }

// ---------- Chrome 查找 ----------
function findChrome(cfg) {
  const cands = [
    process.env.FARM_CHROME,
    cfg.chromePath,
    'C:\\Program Files\\Google\\Chrome\\Application\\chrome.exe',
    'C:\\Program Files (x86)\\Google\\Chrome\\Application\\chrome.exe',
    path.join(os.homedir(), 'AppData\\Local\\Google\\Chrome\\Application\\chrome.exe'),
    'C:\\Program Files (x86)\\Microsoft\\Edge\\Application\\msedge.exe',
    'C:\\Program Files\\Microsoft\\Edge\\Application\\msedge.exe',
  ].filter(Boolean);
  for (const c of cands) if (fs.existsSync(c)) return c;
  throw new Error('没找到 Chrome/Edge，用 FARM_CHROME 环境变量指路径。找过：\n' + cands.join('\n'));
}

// ---------- HTTP 小工具（不用 fetch，避开代理环境变量干扰） ----------
function jget(port, p, timeoutMs) {
  return new Promise((resolve, reject) => {
    const req = http.get({ host: '127.0.0.1', port, path: p, timeout: timeoutMs || 1200 }, res => {
      let d = '';
      res.on('data', c => d += c);
      res.on('end', () => {
        try { resolve(JSON.parse(d)); } catch (e) { reject(new Error('非 JSON 响应: ' + d.slice(0, 120))); }
      });
    });
    req.on('timeout', () => req.destroy(new Error('timeout')));
    req.on('error', reject);
  });
}

// ---------- CDP 单次调用 ----------
function cdp(wsUrl, method, params) {
  return new Promise((resolve, reject) => {
    let ws;
    try { ws = new WebSocket(wsUrl); } catch (e) { return reject(e); }
    const timer = setTimeout(() => { try { ws.close(); } catch (e) {} reject(new Error('CDP 超时: ' + method)); }, 20000);
    ws.onopen = () => ws.send(JSON.stringify({ id: 1, method, params: params || {} }));
    ws.onerror = () => { clearTimeout(timer); reject(new Error('WS 连不上: ' + method)); };
    ws.onmessage = ev => {
      const m = JSON.parse(ev.data);
      if (m.id === 1) {
        clearTimeout(timer);
        try { ws.close(); } catch (e) {}
        if (m.error) reject(new Error('CDP 报错 ' + method + ': ' + m.error.message));
        else resolve(m.result);
      }
    };
  });
}

// ---------- eval 表达式包裹（顶层 return 的坑在这兜住） ----------
function toExpr(code) {
  const t = code.trim();
  const stmt = /^(const|let|var|function|class|if|for|while|return|throw|try|switch|\{)\b/.test(t)
    || /\breturn\b/.test(t) || /\bawait\b/.test(t) || /;\s*$/.test(t) || t.includes('\n');
  if (!stmt) return t; // 纯表达式直接求值
  const isAsync = /\bawait\b/.test(t);
  return (isAsync ? '(async () => {' : '(() => {') + t + '\n})()';
}

const sleep = ms => new Promise(r => setTimeout(r, ms));
// Chrome 刚停机的几秒内 profile 目录还被占（crashpad/杀毒扫描拖文件锁），删目录必须带重试
async function rmDir(p) {
  for (let i = 0; i < 10; i++) {
    try { fs.rmSync(p, { recursive: true, force: true }); } catch (e) {}
    if (!fs.existsSync(p)) return;
    await sleep(800);
  }
  throw new Error('目录删不掉（被占用）: ' + p);
}
// localStorage 的 leveldb 落盘比主进程退出还晚（StorageService 子进程拖几拍）：
// 快照拷盘前等这些文件 mtime 安静下来，防止拷到写一半的旧状态（实测回滚出旧值就这么来的）
async function storageSettled(slotDir, capMs) {
  const dirs = [path.join(slotDir, 'Default', 'Local Storage', 'leveldb'), path.join(slotDir, 'Default', 'Session Storage')];
  const stamp = () => {
    let newest = 0;
    for (const d of dirs) {
      let files; try { files = fs.readdirSync(d, { withFileTypes: true }); } catch (e) { continue; }
      for (const f of files) { try { newest = Math.max(newest, fs.statSync(path.join(d, f.name)).mtimeMs); } catch (e) {} }
    }
    return newest;
  };
  const end = Date.now() + (capMs || 5000);
  let prev = stamp();
  while (Date.now() < end) {
    await sleep(300);
    const cur = stamp();
    if (cur === prev) return; // 两拍没新写入，落盘安静了
    prev = cur;
  }
}
// 快照拷盘同一个坑：Chrome 刚停机，profile 里 Default\Network 等文件还被残留子进程占着，
// cpSync 撞锁直接炸（炸前还留半份残拷）——重试前先清残拷，锁 8 秒还不放就真报错
async function cpProfile(from, to) {
  let lastErr = null;
  for (let i = 0; i < 8; i++) {
    try {
      await rmDir(to);
      fs.cpSync(from, to, { recursive: true });
      return;
    } catch (e) { lastErr = e; await sleep(1000); }
  }
  throw lastErr;
}

// ---------- 档位进程管理 ----------
const running = new Map(); // id -> { proc, pid, adopted, mode }
const lastUsed = new Map(); // id -> 最后活动时间戳（毫秒）。活动=该档的任意 /slot/:id/* 请求
function touchSlot(id) { lastUsed.set(id, Date.now()); }

// ---------- 空闲巡检 ----------
let sweeping = false;
setInterval(async () => {
  if (!IDLE_MIN || sweeping) return;
  sweeping = true;
  try {
    const cfg = loadCfg();
    // 脚本运行中的档不杀：盯表任务几小时不发 API 请求，但一直在干活
    const busySlots = new Set([...scriptRuns.values()].filter(r => r.state === 'running').map(r => r.slotId));
    for (const slot of cfg.slots) {
      const run = running.get(slot.id);
      if (!run || run.mode === 'headful' || busySlots.has(slot.id)) continue; // 没在跑/登录窗口/脚本在用：不管
      const idleMs = Date.now() - (lastUsed.get(slot.id) || 0);
      if (idleMs <= IDLE_MIN * 60000) continue;
      await stopSlot(slot);
      log('档位 ' + slot.id + ' 空闲 ' + Math.round(idleMs / 60000) + ' 分钟自动停（登录态保留，start 即用）');
    }
  } catch (e) { log('空闲巡检出错（下一轮继续）: ' + e.message); }
  finally { sweeping = false; }
}, 30000);


async function isAlive(slot) {
  try { await jget(slot.port, '/json/version', 900); return true; } catch (e) { return false; }
}

// ---------- 脚本看护：脚本跑着但档死了（人关了整个浏览器/闪退），自动拉回来 ----------
// 「网页全关了脚本还跑着」要成立到底：页面没了脚本自己开回（v0.1.15），
// 浏览器没了总管拉回档（本层）。真要停：halt（GUI 停止钮/CLI stop）连脚本带档一起停。
const slotDeadSince = new Map(); // slotId -> 首次看到死的时间：切窗口/重启的几秒空窗不算死，过 15 秒还死才拉
let healing = false;
setInterval(async () => {
  if (healing) return;
  healing = true;
  try {
    const cfg = loadCfg();
    const busy = new Set([...scriptRuns.values()].filter(r => r.state === 'running').map(r => r.slotId));
    for (const id of [...slotDeadSince.keys()]) if (!busy.has(id)) slotDeadSince.delete(id);
    for (const r of scriptRuns.values()) {
      if (r.state !== 'running' || !cfg.slots.some(x => x.id === r.slotId)) continue; // 档被移除：脚本自己等满重连窗收场
      const slot = cfg.slots.find(x => x.id === r.slotId);
      if (await isAlive(slot)) { slotDeadSince.delete(slot.id); continue; }
      const first = slotDeadSince.get(slot.id) || Date.now();
      slotDeadSince.set(slot.id, first);
      if (Date.now() - first < 15000) continue;
      slotDeadSince.delete(slot.id);
      log('[脚本' + r.scriptId + '] 档 ' + slot.id + ' 死了但脚本在跑，自动拉起（无窗口）');
      await startSlot(cfg, slot, reviveOpts(slot.id));
    }
  } catch (e) { log('脚本看护出错（下一轮继续）: ' + e.message); }
  finally { healing = false; }
}, 10000);

async function startSlot(cfg, slot, opts) {
  const mode = (opts && opts.mode) || 'headless';
  lastMode.set(slot.id, mode);
  if (await isAlive(slot)) {
    if (!running.has(slot.id)) running.set(slot.id, { adopted: true, mode });
    touchSlot(slot.id);
    if (mode === 'headful') ensureBar(slot).catch(e => log('档 ' + slot.id + ' 常驻录制条没挂上: ' + e.message));
    return { ok: true, alreadyRunning: true, port: slot.port, mode };
  }
  // 上一发没起来的残 chrome 可能还活着占着 profile（端口检查看不见的形态：只绑了 IPv6），
  // 不连根杀掉就再起一个，会撞 profile 锁秒退（退出码 21）连环失败
  const prev = running.get(slot.id);
  if (prev && prev.proc && prev.proc.exitCode === null && prev.proc.signalCode === null) {
    await killTree(prev.pid, '清上一发没起来的残chrome');
  }
  const chrome = findChrome(cfg);
  const dir = path.join(DATA_DIR, slot.id);
  fs.mkdirSync(dir, { recursive: true });
  const args = [
    '--remote-debugging-port=' + slot.port,
    '--user-data-dir=' + dir,
    '--no-first-run', '--no-default-browser-check',
    '--disable-gpu',
    '--disable-background-timer-throttling',
    '--disable-renderer-backgrounding',
    '--disable-backgrounding-occluded-windows',
    '--disable-extensions', '--disable-sync', '--disable-component-update',
    '--disable-crash-reporter',
    // 省资源组合（puppeteer 默认参数同款思路 + 本农场 farm.log 实测刷屏的痛点）：
    // 静音省音频开销；断后台偷流量/上报类服务；basic 密码库直接灭掉 Windows 上无意义还刷日志的 password store 报错；
    // 磁盘缓存默认无上限，多档一起吃磁盘，锁 32MB；Translate/MediaRouter/喂流是纯用不上的功能，
    // BackForwardCache+CalculateNativeWinOcclusion 关掉：后者是 Windows 遮挡计算静默吞合成点击的老坑（skill-forge 钉过）
    '--mute-audio',
    '--disable-background-networking',
    '--disable-client-side-phishing-detection',
    '--disable-domain-reliability',
    '--disable-breakpad',
    '--password-store=basic', '--use-mock-keychain',
    // 磁盘缓存默认无上限，多档一起吃磁盘：普通档锁 32MB，效率档砍到 8MB（够缓存表头脚本，不攒垃圾）
    '--disk-cache-size=' + (mode === 'eff' ? 8388608 : 33554432),
    // Translate/MediaRouter/喂流是纯用不上的功能；BackForwardCache+CalculateNativeWinOcclusion 关掉：
    // 后者是 Windows 遮挡计算静默吞合成点击的老坑（skill-forge 钉过）。效率档追加关 DoH——
    // 安全 DNS 会绕过 host-resolver-rules，域名拦截就成摆设了
    '--disable-features=' + (mode === 'eff'
      ? 'Translate,MediaRouter,InterestFeedContentSuggestion,BackForwardCache,CalculateNativeWinOcclusion,DnsOverHttps'
      : 'Translate,MediaRouter,InterestFeedContentSuggestion,BackForwardCache,CalculateNativeWinOcclusion'),
    '--window-size=1440,900',
  ];
  if (mode !== 'headful') {
    args.push('--headless=new');
    // 批量操作图片是最大开销；登录模式（headful）必须放行图片，否则二维码都看不见
    if (slot.blockImages !== false) args.push('--blink-settings=imagesEnabled=false');
    if (mode === 'eff') {
      args.push('--disable-remote-fonts');                    // 远端字体不下载（页面用本机字体渲染）
      args.push('--autoplay-policy=user-gesture-required');   // 视频不许自动播，省解码
      const blocked = loadBlocklist();
      if (blocked.length) {
        // 域名拦截：MAP 到 127.0.0.2（Windows 整段 127/8 都是本机回环，那上面没服务=秒拒）
        args.push('--host-resolver-rules=' + blocked.flatMap(d => ['MAP ' + d + ' 127.0.0.2', 'MAP *.' + d + ' 127.0.0.2']).join(','));
      }
      log('档位 ' + slot.id + ' 效率模式启动' + (blocked.length ? '：拦 ' + blocked.length + ' 个域名（blocklist.txt 可改，改完重启档生效）' : '（没找到 blocklist.txt，只省不带拦）'));
    }
  }
  // detached：Windows 上 libuv 默认把子进程放进本进程的 job（父死全灭），
  // "总管挂了档位不死"要成立必须脱离 job（farm.js 拉总管同款手法）
  const proc = spawn(chrome, args, { stdio: ['ignore', 'ignore', 'pipe'], detached: true });
  proc.unref();
  running.set(slot.id, { proc, pid: proc.pid, mode });
  log('档位 ' + slot.id + ' 拉起 chrome=' + chrome + ' pid=' + proc.pid + (mode === 'headful' ? '（窗口）' : '（无窗口）'));
  proc.on('error', e => { log('档位 ' + slot.id + ' 启动失败: ' + e.message); running.delete(slot.id); });
  // Chrome 启动失败只给退出码不给原因，stderr 进 farm.log 才能排障（正常启动只打一行 DevTools listening）
  proc.stderr.on('data', d => { const s = String(d).trim(); if (s) log('档位 ' + slot.id + ' chrome: ' + s.slice(0, 200)); });
  proc.on('exit', (code) => {
    log('档位 ' + slot.id + ' 进程退出 code=' + code);
    running.delete(slot.id);
    if (recSession && recSession.slotId === slot.id) abortRec(slot.id, '浏览器退出了'); // 关窗/闪退都不能把录制会话挂着
    closeBar(slot.id);
  });
  // 等调试口就绪
  for (let i = 0; i < 100; i++) {
    await new Promise(r => setTimeout(r, 300));
    if (await isAlive(slot)) {
      log('档位 ' + slot.id + ' 启动 pid=' + proc.pid + ' port=' + slot.port + ' mode=' + mode);
      touchSlot(slot.id);
      if (mode === 'headful') ensureBar(slot).catch(e => log('档 ' + slot.id + ' 常驻录制条没挂上: ' + e.message));
      return { ok: true, port: slot.port, pid: proc.pid, mode };
    }
    if (proc.exitCode !== null) break;
  }
  // 没起来就别留活口：spawn 出去的 chrome 连根杀掉，孤儿会占 profile 锁毒害下一次启动和快照
  await killTree(proc.pid, '调试口没起来');
  throw new Error('档位 ' + slot.id + ' 的 Chrome 起不来（端口 ' + slot.port + '），看 farm.log');
}

function killByPort(port) {
  // 兜底：CDP 关不掉时按端口找 PID 强杀（netstat 输出格式：TCP  x:x:y:y  ...  LISTENING  pid）
  exec('netstat -ano | findstr :' + port + ' | findstr LISTENING', { windowsHide: true }, (err, out) => {
    if (err) return;
    const pids = new Set(out.trim().split('\n').map(l => l.trim().split(/\s+/).pop()).filter(p => /^\d+$/.test(p)));
    for (const pid of pids) {
      exec('taskkill /F /T /PID ' + pid, { windowsHide: true }, e => { if (e) log('taskkill ' + pid + ' 失败: ' + e.message); });
    }
  });
}

// 连根杀：taskkill /T 连子进程一起。proc.kill() 只杀主进程，残孩会攥着 profile 文件锁
// 和端口句柄不放（探针实测：孤儿能把下一次启动拖成 40 秒连环失败、把快照拖成 EPIPE）
function killTree(pid, why) {
  return new Promise(resolve => {
    exec('taskkill /F /T /PID ' + pid, { windowsHide: true }, (e, _o, se) => {
      const s = String(se || '').trim();
      if (e && /没有找到|not found/i.test(s)) { /* 进程已自己退了，无事 */ }
      else if (e) log('连根杀 pid=' + pid + ' 失败: ' + (s || e.message).slice(0, 120));
      else log('连根杀 pid=' + pid + (why ? '（' + why + '）' : ''));
      resolve();
    });
  });
}

// ---------- Chrome 门卫 ----------
// 治的病：别的测试漏收的无头 Chrome（--headless + 数据目录是相对路径/没给/恰好=默认目录）
// 占了日常 Chrome 默认数据目录的单人锁——之后点桌面图标全被转交给它，弹不出窗=「点了没反应」。
// 只杀命令行里带 --headless 且目录落在这三种的；农场档位（路径含 slots）和正经自动化
// （临时绝对路径目录，puppeteer/playwright 都这么起）一概不碰。
const GUARD_MIN = Number(process.env.FARM_CHROME_GUARD_MIN || 5);
// FARM_CHROME_DEFAULT_UDD 只给测试用：把「默认目录」指到沙盒路径，好造活的假小偷夹具
const DEFAULT_UDD = (process.env.FARM_CHROME_DEFAULT_UDD || path.join(os.homedir(), 'AppData\\Local\\Google\\Chrome\\User Data')).toLowerCase();

function listChromeCmdlines() {
  return new Promise(resolve => {
    // 过滤条件里的引号全用 PS 单引号（'' 转义），整条命令外面套双引段——不走 cmd 转义雷区
    exec('powershell -NoProfile -Command "ConvertTo-Json -InputObject @(Get-CimInstance Win32_Process -Filter \'name=\'\'chrome.exe\'\'\' | Select-Object ProcessId,CommandLine) -Compress"',
      { windowsHide: true, timeout: 25000, maxBuffer: 4 * 1024 * 1024 }, (e, out) => {
        if (e) { log('Chrome门卫扫进程失败（本轮跳过）: ' + e.message.slice(0, 120)); return resolve([]); }
        try {
          let arr = String(out).trim() ? JSON.parse(String(out)) : [];
          if (!Array.isArray(arr)) arr = [arr];
          resolve(arr);
        } catch (err) { log('Chrome门卫解析进程清单失败（本轮跳过）: ' + err.message.slice(0, 120)); resolve([]); }
      });
  });
}

async function chromeGuard(why) {
  const procs = await listChromeCmdlines();
  const killed = [];
  for (const p of procs) {
    const cl = String(p.CommandLine || '');
    if (!cl || !cl.includes('--headless')) continue;            // 没命令行读不了/带窗口的正常 Chrome：不碰
    const m = cl.match(/--user-data-dir=(?:"([^"]+)"|([^\s"]+))/);
    const udd = (m && (m[1] || m[2]) || '').replace(/\\/g, '/').toLowerCase();
    if (udd.includes('slots')) continue;                        // 农场档位（含沙盒 test-home 的 slots）：不碰
    if (udd && /^[a-z]:\//.test(udd) && udd !== DEFAULT_UDD.replace(/\\/g, '/')) continue; // 正经自动化的隔离目录：不碰
    // 走到这=小偷三类之一：没给目录 / 相对路径 / 恰好指着默认 User Data
    await killTree(p.ProcessId, 'Chrome门卫' + (why ? '·' + why : '') + '：无头残留占了 Chrome 默认目录的锁，点图标没反应就是它');
    killed.push(p.ProcessId);
  }
  return { ok: true, found: procs.length, killed };
}

if (GUARD_MIN) {
  log('Chrome 门卫开启：每 ' + GUARD_MIN + ' 分钟扫一遍无头残留（FARM_CHROME_GUARD_MIN=0 关）');
  let guarding = false;
  const sweep = async () => {
    if (guarding) return;
    guarding = true;
    try { const r = await chromeGuard('自动巡'); if (r.killed.length) log('Chrome门卫自动巡清掉 ' + r.killed.length + ' 个无头残留'); }
    catch (e) { log('Chrome门卫自动巡出错（下一轮继续）: ' + e.message); }
    finally { guarding = false; }
  };
  const t0 = setTimeout(sweep, 45000); // 开机 45 秒首扫，别拖启动
  if (t0.unref) t0.unref();
  const t = setInterval(sweep, GUARD_MIN * 60000);
  if (t.unref) t.unref();
}

async function stopSlot(slot) {
  closeBar(slot.id); // 常驻录制条跟着档位走，停档一起收
  const was = running.get(slot.id);
  // 先礼后兵：CDP Browser.close 优雅关（让 Chrome 把 profile 落盘），不行再按端口强杀
  try {
    const v = await jget(slot.port, '/json/version', 1500);
    await cdp(v.webSocketDebuggerUrl, 'Browser.close');
  } catch (e) { /* 端口本来就没开，或 CDP 关失败 —— 继续走确认流程 */ }
  if (was && was.proc) { try { was.proc.kill(); } catch (e) {} }
  for (let i = 0; i < 33; i++) {
    await new Promise(r => setTimeout(r, 300));
    if (!(await isAlive(slot))) {
      running.delete(slot.id);
      // 端口关了 ≠ 停干净：Browser.close 优雅关之后主进程还要拖几秒收尾（探针实测 8 秒+），
      // 这几秒里立刻复起，新 chrome 会撞端口占用（bind 报 10048 退到只绑 IPv6，端口检查永远看不见）
      // 和 profile 文件锁——等主进程真退了才算停完
      if (was && was.proc) {
        for (let j = 0; j < 40 && was.proc.exitCode === null && was.proc.signalCode === null; j++) {
          await new Promise(r => setTimeout(r, 300));
        }
        // 优雅关后 12 秒主进程还赖着（卡死的收尾线程）：只杀主进程会留孤儿攥着 profile 锁毒害下次启动，连根杀
        if (was.proc.exitCode === null && was.proc.signalCode === null && was.pid) {
          await killTree(was.pid, '停机收尾超时');
        }
      }
      await new Promise(r => setTimeout(r, 800)); // 等文件锁释放，快照要用
      log('档位 ' + slot.id + ' 已停（端口 ' + slot.port + ' 关闭）');
      return { ok: true };
    }
  }
  killByPort(slot.port);
  for (let i = 0; i < 10; i++) {
    await new Promise(r => setTimeout(r, 500));
    if (!(await isAlive(slot))) { running.delete(slot.id); log('档位 ' + slot.id + ' 强杀成功'); return { ok: true }; }
  }
  throw new Error('档位 ' + slot.id + ' 停不掉，端口 ' + slot.port + ' 还活着');
}

// ---------- 页面操作 ----------
async function ensureRunning(cfg, slot) {
  if (!(await isAlive(slot))) await startSlot(cfg, slot, reviveOpts(slot.id));
}

async function openPage(cfg, slot, url) {
  await ensureRunning(cfg, slot);
  const v = await jget(slot.port, '/json/version', 2000);
  const r = await cdp(v.webSocketDebuggerUrl, 'Target.createTarget', { url: url || 'about:blank' });
  return { ok: true, targetId: r.targetId };
}

function pickPage(list, targetId) {
  const pages = list.filter(t => t.type === 'page');
  if (targetId) {
    const hit = pages.find(p => p.id === targetId || p.targetId === targetId);
    if (hit) return hit;
    throw new Error('找不到目标页 ' + targetId + '，现有页面: ' + pages.map(p => p.id + ' ' + p.url).join(' | '));
  }
  const real = pages.find(p => !p.url.startsWith('devtools://'));
  return real || pages[0];
}

// /json/list 的 title 被 Chrome 预先 HTML 转义过（探针实测：<img> 存的是原文，报出来是 &lt;img&gt;），
// 解码回真身——总管对外只给真数据，怎么转义是展示层（GUI 的 esc / CLI 的纯文本）自己的事。
// 单遍替换只解一层（&amp;amp; → &amp; 不再解），Chrome 转一次我们解一次，正好还原。
function unescapeOnce(s) {
  return String(s == null ? '' : s).replace(/&amp;|&lt;|&gt;|&quot;|&#39;|&apos;/g, c => ({ '&amp;': '&', '&lt;': '<', '&gt;': '>', '&quot;': '"', '&#39;': "'", '&apos;': "'" }[c]));
}

async function evalSlot(cfg, slot, body) {
  await ensureRunning(cfg, slot);
  if (!body || typeof body.code !== 'string') throw new Error('缺 code');
  const list = await jget(slot.port, '/json/list', 2000);
  const page = pickPage(list, body.targetId);
  await cdp(page.webSocketDebuggerUrl, 'Page.enable');
  const r = await cdp(page.webSocketDebuggerUrl, 'Runtime.evaluate',
    { expression: toExpr(body.code), returnByValue: true, awaitPromise: true });
  if (r.exceptionDetails) {
    const d = r.exceptionDetails;
    const detail = d.exception && d.exception.description ? d.exception.description : (d.text || '未知异常');
    return { ok: false, error: detail.split('\n')[0], page: page.url };
  }
  const res = r.result || {};
  return { ok: true, result: res.value !== undefined ? res.value : (res.description || '{' + (res.type || '?') + '}'), page: page.url };
}

// ---------- 页面结构化数据一把抓（og / json-ld / meta）：agent 查页面信息省一次手写 eval ----------
const STRUCT_SRC = [
  // 开头带顶层 return：eval 的 toExpr 会把含 return 的代码包成 (()=>{...})()，
  // 预制脚本自己再套一层 IIFE 的话返回值会被包成悬空语句（实测 {undefined}）
  'return (function(){',
  '  function meta(n){ var el = document.querySelector(\'meta[property="\' + n + \'"], meta[name="\' + n + \'"]\'); return el ? el.content : null; }',
  '  var jsonld = [];',
  '  var nodes = document.querySelectorAll(\'script[type="application/ld+json"]\');',
  '  for (var i = 0; i < nodes.length; i++) {',
  '    try { jsonld.push(JSON.parse(nodes[i].textContent)); }',
  '    catch (e) { jsonld.push({ parseError: String(e).slice(0, 80) }); }', // 坏的 ld+json 不炸整场，带标记端出来
  '  }',
  '  var canon = document.querySelector(\'link[rel=canonical]\');',
  '  return {',
  '    url: location.href, title: document.title, lang: document.documentElement.lang || null,',
  '    description: meta(\'description\'), canonical: canon ? canon.href : null,',
  '    og: { title: meta(\'og:title\'), type: meta(\'og:type\'), image: meta(\'og:image\'), siteName: meta(\'og:site_name\') },',
  '    twitter: { card: meta(\'twitter:card\'), title: meta(\'twitter:title\') },',
  '    jsonld: jsonld,',
  '    counts: { links: document.links.length, images: document.images.length, scripts: document.scripts.length },',
  '  };',
  '})()',
].join('\n');

function structuredSlot(cfg, slot, body) {
  // 就是一条预制的 eval（同一条求值路径，不另起炉灶）
  return evalSlot(cfg, slot, { code: STRUCT_SRC, targetId: body && body.targetId });
}

// ---------- 接口探测：sniff 抓包 + replay 重放（判断"这活能不能转纯后台"） ----------
const sniffs = new Map(); // slotId -> { wss: WebSocket[], records: Map(requestId -> rec), startedAt, seen: Set(targetId), timer }

// 给一个页面挂抓包 WS（Network 是页面级：浏览器级 WS 上开 Network.enable 没用，一页一条）
async function attachSniffPage(slotId, entry, p) {
  entry.seen.add(p.id); // 先记账再连：防轮询器下一拍重复挂同一页
  const ws = new WebSocket(p.webSocketDebuggerUrl);
  await new Promise((resolve, reject) => {
    const t = setTimeout(() => reject(new Error('页面 WS 连不上（5 秒）')), 5000);
    ws.onopen = () => { clearTimeout(t); resolve(); };
    ws.onerror = () => { clearTimeout(t); reject(new Error('页面 WS 连不上')); };
  });
  ws.onmessage = ev => {
    const m = JSON.parse(ev.data);
    if (m.method === 'Network.requestWillBeSent') {
      const r = m.params;
      if (r.type !== 'Fetch' && r.type !== 'XHR') return; // 静态资源/文档不录
      entry.records.set(r.requestId, {
        url: r.request.url, method: r.request.method,
        postData: r.request.postData ? r.request.postData.slice(0, 2000) : null,
        status: null, tsUTC: new Date(r.timestamp * 1000).toISOString().slice(11, 19),
      });
    } else if (m.method === 'Network.responseReceived') {
      const rec = entry.records.get(m.params.requestId);
      if (rec) rec.status = m.params.response.status;
    }
  };
  ws.onclose = () => {
    const i = entry.wss.indexOf(ws);
    if (i >= 0) entry.wss.splice(i, 1);
    if (!entry.wss.length && sniffs.get(slotId) === entry) { // 档位死/停，会话自动清（连轮询器一起收）
      if (entry.timer) clearInterval(entry.timer);
      sniffs.delete(slotId);
    }
  };
  ws.send(JSON.stringify({ id: 1, method: 'Network.enable' }));
  entry.wss.push(ws);
}

// 抓包期间新开的页面自动补挂：录制时人在新 tab 里点的接口也要抓到
function sniffFollow(slot, entry) {
  entry.timer = setInterval(async () => {
    if (sniffs.get(slot.id) !== entry) return clearInterval(entry.timer); // 会话已被收走，轮询器自灭
    let pages;
    try { pages = (await jget(slot.port, '/json/list', 1500)).filter(t => t.type === 'page' && !t.url.startsWith('devtools://')); }
    catch (e) { return; } // 档位正死/重启中，等下一拍
    for (const p of pages) {
      if (entry.seen.has(p.id)) continue;
      try { await attachSniffPage(slot.id, entry, p); log('抓包跟上新页面: ' + p.url.slice(0, 60)); }
      catch (e) { entry.seen.delete(p.id); } // 这拍没挂上下拍再试；页面真没了自然不再出现
    }
  }, 1500);
  if (entry.timer.unref) entry.timer.unref(); // 别吊住进程退出
}

async function sniffStart(slot) {
  if (sniffs.has(slot.id)) return { ok: true, already: true, seconds: Math.round((Date.now() - sniffs.get(slot.id).startedAt) / 1000) };
  if (!(await isAlive(slot))) throw new Error('档位没在跑，先 start');
  const pages = (await jget(slot.port, '/json/list', 2000)).filter(t => t.type === 'page' && !t.url.startsWith('devtools://'));
  if (!pages.length) throw new Error('档位里没有页面，先 open 一个再抓包');
  const entry = { wss: [], records: new Map(), startedAt: Date.now(), seen: new Set(), timer: null };
  for (const p of pages) await attachSniffPage(slot.id, entry, p);
  sniffs.set(slot.id, entry);
  sniffFollow(slot, entry);
  log('档位 ' + slot.id + ' 开始抓包（盯 ' + pages.length + ' 个页面，新开的也自动跟）');
  return { ok: true, sniffing: true, pages: pages.length };
}

async function sniffStop(slot) {
  const s = sniffs.get(slot.id);
  if (!s) throw new Error('这个档没在抓包（先 POST /slot/:id/sniff {"action":"start"}）');
  if (s.timer) clearInterval(s.timer);
  for (const ws of s.wss) { try { ws.close(); } catch (e) {} }
  sniffs.delete(slot.id);
  // 同接口(url+method)合并计数：重复出现的多半是轮询/轮刷数据接口，是转纯后台的好目标
  const merged = new Map();
  for (const r of s.records.values()) {
    const key = r.method + ' ' + r.url;
    const hit = merged.get(key);
    if (hit) { hit.count += 1; hit.status = hit.status || r.status; }
    else merged.set(key, { ...r, count: 1 });
  }
  const requests = [...merged.values()].sort((a, b) => b.count - a.count);
  log('档位 ' + slot.id + ' 停止抓包：' + requests.length + ' 个接口');
  return { ok: true, seconds: Math.round((Date.now() - s.startedAt) / 1000), count: requests.length, requests };
}

async function slotCookieHeader(slot) {
  if (!(await isAlive(slot))) throw new Error('档位没在跑，cookie 拿不到');
  const v = await jget(slot.port, '/json/version', 2000);
  // Network.getAllCookies 已被新版 Chrome 移除，cookie 走 Storage 域
  const r = await cdp(v.webSocketDebuggerUrl, 'Storage.getCookies');
  return r.cookies.map(c => c.name + '=' + c.value).join('; ');
}

async function replaySlot(slot, body) {
  // 带着档位登录态脱离浏览器直发——成功就证明这接口能转纯后台
  if (!body || !body.url) throw new Error('缺 url');
  const u = new URL(body.url);
  const mod = u.protocol === 'https:' ? require('https') : http;
  const cookie = await slotCookieHeader(slot);
  const headers = { ...(body.headers || {}), Cookie: cookie, 'User-Agent': 'farm-replay/0.1' };
  return new Promise((resolve, reject) => {
    const req = mod.request(u, { method: (body.method || 'GET').toUpperCase(), headers, timeout: 15000 }, res => {
      let d = '';
      res.on('data', c => { if (d.length < 4000) d += c; });
      res.on('end', () => resolve({
        ok: true, status: res.statusCode, contentType: res.headers['content-type'] || '',
        cookieSent: cookie.length + ' 字符', body: d.slice(0, 500),
      }));
    });
    req.on('timeout', () => req.destroy(new Error('重放超时（15 秒）')));
    req.on('error', reject);
    if (body.data) req.write(body.data);
    req.end();
  });
}

// ---------- 快照 / 回滚 ----------
// 快照/回滚要停机拷目录：先把档上脚本停了，不然拷完看护又把档拉起来跟重启撞车
function stopScriptsOnSlot(slotId) {
  let n = 0;
  for (const r of scriptRuns.values()) {
    if (r.state === 'running' && r.slotId === slotId) { r.cancel(); r.state = 'stopping'; log('[脚本' + r.scriptId + '] 随档 ' + slotId + ' 一起停止'); n++; }
  }
  return n;
}

async function snapshotSlot(cfg, slot, name) {
  stopScriptsOnSlot(slot.id);
  if (!name || /[\\/:*?"<>|]/.test(name)) throw new Error('快照名缺了或带非法字符: ' + name);
  const wasRunning = await isAlive(slot);
  if (wasRunning) await stopSlot(slot);
  const from = path.join(DATA_DIR, slot.id);
  const to = path.join(SNAP_DIR, slot.id + '-' + name);
  fs.mkdirSync(SNAP_DIR, { recursive: true });
  await storageSettled(from); // 等 localStorage 落盘安静，快照才算数
  await cpProfile(from, to);
  if (wasRunning) await startSlot(cfg, slot, reviveOpts(slot.id));
  return { ok: true, snapshot: to, sizeMB: Math.round(fs.statSync(to).size / 1048576 * 10) / 10 };
}

async function restoreSlot(cfg, slot, name) {
  const from = path.join(SNAP_DIR, slot.id + '-' + name);
  if (!fs.existsSync(from)) throw new Error('没这个快照: ' + name);
  stopScriptsOnSlot(slot.id); // 回滚同样停机拷目录，先把脚本停了防看护抢跑
  const wasRunning = await isAlive(slot);
  if (wasRunning) await stopSlot(slot);
  const to = path.join(DATA_DIR, slot.id);
  await rmDir(to);
  fs.cpSync(from, to, { recursive: true });
  if (wasRunning) await startSlot(cfg, slot, reviveOpts(slot.id));
  return { ok: true, restored: name };
}

// ---------- 脚本任务（挂总管后台，关终端也跑） ----------
const scriptRuns = new Map(); // scriptId -> { scriptId, slotId, state: running|stopping|done|error, lastMsg, result, error, startedAt, cancel }

function scriptRunSnapshot(r) {
  return { scriptId: r.scriptId, slotId: r.slotId, state: r.state, lastMsg: r.lastMsg, result: r.result, error: r.error, startedAt: r.startedAt };
}

async function startScriptTask(cfg, scriptId, body) {
  const sc = scripter.loadScript(scriptId);
  const prev = scriptRuns.get(sc.id);
  if (prev && (prev.state === 'running' || prev.state === 'stopping')) {
    throw new Error('脚本 ' + sc.id + ' 还在跑（' + prev.state + '），先 stop');
  }
  // 档位回退链：请求显式给的档 > 脚本绑定的档。都没有=人话报错（不给绑错号的机会）
  const slotId = String(body.slot || sc.bindSlot || '');
  if (!slotId) throw new Error('没说在哪个档跑：请求带 slot，或先绑定（POST /script/' + sc.id + '/bind / farm.js bind ' + sc.id + ' 档位id）');
  const slot = getSlot(cfg, slotId);
  await ensureRunning(cfg, slot);
  touchSlot(slot.id); // 起脚本算一次活动；运行中靠空闲巡检的 busySlots 豁免
  let stopped = false;
  const run = { scriptId: sc.id, slotId: slot.id, state: 'running', lastMsg: '', result: null, error: null, startedAt: new Date().toISOString() };
  run.cancel = () => { stopped = true; };
  scriptRuns.set(sc.id, run);
  const opts = {
    port: slot.port, targetId: body.targetId,
    loop: body.loop, once: body.once, dry: body.dry, timeoutMs: body.timeoutMs,
    onLog: msg => { run.lastMsg = msg; log('[脚本' + sc.id + '@档' + slot.id + '] ' + msg); },
  };
  (async () => {
    try {
      run.result = await scripter.runScript(sc, opts, () => stopped);
      run.state = 'done';
    } catch (e) {
      run.state = 'error'; run.error = e.message;
      log('[脚本' + sc.id + '] 出错: ' + e.message);
    }
    log('[脚本' + sc.id + '] 结束 state=' + run.state);
  })();
  return { ok: true, ...scriptRunSnapshot(run) };
}

// ---------- 常驻录制条会话 + 录制会话 ----------
// 有窗口（headful）的档，浏览器里每个页面右下角自带录制条（平时「● 开始录制」）。
// 条上按钮和 GUI/CLI 走同一条 record 路由；一次只录一场（录制要在看得见的窗口里点，多场人自己也分不清）。
const barSessions = new Map(); // slotId -> 常驻条会话
const barPending = new Set();  // 正在建会话的档，防 /slots 轮询触发重复建
async function ensureBar(slot) {
  const had = barSessions.get(slot.id);
  if (had && !had.dead) return had;
  if (barPending.has(slot.id)) {
    for (let i = 0; i < 100; i++) { // 等在建的那份（最多 10s）
      await sleep(100);
      const s = barSessions.get(slot.id);
      if (s && !s.dead) return s;
    }
    throw new Error('档 ' + slot.id + ' 常驻录制条会话起不来');
  }
  barPending.add(slot.id);
  try {
    const s = await scripter.barSession(slot.port, {
      label: '档' + slot.id + (slot.note ? '·' + String(slot.note).slice(0, 10) : ''), // 页面里的标识：条左端小标+标题后缀
      onCmd: async cmd => {
        // 条上「● 开始录制」/命名框「存」「不存」：与 GUI/CLI 同一条路；对面先停了就吃个"没在录制"，无害
        // 消息两代并存：旧窗口页发纯 "start"/"stop"；新版条停止带名字/丢弃 {"cmd":"stop","name":"xx","discard":true}
        let op = cmd, name, discard = false, asAgent = false;
        if (typeof cmd === 'string' && cmd.startsWith('{')) {
          try { const m = JSON.parse(cmd); if (m && m.cmd === 'stop') { op = 'stop'; name = m.name; discard = !!m.discard; asAgent = !!m.asAgent; } }
          catch (e) { /* 解析不动当没这个名字，走下面的纯 stop 分支 */ }
        }
        try {
          if (op === 'start') await recordStart(loadCfg(), slot, {});
          else if (op === 'stop') await recordStop(slot, name, discard, asAgent);
        } catch (e) {
          log('窗口里' + (op === 'start' ? '开始录制' : '停止保存') + '失败: ' + e.message);
          // 停止失败（比如"没在录制"）要把条从命名态捞回来，不然卡在"存"上回不去
          if (op !== 'start') { try { barSessions.get(slot.id).stopRec(); } catch (e2) {} }
        }
      },
    });
    barSessions.set(slot.id, s);
    log('档 ' + slot.id + ' 常驻录制条就位（' + s.pages.size + ' 页）');
    return s;
  } finally { barPending.delete(slot.id); }
}
function closeBar(id) {
  const s = barSessions.get(id);
  if (s) { s.close(); barSessions.delete(id); }
}

let recSession = null; // { slotId, bar, startedAt, name }——bar 是常驻条会话，停录不关它
let lastRec = null;    // 上一场收工存了什么（CLI record 轮询 /slots 用它确认窗口里停的那场真存了盘）

// 浏览器死了（手动关窗/闪退/被杀）录制没法继续：立刻收会话，别让 GUI 红条和 CLI 轮询永远挂着
function abortRec(slotId, why) {
  if (!recSession || recSession.slotId !== slotId) return;
  const cnt = (recSession.bar && Array.isArray(recSession.bar.steps)) ? recSession.bar.steps.length : 0;
  recSession = null;
  lastRec = { aborted: true, slotId, count: cnt, at: Date.now() };
  log('档 ' + slotId + ' ' + why + '，录制中止没保存（已录 ' + cnt + ' 步）');
}

async function recordStart(cfg, slot, body) {
  if (recSession) throw new Error('已经在录档 ' + recSession.slotId + '，先停止并保存再录下一场');
  for (const r of scriptRuns.values()) {
    if (r.state === 'running' && r.slotId === slot.id) throw new Error('档 ' + slot.id + ' 有脚本在跑，先停脚本再录');
  }
  const run = running.get(slot.id);
  if (!(await isAlive(slot)) || !run || run.mode !== 'headful') {
    if (await isAlive(slot)) await stopSlot(slot);
    await startSlot(cfg, slot, { mode: 'headful' }); // 录制要点得着真窗口（startSlot 顺手挂常驻条）
  }
  touchSlot(slot.id);
  const name = ((body && body.name ? String(body.name) : '').trim())
    || ('档' + slot.id + ' ' + new Date().toTimeString().slice(0, 5)); // 没给名=档号+时刻，窗口里直接开录就是它
  const bar = await ensureBar(slot);
  bar.startRec();
  let sniffOurs = false;
  if (!sniffs.has(slot.id)) { // 录制自动带接口记录：录完脚本里就有「点了什么+背后发了什么请求」，agent 拿一个文件看懂全链路
    try { await sniffStart(slot); sniffOurs = true; }
    catch (e) { log('档 ' + slot.id + ' 录制自动抓包没开成（不影响录制）: ' + e.message); }
  }
  recSession = { slotId: slot.id, bar, startedAt: new Date().toISOString(), name, sniffOurs };
  log('档 ' + slot.id + ' 开始录制「' + name + '」（窗口右下角条已变录制中' + (sniffOurs ? '，接口也抓着' : '') + '）');
  return { ok: true, slotId: slot.id, pages: bar.pages.size };
}

// 录制自己开的抓包收摊（人手动开的不动）；返回接口清单，收不成返回 null 不拦录制收工
async function stopOursSniff(slot) {
  try { return (await sniffStop(slot)).requests; }
  catch (e) { log('录制抓包收摊失败（这场的接口清单没存上）: ' + e.message); return null; }
}

async function recordStop(slot, name, discard, asAgent) {
  if (!recSession) throw new Error('没在录制');
  if (recSession.slotId !== slot.id) throw new Error('在录的是档 ' + recSession.slotId + '，不是 ' + slot.id);
  let steps;
  try { steps = recSession.bar.stopRec(); } // 条弹回「● 开始录制」，常驻会话留着
  catch (e) { // 条没响应（页面关了/条会话死了）：会话立刻作废，不能永久卡死
    abortRec(slot.id, '录制条没响应');
    throw new Error('录制条没响应（页面可能关了），这场没收成: ' + e.message);
  }
  const nm = ((name && String(name).trim()) || recSession.name || '').trim() || '未命名'; // 停止时带名字优先，没带用开录时存的
  const count = steps.length;
  const sniffOurs = recSession.sniffOurs;
  recSession = null;
  const apis = sniffOurs ? await stopOursSniff(slot) : null; // 存不存都先收摊自己开的抓包（丢弃/空场不留尾巴）
  if (discard) { // 不存：整场扔掉，不落文件（一步没录到也走这里，安静回平时态）
    lastRec = { discarded: true, slotId: slot.id, count, at: Date.now() };
    log('档 ' + slot.id + ' 录制丢弃 ' + count + ' 步（点了不存，没保存）');
    return { ok: true, discarded: true, count };
  }
  if (!count) throw new Error('一步没录到，没保存（去档 ' + slot.id + ' 的窗口里点几下再停）');
  if (asAgent) { // 存 Agent 笔记：不建脚本，落 agent-notes/ 一份 md 给 agent 直接读（发它或让它自己来读都行）
    const note = scripter.saveAgentNote(path.join(HOME, 'agent-notes'), nm, { slotId: slot.id, note: slot.note }, steps, apis);
    lastRec = { agentNote: path.basename(note), slotId: slot.id, name: nm, count, at: Date.now() };
    log('档 ' + slot.id + ' 录制收工 ' + count + ' 步 → Agent 笔记 ' + note + (apis ? '（带 ' + apis.length + ' 个接口记录）' : '') + '，没建脚本');
    return { ok: true, agentNote: note, count };
  }
  const sc = {
    id: scripter.nextId(), name: nm, type: 'loop',
    steps: steps.map(s => ({ selector: s.selector, text: s.text, tag: s.tag, href: s.href || null })), // href=录的时候点的哪个页，跑时没这页就自动开回来
    loop: 0, delayMs: 1200, jitterMs: 800, clickJitter: 0.4,
    created: new Date().toISOString(),
    apis: apis || undefined, // 录制期间抓到的接口（url/方法/状态/次数/入参），给 agent 判断哪步能转纯后台
  };
  scripter.saveScript(sc);
  lastRec = { scriptId: sc.id, slotId: slot.id, name: sc.name, count, at: Date.now() };
  log('档 ' + slot.id + ' 录制收工 ' + count + ' 步 → 脚本 ' + sc.id + ' ' + sc.name + (apis ? '（带 ' + apis.length + ' 个接口记录）' : ''));
  return { ok: true, script: sc, count };
}

// ---------- HTTP API ----------
function readBody(req) {
  return new Promise((resolve, reject) => {
    let d = '';
    req.on('data', c => { d += c; if (d.length > 10 * 1024 * 1024) req.destroy(new Error('body 超 10MB')); });
    req.on('end', () => { try { resolve(d ? JSON.parse(d) : {}); } catch (e) { reject(new Error('body 不是合法 JSON')); } });
    req.on('error', reject);
  });
}

function send(res, code, obj) {
  const s = JSON.stringify(obj);
  res.writeHead(code, { 'Content-Type': 'application/json; charset=utf-8' });
  res.end(s);
}

function getSlot(cfg, id) {
  const s = cfg.slots.find(x => x.id === id);
  if (!s) throw new Error('没这个档位: ' + id + '（先 POST /slots/add）');
  return s;
}

const server = http.createServer(async (req, res) => {
  try {
    const u = new URL(req.url, 'http://127.0.0.1');
    const cfg = loadCfg();
    if (req.method === 'GET' && u.pathname === '/health') return send(res, 200, { ok: true });
    // 人的界面：每次读盘，改 gui.html 不用重启总管。
    // 读 __dirname 不是 HOME：gui.html 是程序本体不是数据，FARM_HOME 指到别处（沙盒/多实例）页面不能跟着丢
    if (req.method === 'GET' && u.pathname === '/gui') {
      try {
        const html = fs.readFileSync(path.join(__dirname, 'gui.html'));
        res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8' });
        return res.end(html);
      } catch (e) {
        return send(res, 500, { ok: false, error: 'gui.html 读不了: ' + e.message });
      }
    }
    if (req.method === 'GET' && (u.pathname === '/' || u.pathname === '/slots')) {
      // 并行探测：串行最坏一档拖满 900ms 全场陪等，GUI 3 秒一轮心跳伤不起
      const alives = await Promise.all(cfg.slots.map(s => isAlive(s)));
      const aliveNow = new Map(cfg.slots.map((s, i) => [s.id, alives[i]]));
      const list = cfg.slots.map(s => ({ ...s, alive: aliveNow.get(s.id), mode: (running.get(s.id) || {}).mode || null, lastUsed: lastUsed.get(s.id) || null }));
      // 领养的档（总管重启接手的）没有进程看护，浏览器死了靠这 3s 心跳把录制会话收掉
      if (recSession && !aliveNow.get(recSession.slotId)) abortRec(recSession.slotId, '浏览器没了');
      // 有窗口的活档顺手确保常驻条在（总管重启/条会话自收后靠这里补挂，GUI 3s 一轮就是心跳）
      for (const s of cfg.slots) {
        const run = running.get(s.id);
        if (run && run.mode === 'headful' && aliveNow.get(s.id)) ensureBar(s).catch(e => log('档 ' + s.id + ' 常驻录制条没挂上: ' + e.message));
      }
      return send(res, 200, {
        ok: true, supervisorPort: PORT, idleStopMin: IDLE_MIN, slots: list,
        recording: recSession ? { slotId: recSession.slotId, count: recSession.bar.steps.length, startedAt: recSession.startedAt } : null,
        lastRec,
      });
    }
    let m = u.pathname.match(/^\/slot\/([^/]+)$/);
    if (m && req.method === 'GET') {
      const slot = getSlot(cfg, m[1]);
      touchSlot(slot.id); // 查详情也算活动（GUI 详情轮询/agent 心跳都靠它续命）
      const alive = await isAlive(slot);
      let targets = [];
      if (alive) {
        try { targets = (await jget(slot.port, '/json/list', 1500))
          .filter(t => t.type === 'page').map(t => ({ targetId: t.id, url: t.url, title: unescapeOnce(t.title) })); } catch (e) {}
        const run = running.get(slot.id);
        if (run && run.mode === 'headful') ensureBar(slot).catch(() => {}); // 详情查询顺手补挂常驻条（与 /slots 同一套自愈）
      }
      return send(res, 200, { ok: true, ...slot, alive, mode: (running.get(slot.id) || {}).mode || null, targets });
    }
    // 当前页截图：GUI 详情里直接看画面（脚本跑得对不对一眼看到）。故意不 touchSlot——
    // 光看截图不算操作，别让开着的详情面板把空闲自动停废了
    m = u.pathname.match(/^\/slot\/([^/]+)\/shot$/);
    if (m && req.method === 'GET') {
      const slot = getSlot(cfg, m[1]);
      if (!(await isAlive(slot))) return send(res, 503, { ok: false, error: '档位没在跑' });
      const list = await jget(slot.port, '/json/list', 2000);
      const page = pickPage(list);
      const r = await cdp(page.webSocketDebuggerUrl, 'Page.captureScreenshot', { format: 'jpeg', quality: 70 });
      const buf = Buffer.from(r.data, 'base64');
      res.writeHead(200, { 'Content-Type': 'image/jpeg', 'Content-Length': buf.length, 'Cache-Control': 'no-store' });
      return res.end(buf);
    }
    // 快照列表：GUI 回滚下拉用（名字 = 目录名去掉 "档位id-" 前缀，时间取目录 mtime）
    m = u.pathname.match(/^\/slot\/([^/]+)\/snapshots$/);
    if (m && req.method === 'GET') {
      const slot = getSlot(cfg, m[1]);
      const pre = slot.id + '-';
      let snaps = [];
      try {
        snaps = fs.readdirSync(SNAP_DIR)
          .filter(n => n.startsWith(pre))
          .map(n => ({ name: n.slice(pre.length), at: Math.round(fs.statSync(path.join(SNAP_DIR, n)).mtimeMs) }))
          .sort((a, b) => b.at - a.at);
      } catch (e) { /* 目录还没有 = 一个快照没拍过，返回空列表 */ }
      return send(res, 200, { ok: true, snapshots: snaps });
    }
    if (req.method === 'POST' && u.pathname === '/slots/add') {
      const body = await readBody(req);
      const id = String(cfg.nextId).padStart(2, '0');
      cfg.nextId += 1;
      const slot = { id, port: cfg.nextPort, note: body.note || '', blockImages: body.blockImages !== false };
      cfg.nextPort += 1;
      cfg.slots.push(slot);
      saveCfg(cfg);
      log('登记档位 ' + id + ' port=' + slot.port + ' note=' + slot.note);
      return send(res, 200, { ok: true, slot });
    }
    m = u.pathname.match(/^\/slot\/([^/]+)\/([a-z]+)$/);
    if (m && req.method === 'POST') {
      const slot = getSlot(cfg, m[1]);
      if (m[2] !== 'stop' && m[2] !== 'halt') touchSlot(slot.id); // 对这个档做事=活动；stop/halt 不用续命
      const body = await readBody(req);
      const act = m[2];
      if (act === 'start') return send(res, 200, { ok: true, ...(await startSlot(cfg, slot, body)) });
      if (act === 'stop') return send(res, 200, await stopSlot(slot));
      if (act === 'halt') { // 真停：连档上跑着的脚本一起。stop 只是停浏览器（切窗口/后台还用它，脚本靠重连窗活）
        const stopped = stopScriptsOnSlot(slot.id);
        return send(res, 200, { ok: true, stoppedScripts: stopped, ...(await stopSlot(slot)) });
      }
      if (act === 'restart') { if (await isAlive(slot)) await stopSlot(slot); return send(res, 200, { ok: true, ...(await startSlot(cfg, slot, body)) }); }
      if (act === 'open') return send(res, 200, await openPage(cfg, slot, body.url));
      if (act === 'eval') return send(res, 200, await evalSlot(cfg, slot, body));
      if (act === 'structured') return send(res, 200, await structuredSlot(cfg, slot, body));
      if (act === 'snapshot') return send(res, 200, await snapshotSlot(cfg, slot, body.name));
      if (act === 'sniff') {
        const action = body.action || 'start';
        if (action === 'start') return send(res, 200, await sniffStart(slot));
        if (action === 'stop') return send(res, 200, await sniffStop(slot));
        throw new Error('sniff 的 action 只认 start/stop');
      }
      if (act === 'replay') return send(res, 200, await replaySlot(slot, body));
      if (act === 'record') {
        const action = body.action || 'start';
        if (action === 'start') return send(res, 200, await recordStart(cfg, slot, body));
        if (action === 'stop') return send(res, 200, await recordStop(slot, body.name, !!body.discard, !!body.asAgent));
        throw new Error('record 的 action 只认 start/stop');
      }
      if (act === 'restore') return send(res, 200, await restoreSlot(cfg, slot, body.name));
      if (act === 'remove') {
        stopScriptsOnSlot(slot.id); // 不停的话看护会按 cfg 找不到档跳过，但脚本会干等满 90 秒才收场，先停干脆
        if (await isAlive(slot)) await stopSlot(slot);
        cfg.slots = cfg.slots.filter(x => x.id !== slot.id);
        saveCfg(cfg);
        let wiped = false;
        if (body.wipe) { await rmDir(path.join(DATA_DIR, slot.id)); wiped = true; }
        log('移除档位 ' + slot.id + (wiped ? '（连数据一起删）' : '（数据目录保留）'));
        return send(res, 200, { ok: true, wiped });
      }
      return send(res, 404, { ok: false, error: '不认识的动作: ' + act });
    }
    // ---- 脚本任务 ----
    // Chrome 门卫手动口：桌面 Chrome 点不开时一条命令清无头残留（总管也每 5 分钟自动扫）
    if (req.method === 'POST' && u.pathname === '/chrome/fix') {
      return send(res, 200, await chromeGuard('手动'));
    }
    if (req.method === 'GET' && u.pathname === '/scripts') {
      const runs = {};
      for (const [sid, r] of scriptRuns) runs[sid] = scriptRunSnapshot(r);
      return send(res, 200, { ok: true, scripts: scripter.listScripts(), runs });
    }
    m = u.pathname.match(/^\/script\/([^/]+)\/start$/);
    if (m && req.method === 'POST') {
      const body = await readBody(req);
      return send(res, 200, await startScriptTask(cfg, m[1], body));
    }
    m = u.pathname.match(/^\/script\/([^/]+)\/stop$/);
    if (m && req.method === 'POST') {
      const run = scriptRuns.get(m[1]);
      if (!run) throw new Error('脚本 ' + m[1] + ' 没有跑过');
      if (run.state === 'running') { run.cancel(); run.state = 'stopping'; log('[脚本' + m[1] + '] 收到停止信号'); }
      return send(res, 200, { ok: true, ...scriptRunSnapshot(run) });
    }
    m = u.pathname.match(/^\/script\/([^/]+)\/status$/);
    if (m && req.method === 'GET') {
      const run = scriptRuns.get(m[1]);
      if (!run) throw new Error('脚本 ' + m[1] + ' 没有跑过');
      return send(res, 200, { ok: true, ...scriptRunSnapshot(run) });
    }
    m = u.pathname.match(/^\/script\/([^/]+)\/delete$/);
    if (m && req.method === 'POST') {
      const run = scriptRuns.get(m[1]);
      if (run && run.state === 'running') throw new Error('脚本 ' + m[1] + ' 还在跑，先停了再删');
      const file = scripter.deleteScript(m[1]);
      scriptRuns.delete(m[1]); // 连台账一起清，GUI 不再挂着旧出错状态
      log('删除脚本 ' + m[1] + ': ' + path.basename(file));
      return send(res, 200, { ok: true, deleted: path.basename(file) });
    }
    // ---- 绑定/解绑：skill 跟档位（=端口+登录态）绑死，启动不用再选档 ----
    m = u.pathname.match(/^\/script\/([^/]+)\/bind$/);
    if (m && req.method === 'POST') {
      const body = await readBody(req);
      const sc = scripter.loadScript(m[1]);
      if (body.slot !== undefined || body.desc !== undefined) {
        if (body.slot !== undefined) {
          const b = String(body.slot || '').trim();
          if (!b) delete sc.bindSlot; // 空串=解绑
          else { getSlot(cfg, b); sc.bindSlot = b; } // 没这个档会抛人话错，绑不上去
        }
        if (body.desc !== undefined) {
          const d = String(body.desc || '').trim().slice(0, 120);
          if (d) sc.desc = d; else delete sc.desc;
        }
        scripter.saveScript(sc);
        log('脚本 ' + sc.id + ' ' + (sc.bindSlot ? '绑到档 ' + sc.bindSlot : '解绑'));
      }
      return send(res, 200, { ok: true, bindSlot: sc.bindSlot || null, desc: sc.desc || '' });
    }
    // ---- agent 写脚本：交一份步骤 json，校验落盘自动编号，跟人录的同待遇 ----
    if (req.method === 'POST' && u.pathname === '/script/new') {
      const body = await readBody(req);
      if (!body || typeof body !== 'object') throw new Error('body 要是脚本 json（steps 数组或 watch 对象）');
      const sc = { ...body, name: String(body.name || '').trim() || 'agent脚本', created: new Date().toISOString() };
      delete sc.id; // 编号永远农场发（nextId），不给覆盖已有脚本的机会
      sc.type = body.type === 'watch' || (!body.steps && body.watch) ? 'watch' : 'loop';
      const bad = []; // 坏数据早炸：一样不对就拒收，不落半个脚本
      // 绑定档位 + 一句话说明（skill 化字段）：档位必须真存在，别绑个空号留到启动时才炸
      if (sc.bindSlot !== undefined && sc.bindSlot !== null && String(sc.bindSlot) !== '') {
        const b = String(sc.bindSlot);
        if (!cfg.slots.some(x => x.id === b)) bad.push('bindSlot 没这个档位: ' + b + '（先 POST /slots/add）');
        else sc.bindSlot = b;
      } else delete sc.bindSlot;
      sc.desc = String(sc.desc || '').trim().slice(0, 120); // 说明截 120 字，GUI 卡上就一行
      if (!sc.desc) delete sc.desc;
      if (sc.type === 'watch') {
        const w = sc.watch;
        if (!w || typeof w !== 'object') bad.push('watch 脚本要带 watch 对象');
        else {
          for (const k of ['rowText', 'columnHeader', 'value', 'clickText']) if (w[k] === undefined || String(w[k]) === '') bad.push('watch 缺 ' + k);
          if (w.op !== undefined && !['>', '>=', '<', '<='].includes(w.op)) bad.push('watch.op 只认 > >= < <=');
        }
      } else {
        if (!Array.isArray(sc.steps) || sc.steps.length === 0) bad.push('steps 要非空数组');
        else sc.steps.forEach((st, i) => { if (!st || typeof st !== 'object' || (!String(st.selector || '') && !String(st.text || ''))) bad.push('步骤' + (i + 1) + ' 要有 selector 或 text（先 open+eval 看清页面再写）'); });
        if (sc.loop !== undefined && !(Number.isFinite(Number(sc.loop)) && Number(sc.loop) >= 0)) bad.push('loop 要是 >=0 的数（0=无限循环）');
      }
      if (bad.length) return send(res, 400, { ok: false, error: '脚本没过校验：' + bad.join('；') });
      const id = scripter.nextId();
      const file = scripter.saveScript({ ...sc, id });
      log('新脚本 ' + id + '（写的）: ' + sc.name);
      return send(res, 200, { ok: true, id, file: path.basename(file) });
    }
    // ---- 配置搬家：档位登记+全部脚本打成一份 json，另一台电脑导入即用（登录态不跟走，另登一次） ----
    if (req.method === 'GET' && u.pathname === '/config/export') {
      const payload = {
        farm: 'browser-farm', version: '0.1.19', exportedAt: new Date().toISOString(),
        slots: cfg.slots.map(s => ({ id: s.id, note: s.note || '', port: s.port, blockImages: s.blockImages !== false })), // id 带上：导入时脚本的 bindSlot 才能对回新档位号
        scripts: scripter.listScripts(),
      };
      log('导出配置：' + payload.slots.length + ' 档 ' + payload.scripts.length + ' 脚本');
      return send(res, 200, { ok: true, payload, summary: payload.slots.length + ' 档 ' + payload.scripts.length + ' 脚本' });
    }
    if (req.method === 'POST' && u.pathname === '/config/import') {
      const body = await readBody(req);
      if (!body || !Array.isArray(body.scripts) || body.farm !== 'browser-farm') {
        throw new Error('这不是农场配置文件（要 GUI「导出配置」或 farm.js export 出来的 json）');
      }
      const existIds = new Set(scripter.listScripts().map(s => s.id));
      let addedScripts = 0, renamedScripts = 0, addedSlots = 0, skippedSlots = 0, droppedBinds = 0;
      const slotIdMap = new Map(); // 旧档位号 -> 新档位号：搬过去的档位编号会变，绑定要跟着重指
      for (const inc of (Array.isArray(body.slots) ? body.slots : [])) {
        if (!inc || typeof inc.port !== 'number' || cfg.slots.some(x => x.port === inc.port)) { skippedSlots += 1; continue; }
        const id = String(cfg.nextId).padStart(2, '0');
        cfg.nextId += 1;
        cfg.slots.push({ id, port: inc.port, note: String(inc.note || ''), blockImages: inc.blockImages !== false });
        if (inc.port >= cfg.nextPort) cfg.nextPort = inc.port + 1; // 后面登记新档别跟导入的端口撞车
        if (inc.id) slotIdMap.set(String(inc.id), id);
        addedSlots += 1;
      }
      if (addedSlots) saveCfg(cfg);
      for (const sc of body.scripts) {
        if (!sc || !(Array.isArray(sc.steps) || sc.watch)) continue; // 坏条目跳过不炸整场导入
        let id = String(sc.id || '');
        if (!id || existIds.has(id)) { id = scripter.nextId(); renamedScripts += 1; } // 编号被占：自动取新号，不覆盖已有脚本
        existIds.add(id);
        if (sc.bindSlot) { // 绑定重指：老配置的档位号在新机对不上的，宁可摘绑别绑错账号
          const bound = slotIdMap.get(String(sc.bindSlot)) || (cfg.slots.some(x => x.id === String(sc.bindSlot)) ? String(sc.bindSlot) : '');
          if (bound) sc.bindSlot = bound;
          else { delete sc.bindSlot; droppedBinds += 1; }
        }
        scripter.saveScript({ ...sc, id });
        addedScripts += 1;
      }
      log('导入配置：脚本 +' + addedScripts + (renamedScripts ? '（' + renamedScripts + ' 个改号）' : '') + '，档位 +' + addedSlots + (skippedSlots ? '（' + skippedSlots + ' 个端口被占跳过）' : '') + (droppedBinds ? '，' + droppedBinds + ' 个绑定对不上档位已摘绑' : ''));
      return send(res, 200, { ok: true, addedScripts, renamedScripts, addedSlots, skippedSlots, droppedBinds });
    }
    return send(res, 404, { ok: false, error: '路由不存在: ' + req.method + ' ' + u.pathname });
  } catch (e) {
    log('API 出错: ' + e.message);
    return send(res, 400, { ok: false, error: e.message });
  }
});

server.listen(PORT, '127.0.0.1', () => {
  fs.mkdirSync(DATA_DIR, { recursive: true });
  fs.mkdirSync(SNAP_DIR, { recursive: true });
  if (!fs.existsSync(SLOTS_FILE)) saveCfg(loadCfg());
  log('总管就绪 http://127.0.0.1:' + PORT + '（档位数据在 ' + DATA_DIR + '）');
});

// 总管自己退出不带走档位：Chrome 留着继续跑，下次起总管自动接管（adopt）
process.on('SIGINT', () => { log('总管退出（档位不动的，要停用 /slot/:id/stop）'); process.exit(0); });
