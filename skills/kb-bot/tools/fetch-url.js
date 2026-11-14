#!/usr/bin/env node
// kb-bot 抓取工具：本地 Chrome/Edge CDP 渲染后取 SPA 页面正文+链接（curl/静态抓取拿不到的用它）。零依赖。
// 原理：起一个带独立档案的 Chrome，CDP 真时钟导航，等正文长度连续两次采样不变（渲染稳定）再取数。
// 用法：
//   node tools/fetch-url.js "<url>" [--wait=20000] [--profile=<dir>] [--headful] [--headful-login]
//   --headful        有头模式跑（headless 被识别成机器人时的后手）
//   --headful-login  开真窗口真人登录，回车后自动用同一 profile 抓取（profile 持久化，下次免登）
// 注意：同一 profile 不能同时开两个 Chrome 实例，抓取前先关掉用该 profile 的窗口。
'use strict';
const { spawn, spawnSync } = require('child_process');
const net = require('net');
const fs = require('fs');
const os = require('os');
const path = require('path');

const CANDIDATES = [
  process.env.CHROME_PATH,
  path.join(process.env.ProgramFiles || '', 'Google/Chrome/Application/chrome.exe'),
  path.join(process.env['ProgramFiles(x86)'] || '', 'Google/Chrome/Application/chrome.exe'),
  path.join(process.env.LOCALAPPDATA || '', 'Google/Chrome/Application/chrome.exe'),
  path.join(process.env.ProgramFiles || '', 'Microsoft/Edge/Application/msedge.exe'),
  path.join(process.env['ProgramFiles(x86)'] || '', 'Microsoft/Edge/Application/msedge.exe'),
].filter(Boolean);

function findBrowser() {
  for (const p of CANDIDATES) if (fs.existsSync(p)) return p;
  console.error('找不到 Chrome/Edge，设 CHROME_PATH 环境变量指定浏览器路径');
  process.exit(2);
}
function freePort() {
  return new Promise((resolve, reject) => {
    const srv = net.createServer();
    srv.listen(0, '127.0.0.1', () => { const p = srv.address().port; srv.close(() => resolve(p)); });
    srv.on('error', reject);
  });
}
const sleep = ms => new Promise(r => setTimeout(r, ms));

class Cdp {
  constructor(ws) { this.ws = ws; this.id = 0; this.pending = new Map(); this.listeners = []; }
  static async connect(url) {
    const ws = new WebSocket(url);
    await new Promise((res, rej) => { ws.addEventListener('open', res); ws.addEventListener('error', rej); });
    const c = new Cdp(ws);
    ws.addEventListener('message', ev => c._onMsg(String(ev.data)));
    ws.addEventListener('close', () => c.pending.forEach(p => p.reject(new Error('CDP 连接断开'))));
    return c;
  }
  _onMsg(raw) {
    const m = JSON.parse(raw);
    if (m.id && this.pending.has(m.id)) {
      const { res, rej } = this.pending.get(m.id);
      this.pending.delete(m.id);
      m.error ? rej(new Error(m.error.message)) : res(m.result);
    } else {
      this.listeners.forEach(fn => fn(m));
    }
  }
  send(method, params = {}, sessionId) {
    const id = ++this.id;
    const msg = { id, method, params };
    if (sessionId) msg.sessionId = sessionId;
    this.ws.send(JSON.stringify(msg));
    return new Promise((res, rej) => this.pending.set(id, { res, rej }));
  }
  once(method, sessionId) {
    return new Promise(res => {
      const fn = m => {
        if (m.method === method && (!sessionId || m.sessionId === sessionId)) {
          this.listeners = this.listeners.filter(x => x !== fn);
          res(m.params);
        }
      };
      this.listeners.push(fn);
    });
  }
  close() { try { this.ws.close(); } catch (e) { /* 关闭失败不致命，进程退出兜底 */ } }
}

const EVAL_SNAPSHOT = `(() => {
  const text = document.body ? document.body.innerText : '';
  const links = [...document.querySelectorAll('a')].slice(0, 300)
    .map(a => ({ t: (a.innerText || '').trim().slice(0, 60), h: a.href }))
    .filter(x => x.t && x.h && x.h.startsWith('http'));
  return JSON.stringify({ title: document.title, url: location.href, text: text.slice(0, 20000), textLen: text.length, links });
})()`;

async function main() {
  const args = process.argv.slice(2);
  const url = args.find(a => !a.startsWith('--'));
  if (!url) {
    console.error('用法：node tools/fetch-url.js "<url>" [--wait=20000] [--profile=<dir>] [--headful] [--headful-login]');
    process.exit(2);
  }
  const waitArg = args.find(a => a.startsWith('--wait='));
  const deadline = waitArg ? parseInt(waitArg.slice(7), 10) : 20000;
  const profileArg = args.find(a => a.startsWith('--profile='));
  const profile = profileArg ? profileArg.slice(10) : path.join(os.tmpdir(), 'kb-bot-chrome-profile');
  const browserPath = findBrowser();
  fs.mkdirSync(profile, { recursive: true });

  if (args.includes('--headful-login')) {
    console.log('开真窗口（profile=' + profile + '）。登录完成后回到这里按回车，自动用同一 profile 抓取…');
    spawn(browserPath, ['--user-data-dir=' + profile, '--no-first-run', url], { stdio: 'ignore' });
    await new Promise(res => process.stdin.once('data', res));
    await sleep(1500);
  }

  const port = await freePort();
  const flags = [
    args.includes('--headful') ? '--window-size=1280,900' : '--headless=new',
    '--disable-gpu', '--no-first-run', '--disable-extensions',
    '--remote-debugging-port=' + port, '--user-data-dir=' + profile, 'about:blank',
  ];
  const child = spawn(browserPath, flags, { stdio: 'ignore' });
  const cleanup = () => { try { spawnSync('taskkill', ['/pid', String(child.pid), '/T', '/F']); } catch (e) { /* 已退则罢 */ } };
  process.on('exit', cleanup);

  // 等调试口就绪
  let ver = null;
  for (let i = 0; i < 30; i++) {
    await sleep(500);
    try { ver = await (await fetch('http://127.0.0.1:' + port + '/json/version')).json(); break; } catch (e) { /* 端口没起，继续等 */ }
  }
  if (!ver) { console.error('CDP 调试口 15 秒没起来，重跑一次或检查端口占用'); cleanup(); process.exit(1); }

  const cdp = await Cdp.connect(ver.webSocketDebuggerUrl);
  try {
    const { targetId } = await cdp.send('Target.createTarget', { url: 'about:blank' });
    const { sessionId } = await cdp.send('Target.attachToTarget', { targetId, flatten: true });
    await cdp.send('Page.enable', {}, sessionId);
    await cdp.send('Runtime.enable', {}, sessionId);
    const loaded = cdp.once('Page.loadEventFired', sessionId);
    await cdp.send('Page.navigate', { url }, sessionId);
    await Promise.race([loaded, sleep(30000)]);

    // 正文长度连续两次采样不变 = 渲染稳定，最多等 deadline
    let snap = null, stable = 0, last = -1;
    const t0 = Date.now();
    while (Date.now() - t0 < deadline) {
      await sleep(1500);
      const r = await cdp.send('Runtime.evaluate', { expression: EVAL_SNAPSHOT, returnByValue: true }, sessionId);
      if (r.exceptionDetails) { console.error('页面取数异常：' + JSON.stringify(r.exceptionDetails).slice(0, 300)); cleanup(); process.exit(1); }
      snap = JSON.parse(r.result.value);
      stable = snap.textLen === last ? stable + 1 : 0;
      last = snap.textLen;
      if (snap.textLen > 200 && stable >= 1) break; // 已有肉且不再长
    }
    if (!snap) { console.error('没取到快照'); cleanup(); process.exit(1); }
    snap.requested = url; // snap.url 是 location.href（重定向后的真实地址），requested 是原始请求
    snap.warning = snap.textLen < 200 ? '正文过短：可能登录墙/未渲染/反机器人，试 --wait=40000、--headful 或先 --headful-login' : '';
    console.log(JSON.stringify(snap, null, 2));
    await cdp.send('Browser.close').catch(() => {});
  } finally {
    cdp.close();
    cleanup();
  }
}

main().catch(e => { console.error('抓取失败：' + e.message); process.exit(1); });
