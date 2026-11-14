/* cdp.mjs — CDP 底仓（纯 Node 零依赖，Node 24 自带 WebSocket/fetch）
 * 本机惯例（来自多个取数与投放自动化项目的实测）：
 *   - Chrome 136+ 禁止默认配置开调试口 → 必须独立 user-data-dir
 *   - 新开标签要用 PUT /json/new?<url>（GET 已被禁）
 *   - evaluate 一律 IIFE 包裹：顶层 return 会让整段静默不执行（CDP 大坑）
 *   - 一任务一端口一 profile，绝不与他人共用 18801
 */
import { spawn, spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import path from 'node:path';
import fs from 'node:fs';

const SKILL_ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..', '..');

export const CHROME_CANDIDATES = [
  process.env.CHROME_EXE,
  'C:\\Program Files\\Google\\Chrome\\Application\\chrome.exe',
  'C:\\Program Files (x86)\\Google\\Chrome\\Application\\chrome.exe',
  process.env.LOCALAPPDATA ? path.join(process.env.LOCALAPPDATA, 'Google\\Chrome\\Application\\chrome.exe') : ''
].filter(Boolean);

export async function portAlive(port) {
  try {
    const r = await fetch(`http://127.0.0.1:${port}/json/version`, { signal: AbortSignal.timeout(2000) });
    return r.ok;
  } catch { return false; }
}

/* 确保一台调试 Chrome 活着。mode=watch 前台可见（录制/要用户操作），mode=bg 屏幕外（纯自动化） */
export async function ensureChrome({ port = 18801, profile, mode = 'watch', launch = true } = {}) {
  if (await portAlive(port)) return { port, launched: false };
  if (!launch) throw new Error(`调试口 ${port} 不通且未允许拉起浏览器`);
  const exe = CHROME_CANDIDATES.find(p => fs.existsSync(p));
  if (!exe) throw new Error('找不到 chrome.exe，装 Chrome 或设 CHROME_EXE 环境变量');
  profile = profile || path.join(SKILL_ROOT, 'chrome_profile');
  fs.mkdirSync(profile, { recursive: true });
  // bg 的 -21333 坐标是实测过的"屏幕外"位置；要看人操作就用 watch 的正常坐标
  const pos = mode === 'bg' ? '--window-position=-21333,-21333' : '--window-position=40,40 --window-size=1280,860';
  const args = [
    `--remote-debugging-port=${port}`, `--user-data-dir=${profile}`, pos,
    '--no-first-run', '--no-default-browser-check', '--restore-last-session=false', 'about:blank'
  ];
  spawn(exe, args, { detached: true, stdio: 'ignore' }).unref();
  for (let i = 0; i < 40; i++) {
    await sleep(500);
    if (await portAlive(port)) return { port, launched: true };
  }
  throw new Error(`Chrome 拉起后调试口 ${port} 仍不通（可能被占用或 profile 被锁）`);
}

export function sleep(ms) { return new Promise(r => setTimeout(r, ms)); }

/* ---------- 浏览器农场感知（2026-11-14）：农场档位=常驻登录态，只连不关 ----------
 * 农场（browser-farm）每账号一个常驻 Chrome 档，固定调试端口（默认 9331 起），总管在 9300。
 * forge 的 --port 指到档位口，就能在已登录账号上直接录制/回放，不用重新登录。
 * 铁律：识别为农场档位的端口，收尾绝不关（关了破坏「登录一次永久保持」）；识别失败按非农场处理（照旧关）。*/
export function farmPort() { return Number(process.env.SF_FARM_PORT || 9300); }

/* 这个调试口是不是农场的档位？是 → 返回 {id, note, port}；不是/农场没跑 → null */
export async function farmSlotOf(port) {
  try {
    const h = await fetch(`http://127.0.0.1:${farmPort()}/health`, { signal: AbortSignal.timeout(1200) });
    if (!h.ok) return null;
    const r = await fetch(`http://127.0.0.1:${farmPort()}/slots`, { signal: AbortSignal.timeout(1500) });
    const j = await r.json();
    const s = (j.slots || []).find(x => Number(x.port) === Number(port));
    return s ? { id: s.id, note: s.note || '', port: s.port } : null;
  } catch { return null; } // 农场没跑/回话慢：按非农场处理，走默认收尾
}

/* 聪明收尾：农场档位只连不关（档位归农场总管管，forge 不越权杀）；非农场照旧按端口关 */
export async function closeChromeSmart(port, { log = console.log } = {}) {
  const slot = await farmSlotOf(port);
  if (slot) {
    log(`  [农场] port=${port} 是常驻档 ${slot.id}（${slot.note}），不关——档位归农场管`);
    return { ok: true, skipped: 'farm-slot', slot };
  }
  return closeChromeByPort(port, { log });
}

/* 写接口在农场档位上真跑前的快照（出事能回滚）：失败=抛错，调用方别带病写 */
export async function farmPreWriteSnapshot(port, label) {
  const slot = await farmSlotOf(port);
  if (!slot) return null; // 不是农场档：没有快照能力，正常继续
  const r = await fetch(`http://127.0.0.1:${farmPort()}/slot/${encodeURIComponent(slot.id)}/snapshot`, {
    method: 'POST', headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ name: String(label || '写前快照').slice(0, 60) }),
    signal: AbortSignal.timeout(60000),
  });
  const j = await r.json().catch(() => ({}));
  if (!r.ok || !j.ok) throw new Error(`农场写前快照失败（档 ${slot.id}）：${j.error || r.status}`);
  return { slot, snapshot: j };
}

/* 按调试端口精确关掉「自己开的」那台 Chrome（全局规则：跑完必须收尾，不许挂一整天）
 * 只匹配命令行里的 remote-debugging-port=<port>，绝不按进程名全杀（别人的浏览器不能碰） */
export function closeChromeByPort(port, { log = console.log } = {}) {
  const q = `--remote-debugging-port=${port}`;
  const ps = `$p = Get-CimInstance Win32_Process | Where-Object { $_.CommandLine -like '*${q}*' }; ` +
      `if ($p) { $ids = $p.ProcessId; $p | ForEach-Object { Stop-Process -Id $_.ProcessId -Force -ErrorAction SilentlyContinue }; "CLOSED pids=$($ids -join ',')" } else { 'NOTHING' }`;
  try {
    const r = spawnSync('powershell', ['-NoProfile', '-ExecutionPolicy', 'Bypass', '-Command', ps], { encoding: 'utf8', timeout: 30000 });
    const out = String(r.stdout || '').trim();
    log(`  关闭浏览器 port=${port} → ${out.slice(-120) || '(无输出)'}`);
    return { ok: !r.error, out, remaining: /remaining=0/.test(out) ? 0 : null };
  } catch (e) {
    log(`  关闭浏览器失败（port=${port}）：${e.message}`);
    return { ok: false, out: '', remaining: null };
  }
}

async function listTargets(port) {
  const r = await fetch(`http://127.0.0.1:${port}/json/list`);
  return r.json();
}

/* 找/开一个页面标签。给了 urlPart 就找 URL 含它的旧标签，找不到开新的 */
export async function findPage({ port = 18801, url, urlPart, create = true } = {}) {
  const list = await listTargets(port);
  const pages = list.filter(t => t.type === 'page');
  let hit = urlPart ? pages.find(p => (p.url || '').includes(urlPart)) : pages[0];
  if (!hit && create) {
    const open = url || 'about:blank';
    // PUT：新版 Chrome 的 /json/new 只收 PUT（实测坑）
    const r = await fetch(`http://127.0.0.1:${port}/json/new?${encodeURIComponent(open)}`, { method: 'PUT' });
    hit = await r.json();
  }
  if (!hit) throw new Error('没有可用的页面标签');
  return hit;
}

/* CDP 会话：发命令 + 订阅事件 */
export class Cdp {
  constructor(wsUrl, targetInfo) {
    this.wsUrl = wsUrl; this.target = targetInfo;
    this.id = 0; this.pending = new Map(); this.handlers = new Map();
  }
  static async attach({ port = 18801, urlPart, url, create = true } = {}) {
    const t = await findPage({ port, urlPart, url, create });
    const c = new Cdp(t.webSocketDebuggerUrl, t);
    await c._open();
    return c;
  }
  async _open() {
    this.ws = new WebSocket(this.wsUrl);
    await new Promise((ok, bad) => {
      this.ws.onopen = ok;
      this.ws.onerror = () => bad(new Error(`连不上调试口：${this.wsUrl}`));
    });
    this.ws.onmessage = ev => {
      const m = JSON.parse(ev.data);
      if (m.id && this.pending.has(m.id)) {
        const { res, rej } = this.pending.get(m.id);
        this.pending.delete(m.id);
        m.error ? rej(new Error(`${m.error.message} (${m.method || m.id})`)) : res(m.result);
      } else if (m.method && this.handlers.has(m.method)) {
        for (const fn of this.handlers.get(m.method)) fn(m.params);
      }
    };
    // 页面整页跳转/标签关闭时 ws 会断；不兜底的话 send() 永远挂住，录制轮询就此卡死
    this.ws.onclose = () => {
      for (const { rej } of this.pending.values()) rej(new Error('调试连接已断开'));
      this.pending.clear();
    };
  }
  on(method, fn) {
    if (!this.handlers.has(method)) this.handlers.set(method, []);
    this.handlers.get(method).push(fn);
  }
  send(method, params = {}, timeoutMs = 15000) {
    const id = ++this.id;
    try { this.ws.send(JSON.stringify({ id, method, params })); }
    catch (e) { return Promise.reject(new Error(`发送失败：${e.message}`)); }
    return new Promise((res, rej) => {
      const timer = setTimeout(() => {
        this.pending.delete(id);
        rej(new Error(`CDP 超时（${timeoutMs}ms）：${method}`));
      }, timeoutMs);
      this.pending.set(id, {
        res: v => { clearTimeout(timer); res(v); },
        rej: e => { clearTimeout(timer); rej(e); }
      });
    });
  }
  close() { try { this.ws.close(); } catch { /* already closed */ } }

  /* 求值：自动 IIFE 包裹 + 等待 Promise + 中文原样返回 */
  async evalJs(expression, { awaitPromise = true } = {}) {
    const wrapped = expression.trim().startsWith('(function') || expression.trim().startsWith('(async')
      ? expression : `(async function(){ return (${expression}); })()`;
    const r = await this.send('Runtime.evaluate', {
      expression: wrapped, returnByValue: true, awaitPromise
    });
    if (r.exceptionDetails) {
      throw new Error(`页面执行报错：${r.exceptionDetails.exception?.description || r.exceptionDetails.text}`);
    }
    return r.result?.value;
  }

  /* 注入整个 js 文件（内容须是表达式形态，如 recorder.js 的 IIFE）
     注意：不能走 evalJs()——它会再做一次 IIFE 包裹，带注释+末尾分号的文件会被包坏（实测） */
  async injectFile(filePath) {
    const code = fs.readFileSync(filePath, 'utf8');
    const r = await this.send('Runtime.evaluate', { expression: code, returnByValue: true, awaitPromise: false });
    if (r?.exceptionDetails) {
      throw new Error(`注入失败：${r.exceptionDetails.exception?.description || r.exceptionDetails.text}`);
    }
    return r?.result?.value;
  }

  async enableSession() {
    await this.send('Page.enable');
    await this.send('Runtime.enable');
    await this.send('Network.enable');
  }
}

/* 下载管家：把本会话下载落到独立目录，收齐文件名与结束事件 */
export function watchDownloads(cdp, dir) {
  fs.mkdirSync(dir, { recursive: true });
  // 不设这个，Chrome 会下到系统下载夹，dir 里的文件名就对不上了（实测坑）
  cdp.send('Page.setDownloadBehavior', { behavior: 'allow', downloadPath: dir }).catch(() => {});
  const files = [];
  cdp.on('Page.downloadWillBegin', p => {
    files.push({ guid: p.guid, filename: p.suggestedFilename, at: Date.now(), done: false });
  });
  cdp.on('Page.downloadProgress', p => {
    const f = files.find(x => x.guid === p.guid);
    if (f && p.state === 'completed') f.done = true;
  });
  return {
    dir, files,
    async waitAll(timeoutMs = 120000) {
      const t0 = Date.now();
      while (Date.now() - t0 < timeoutMs) {
        if (files.length && files.every(f => f.done)) return files;
        await sleep(1000);
      }
      throw new Error(`等下载超时：${files.filter(f => !f.done).map(f => f.filename).join(', ') || '一个都没开始'}`);
    }
  };
}

/* 网络摘要：只记 XHR/Fetch 请求（找"同源接口直调"用），环形上限 600 条 */
/* 网络采证：不只记 URL，还记状态码/耗时/响应体摘要/返回字段
   目的：让 agent 能判断「这一步的数据是不是某个接口直接给的」，从而找更短的路 */
function pickHeaders(h = {}) {
  const keep = ['content-type', 'authorization', 'x-requested-with'];
  const out = {};
  for (const [k, v] of Object.entries(h)) if (keep.includes(String(k).toLowerCase())) out[k] = String(v).slice(0, 200);
  return out;
}

/* JSON → 字段名 + 行数：{data:{list:[...]}} 这种包裹也要能挖到 */
function summarizeJson(text) {
  if (!text || !/^\s*[[{]/.test(text)) return { fields: null, rows: null };
  try {
    const j = JSON.parse(text);
    const walk = (o, depth = 0) => {
      if (!o || typeof o !== 'object' || depth > 3) return null;
      for (const v of Object.values(o)) {
        if (Array.isArray(v) && v.length && typeof v[0] === 'object') return v;
        const got = walk(v, depth + 1); if (got) return got;
      }
      return null;
    };
    const arr = Array.isArray(j) ? j : walk(j);
    if (arr && arr.length) return { fields: Object.keys(arr[0]).slice(0, 40), rows: arr.length };
    if (!Array.isArray(j)) return { fields: Object.keys(j).slice(0, 40), rows: null };
  } catch { /* 不是 JSON */ }
  return { fields: null, rows: null };
}

export function watchNetwork(cdp) {
  const reqs = [];
  const byId = new Map();
  const MAX = 800;
  cdp.on('Network.requestWillBeSent', p => {
    if (!['XHR', 'Fetch'].includes(p.type)) return;
    if (reqs.length >= MAX) { const old = reqs.shift(); byId.delete(old.id); }
    const r = {
      id: p.requestId, at: Date.now(), type: p.type,
      method: p.request.method,
      url: p.request.url.slice(0, 500),
      body: p.request.postData ? String(p.request.postData).slice(0, 1500) : '',
      headers: pickHeaders(p.request.headers),
      status: null, mime: '', size: 0, ms: null,
      respPreview: '', fields: null, rows: null
    };
    byId.set(p.requestId, r);
    reqs.push(r);
  });
  cdp.on('Network.responseReceived', p => {
    const r = byId.get(p.requestId); if (!r) return;
    r.status = p.response.status;
    r.mime = p.response.mimeType || '';
    r.size = p.response.encodedDataLength || 0;
  });
  cdp.on('Network.loadingFinished', p => {
    const r = byId.get(p.requestId); if (!r) return;
    r.ms = Date.now() - r.at;
    cdp.send('Network.getResponseBody', { requestId: p.requestId }, 8000).then(b => {
      const text = b?.base64Encoded ? '' : String(b?.body || '');
      r.respPreview = text.slice(0, 4000);
      const s = summarizeJson(text);
      r.fields = s.fields; r.rows = s.rows;
    }).catch(() => { /* 大文件/已失效，跳过 */ });
  });
  return reqs;
}
