// 脚本引擎：录制/路径循环/数据触发。supervisor（后台任务）和 farm.js（录制/试跑）共用。
// 单点循环/路径循环 = loop 引擎（步骤 1~N 条，随机延迟+点击位置随机偏移，模拟真人）
// 数据触发 = watch 引擎（盯表格某行某列数值，达标点该行按钮，如 计划A消费≥300→暂停）
'use strict';
const http = require('http');
const fs = require('fs');
const path = require('path');

const SCRIPTS_DIR = process.env.FARM_HOME ? path.join(process.env.FARM_HOME, 'scripts') : path.join(__dirname, 'scripts');
const sleep = ms => new Promise(r => setTimeout(r, ms));
function log(msg) { console.log('[' + new Date().toTimeString().slice(0, 8) + '] ' + msg); }

// ---------- HTTP 小工具（不走 fetch，避开代理环境变量） ----------
function jget(port, p, timeoutMs) {
  return new Promise((resolve, reject) => {
    const req = http.get({ host: '127.0.0.1', port, path: p, timeout: timeoutMs || 1500 }, res => {
      let d = '';
      res.on('data', c => d += c);
      res.on('end', () => { try { resolve(JSON.parse(d)); } catch (e) { reject(new Error('非 JSON: ' + d.slice(0, 100))); } });
    });
    req.on('timeout', () => req.destroy(new Error('timeout')));
    req.on('error', reject);
  });
}

// ---------- CDP 会话 ----------
class Cdp {
  constructor(wsUrl) { this.wsUrl = wsUrl; this.ws = null; this.seq = 0; this.pending = new Map(); this.handlers = []; }
  connect() {
    return new Promise((resolve, reject) => {
      this.ws = new WebSocket(this.wsUrl);
      this.ws.onopen = () => resolve(this);
      this.ws.onerror = () => reject(new Error('WS 连不上: ' + this.wsUrl));
      this.ws.onmessage = ev => {
        const m = JSON.parse(ev.data);
        if (m.id !== undefined && this.pending.has(m.id)) {
          const { res, rej, timer } = this.pending.get(m.id);
          clearTimeout(timer); this.pending.delete(m.id);
          m.error ? rej(new Error('CDP: ' + m.error.message)) : res(m.result);
        } else {
          for (const h of this.handlers) h(m);
        }
      };
    });
  }
  send(method, params) {
    const id = ++this.seq;
    return new Promise((resolve, reject) => {
      const timer = setTimeout(() => { this.pending.delete(id); reject(new Error('CDP 超时: ' + method)); }, 25000);
      this.pending.set(id, { res: resolve, rej: reject, timer });
      this.ws.send(JSON.stringify({ id, method, params: params || {} }));
    });
  }
  onMessage(h) { this.handlers.push(h); }
  close() { try { this.ws.close(); } catch (e) {} }
}

async function attachPage(port, targetId) {
  const list = (await jget(port, '/json/list', 2500)).filter(t => t.type === 'page');
  const page = targetId
    ? list.find(p => p.id === targetId)
    : (list.find(p => !p.url.startsWith('devtools://')) || list[0]);
  if (!page) throw new Error(targetId ? '没有这个页面 ' + targetId : '端口 ' + port + ' 上没有页面，先开一页');
  const cdp = new Cdp(page.webSocketDebuggerUrl);
  await cdp.connect();
  await cdp.send('Page.enable');
  await cdp.send('Runtime.enable');
  return cdp;
}

// 两个地址算不算同一个页：先精确比，再去掉 ?query 比（页面带跟踪参数会变，地址本体不变）。
// #hash 保留参与比较——SPA 靠 hash 路由，hash 变了就是另一个画面，不能糊成同一个页。
function samePage(a, b) {
  if (!a || !b) return false;
  if (a === b) return true;
  const cut = u => {
    u = String(u);
    const h = u.indexOf('#');
    const base = h >= 0 ? u.slice(0, h) : u, frag = h >= 0 ? u.slice(h) : '';
    const q = base.indexOf('?');
    return (q >= 0 ? base.slice(0, q) : base) + frag;
  };
  return cut(a) === cut(b);
}

// 浏览器级开新页：/json/version 拿浏览器调试口，Target.createTarget 开页（和总管 open 同一条路，已验证可靠）
async function openTabOnPort(port, url) {
  const v = await jget(port, '/json/version', 2500);
  const cdp = new Cdp(v.webSocketDebuggerUrl);
  await cdp.connect();
  try { return (await cdp.send('Target.createTarget', { url })).targetId; }
  finally { cdp.close(); }
}

// ---------- 录制：常驻条（两态）+ 页面注入的点击监听（capture 阶段，抢在框架改 DOM 前） ----------
// 条常驻浏览器窗口右下角（bottom:56 避开 Chrome 自带的右下角自定义钮）：平时绿钮「● 开始录制」，
// 录制中=红点+计数+「■ 停止并保存」。态由外面会话推（window.__farmBarSet('rec'|'idle')），
// 点击监听只在 rec 态记账——平时条只是摆着，等一键开录。
// label=档位名（如「档12·备注」）：条左端常驻小标 + 页面标题后缀，多开窗口一眼认出是哪个档的浏览器
function barSrc(label) {
  const L = String(label || '').replace(/[\r\n"\\]/g, '').slice(0, 16);
  const BAR_SRC = [
  '(function(){',
  '  var FARM_LABEL = ' + JSON.stringify(L) + ';',
  '  var bar = document.getElementById("__farmRecBar");',
  '  if (bar && bar.dataset.farm !== "2") { bar.remove(); bar = null; } // 旧版条（没档位标/不存钮）拆了重建：升级后已开页面不用刷新就拿到新条',
  '  if (!bar) {',
  '    bar = document.createElement("div");',
  '    bar.id = "__farmRecBar";',
  '    bar.style.cssText = "position:fixed;right:16px;bottom:56px;z-index:2147483647;display:flex;align-items:center;gap:10px;padding:10px 14px;background:#111827;color:#fff;border-radius:10px;font:13px/1.4 system-ui,sans-serif;box-shadow:0 4px 16px rgba(0,0,0,.35);user-select:none;";',
  '    bar.dataset.farm = "2";',
  // 档位名小标：条最左端，任何态都显示——多开时认出这页属于哪个档
  '    var chip = document.createElement("span");',
  '    chip.textContent = FARM_LABEL;',
  '    chip.title = FARM_LABEL;',
  '    chip.style.cssText = "font:12px system-ui,sans-serif;color:#9ca3af;max-width:150px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;";',
  '    if (FARM_LABEL) bar.appendChild(chip);',
  // 平时态：绿钮一键开录
  '    var idleBox = document.createElement("span");',
  '    idleBox.style.cssText = "display:flex;align-items:center;";',
  '    var btnStart = document.createElement("button");',
  '    btnStart.type = "button";',
  '    btnStart.style.cssText = "padding:6px 12px;border:0;border-radius:6px;background:#059669;color:#fff;font:13px system-ui,sans-serif;cursor:pointer;";',
  '    btnStart.textContent = "● 开始录制";',
  '    btnStart.addEventListener("click", function(){ try { window.__wsCmd("start"); } catch (e) {} });',
  '    idleBox.appendChild(btnStart);',
  // 录制态：红点+计数+停止钮
  '    var recBox = document.createElement("span");',
  '    recBox.style.cssText = "display:none;align-items:center;gap:10px;";',
  '    var dot = document.createElement("span");',
  '    dot.style.cssText = "width:9px;height:9px;border-radius:50%;background:#ef4444;display:inline-block;";',
  '    var cnt = document.createElement("span");',
  '    cnt.id = "__farmRecCnt";',
  '    cnt.textContent = "录制中 0 下";',
  '    var btn = document.createElement("button");',
  '    btn.type = "button";',
  '    btn.style.cssText = "padding:6px 12px;border:0;border-radius:6px;background:#dc2626;color:#fff;font:13px system-ui,sans-serif;cursor:pointer;";',
  '    btn.textContent = "■ 停止并保存";',
  // 停止不再直接存：先弹命名框（自定义名字，空=自动起），「存」才真存；录制没停，反悔可「继续录」
  '    btn.addEventListener("click", askName);',
  // 命名态：输入框 + 存 + 继续录（Enter=存，Esc=继续录）
  '    var saveBox = document.createElement("span");',
  '    saveBox.style.cssText = "display:none;align-items:center;gap:8px;";',
  '    var nameInput = document.createElement("input");',
  '    nameInput.placeholder = "脚本名（可空=自动起）";',
  '    nameInput.maxLength = 30;',
  '    nameInput.style.cssText = "padding:6px 10px;border:0;border-radius:6px;background:#fff;color:#111827;font:13px system-ui,sans-serif;width:170px;outline:none;";',
  '    var btnSave = document.createElement("button");',
  '    btnSave.type = "button";',
  '    btnSave.style.cssText = "padding:6px 14px;border:0;border-radius:6px;background:#059669;color:#fff;font:13px system-ui,sans-serif;cursor:pointer;";',
  '    btnSave.textContent = "存";',
  // 存Agent：不进脚本体系，存成 agent 直接读的 markdown 笔记（发 agent 或落盘给它读）
  '    var btnAgent = document.createElement("button");',
  '    btnAgent.type = "button";',
  '    btnAgent.style.cssText = "padding:6px 14px;border:0;border-radius:6px;background:#2563eb;color:#fff;font:13px system-ui,sans-serif;cursor:pointer;";',
  '    btnAgent.title = "不存脚本，存一份给 agent 读的操作笔记（md 文件）";',
  '    btnAgent.textContent = "存Agent";',
  '    var btnGo = document.createElement("button");',
  '    btnGo.type = "button";',
  '    btnGo.style.cssText = "padding:6px 10px;border:1px solid #4b5563;border-radius:6px;background:transparent;color:#d1d5db;font:13px system-ui,sans-serif;cursor:pointer;";',
  '    btnGo.textContent = "继续录";',
  // 不存：整场扔掉（录废了/点错了），不落任何文件
  '    var btnDrop = document.createElement("button");',
  '    btnDrop.type = "button";',
  '    btnDrop.style.cssText = "padding:6px 10px;border:1px solid #4b5563;border-radius:6px;background:transparent;color:#f87171;font:13px system-ui,sans-serif;cursor:pointer;";',
  '    btnDrop.textContent = "不存";',
  '    function askName(){',
  '      nameInput.value = "";',
  '      recBox.style.display = "none";',
  '      saveBox.style.display = "flex";',
  '      btnSave.disabled = false; btnSave.textContent = "存";',
  '      btnAgent.disabled = false; btnAgent.textContent = "存Agent";',
  '      btnDrop.disabled = false; btnDrop.textContent = "不存";',
  '      try { nameInput.focus(); } catch (e) {}',
  '    }',
  '    function backToRec(){',
  '      saveBox.style.display = "none";',
  '      recBox.style.display = "flex";',
  '    }',
  '    function doSave(){',
  '      if (btnSave.disabled) return;',
  '      btnSave.disabled = true; btnSave.textContent = "存中…";',
  '      var nm = (nameInput.value || "").trim();',
  '      try { window.__wsCmd(JSON.stringify({ cmd: "stop", name: nm })); }',
  '      catch (e) { btnSave.disabled = false; btnSave.textContent = "存"; }',
  '    }',
  '    function doSaveAgent(){', // 与存同一条路，多带 asAgent：服务端不建脚本，写 agent-notes/ 笔记
  '      if (btnAgent.disabled) return;',
  '      btnAgent.disabled = true; btnAgent.textContent = "存中…";',
  '      var nm = (nameInput.value || "").trim();',
  '      try { window.__wsCmd(JSON.stringify({ cmd: "stop", name: nm, asAgent: true })); }',
  '      catch (e) { btnAgent.disabled = false; btnAgent.textContent = "存Agent"; }',
  '    }',
  '    function doDrop(){',
  '      if (btnDrop.disabled) return;',
  '      btnDrop.disabled = true; btnDrop.textContent = "丢弃中…";',
  '      try { window.__wsCmd(JSON.stringify({ cmd: "stop", discard: true })); }',
  '      catch (e) { btnDrop.disabled = false; btnDrop.textContent = "不存"; }',
  '    }',
  '    btnSave.addEventListener("click", doSave);',
  '    btnAgent.addEventListener("click", doSaveAgent);',
  '    btnDrop.addEventListener("click", doDrop);',
  '    btnGo.addEventListener("click", backToRec);',
  '    nameInput.addEventListener("keydown", function(e){',
  '      if (e.key === "Enter") doSave();',
  '      else if (e.key === "Escape") backToRec();',
  '    });',
  '    recBox.appendChild(dot); recBox.appendChild(cnt); recBox.appendChild(btn);',
  '    saveBox.appendChild(nameInput); saveBox.appendChild(btnSave); saveBox.appendChild(btnAgent); saveBox.appendChild(btnGo); saveBox.appendChild(btnDrop);',
  '    bar.appendChild(idleBox); bar.appendChild(recBox); bar.appendChild(saveBox);',
  '    window.__farmBarSet = function(s){',
  '      window.__farmBarState = s === "rec" ? "rec" : "idle";',
  '      idleBox.style.display = window.__farmBarState === "rec" ? "none" : "flex";',
  '      recBox.style.display = window.__farmBarState === "rec" ? "flex" : "none";',
  '      saveBox.style.display = "none"; // 服务器推什么态都收掉命名框（存成功推 idle、新一场推 rec、导航重推）',
  '      if (window.__farmBarState === "rec") { // 开录=新一场，本页计数从零数',
  '        cnt.dataset.n = 0; cnt.textContent = "录制中 0 下";',
  '        btn.disabled = false; btn.textContent = "■ 停止并保存";',
  '      }',
  '    };',
  '    function mount(){',
  '      if (!document.documentElement) return; // 新文档刚创建还没有根元素，等 DOMContentLoaded 再挂，这里不许抛（抛了监听器就没了）',
  '      if (!document.getElementById("__farmRecBar")) document.documentElement.appendChild(bar);',
  '      try { if (FARM_LABEL && document.title && document.title.indexOf(FARM_LABEL) < 0) document.title = document.title + " 〔" + FARM_LABEL + "〕"; } catch (e) {} // 标题带档名：任务栏/窗口栏认出是哪个档的浏览器',
  '    }',
  '    mount();',
  '    document.addEventListener("DOMContentLoaded", mount); // 文档头注入时可能被站点脚本清掉，补一枪',
  '    window.__farmBarSet(window.__farmBarState || "idle");',
  '  }',
  "  if (window.__wsRecInstalled) return; window.__wsRecInstalled = 1;",
  '  function cssPath(el){',
  '    var p = [];',
  "    while (el && el.tagName !== 'HTML' && p.length < 8){",
  '      var i = 1, s = el;',
  '      while (s.previousElementSibling){ s = s.previousElementSibling; i++; }',
  "      p.unshift(el.tagName.toLowerCase() + ':nth-child(' + i + ')');",
  '      el = el.parentElement;',
  '    }',
  "    return 'html>' + p.join('>');",
  '  }',
  "  document.addEventListener('click', function(e){",
  '    try { if (e.target && e.target.closest && e.target.closest("#__farmRecBar")) return; } catch (x) {} // 录制条自己的点击不算步骤',
  '    if (!e.isTrusted) return; // 网页自己代码触发的合成点击不录——下载按钮真点一下会跟一个隐形临时 <a> 的假点击，录进去回放永远找不到',
  '    if (window.__farmBarState !== "rec") return; // 平时条在但不记账，只有录制中才记',
  '    var el = e.target, up = 0;',
  '    try {',
  '      // 点到的常是按钮里的 span/svg，往上找按钮本体',
  '      while (el && el.parentElement && el !== document.body && up < 4){',
  "        var tag = el.tagName, role = el.getAttribute && el.getAttribute('role');",
  "        if (tag === 'BUTTON' || tag === 'A' || role === 'button') break;",
  '        el = el.parentElement; up++;',
  '      }',
  '      if (!el || el === document || el === document.documentElement) el = e.target;',
  "      var text = (el.innerText || el.value || '').replace(/\\s+/g, ' ').trim().slice(0, 30);",
  '      var id = (el.id && !/^\\d/.test(el.id) && !/^[a-z]*\\d{4,}$/i.test(el.id) && el.id.length < 30) ? el.id : null;',
  '      var attr = null;',
  '      for (var i = 0; i < el.attributes.length; i++){',
  '        var n = el.attributes[i].name, v = el.attributes[i].value;',
  "        if (/^data-[a-z][a-z0-9-]*$/.test(n) && v && v.length < 60 && v.indexOf('\"') < 0) { attr = [n, v]; break; }",
  '      }',
  '      var sel = id ? ("#" + id)',
  "        : attr ? ('[' + attr[0] + '=\"' + attr[1] + '\"]')",
  '        : text ? ("text=" + text)',
  '        : ("path=" + cssPath(el));',
  '      window.__wsRec(JSON.stringify({ selector: sel, text: text, tag: el.tagName, href: location.href, ts: Date.now() }));',
  '      var c = document.getElementById("__farmRecCnt");',
  '      if (c) { c.dataset.n = (+(c.dataset.n) || 0) + 1; c.textContent = "录制中 " + c.dataset.n + " 下"; }',
  '    } catch (err) {',
  '      try { window.__wsRec(JSON.stringify({ selector: "path=" + cssPath(e.target), text: "", tag: e.target.tagName, href: location.href, ts: Date.now(), err: String(err) })); } catch (e2) {}',
  '    }',
  '  }, true);',
  '})();',
  ].join('\n');
  return BAR_SRC;
}

// 收工撤录制条（页面已关/已跳走时 evaluate 会失败，忽略）
const BAR_REMOVE_SRC = '(function(){var b=document.getElementById("__farmRecBar"); if (b) b.remove();})()';
// 推条状态（页面还没注入 BAR_SRC 时 __farmBarSet 不存在，短路掉不炸）
const barStateExpr = s => 'window.__farmBarSet&&window.__farmBarSet("' + s + '")';

// ---------- 常驻录制条会话：挂在档位上，页面开了就带条，新标签页自动跟上 ----------
// 会话不死：每 1.2s 轮询 /json/list 补新页、丢死页；页面导航（loadEventFired）后重注条+重推态
// （不推的话新文档里条回到平时态，录制中的点击就静默丢了——这是命门）。
// recActive 才记步：平时条只是摆着，用户点「● 开始录制」回传 onCmd('start')，外层调 startRec()。
async function barSession(port, opts) {
  const o = opts || {};
  const SRC = barSrc(o.label); // 档位名打进条源码（chip+标题后缀），本会话所有注入共用同一份
  const self = { port, dead: false, recActive: false, steps: [], pages: new Map() }; // pages: targetId -> cdp
  let sweeping = false, fails = 0;
  function pushState(cdp, s) {
    // 推态是尽力而为：页面死了 evaluate 会超时 reject，必须接住（裸 promise 没人接会崩宿主进程）
    try { cdp.send('Runtime.evaluate', { expression: barStateExpr(s) }).catch(() => {}); } catch (e) {}
  }
  const pushAll = s => { for (const cdp of self.pages.values()) pushState(cdp, s); };
  async function attach(p) {
    const cdp = new Cdp(p.webSocketDebuggerUrl);
    await cdp.connect();
    await cdp.send('Runtime.enable');
    await cdp.send('Page.enable');
    await cdp.send('Runtime.addBinding', { name: '__wsRec' });
    await cdp.send('Runtime.addBinding', { name: '__wsCmd' }); // 条上按钮的回传通道（start/stop）
    await cdp.send('Page.addScriptToEvaluateOnNewDocument', { source: SRC });
    await cdp.send('Runtime.evaluate', { expression: SRC });
    pushState(cdp, self.recActive ? 'rec' : 'idle');
    cdp.onMessage(m => {
      if (m.method === 'Page.loadEventFired') {
        try { cdp.send('Runtime.evaluate', { expression: SRC }).catch(() => {}); } catch (e) {}
        pushState(cdp, self.recActive ? 'rec' : 'idle');
      }
      if (m.method === 'Runtime.bindingCalled' && m.params.name === '__wsRec') {
        if (!self.recActive) return;
        try {
          const st = JSON.parse(m.params.payload);
          self.steps.push(st);
          if (o.onStep) o.onStep(st, self.steps.length);
        } catch (e) { console.error('录制的点击数据解析失败: ' + e.message); }
      }
      if (m.method === 'Runtime.bindingCalled' && m.params.name === '__wsCmd' && o.onCmd) {
        try { o.onCmd(m.params.payload); } catch (e) { console.error('录制条命令处理失败: ' + e.message); }
      }
    });
    cdp.ws.onclose = () => { self.pages.delete(p.id); }; // 页面关了/崩了，下轮巡检自然补
    self.pages.set(p.id, cdp);
  }
  async function sweep() {
    let list;
    try { list = (await jget(port, '/json/list', 1500)).filter(t => t.type === 'page' && !t.url.startsWith('devtools://')); }
    catch (e) { fails += 1; if (fails > 40) self.close(); return; } // 档位没了：自收会话，外部 ensureBar 还能重建
    fails = 0;
    const ids = new Set(list.map(t => t.id));
    for (const id of [...self.pages.keys()]) {
      if (!ids.has(id)) { try { self.pages.get(id).close(); } catch (e) {} self.pages.delete(id); }
    }
    for (const t of list) {
      if (self.pages.has(t.id)) continue;
      try { await attach(t); } catch (e) { /* 页面可能正开着关着，下轮再试 */ }
    }
  }
  await sweep(); // 建会话先把当前页面全钩上（调用方可以就此等条就位）
  const timer = setInterval(() => { if (!self.dead && !sweeping) { sweeping = true; sweep().catch(() => {}).finally(() => { sweeping = false; }); } }, 1200);
  self.startRec = () => { self.recActive = true; self.steps.length = 0; pushAll('rec'); };
  self.stopRec = () => { self.recActive = false; pushAll('idle'); return self.steps.slice(); };
  self.close = () => {
    if (self.dead) return; self.dead = true;
    clearInterval(timer);
    for (const cdp of self.pages.values()) {
      try { cdp.send('Runtime.evaluate', { expression: BAR_REMOVE_SRC }).catch(() => {}); } catch (e) {}
      cdp.close();
    }
    self.pages.clear();
  };
  return self;
}

// ---------- 一次性录制会话（老接口：test-scripter/直连引擎用）----------
// 建好即录制态；新标签页不跟（跟条要用上面的 barSession）。停了把条弹回平时态但不撤条——
// 撤了会把同页面上的常驻条一起干掉。导航后 loadEventFired 重推，保持录制态不断。
async function recordSession(port, onStep, onCmd) {
  const pages = (await jget(port, '/json/list', 2500)).filter(t => t.type === 'page' && !t.url.startsWith('devtools://'));
  if (!pages.length) throw new Error('端口 ' + port + ' 上没有页面');
  const SRC = barSrc(''); // 引擎层会话没有档位名，条不带标识
  const sessions = [];
  const steps = [];
  const pushAll = s => {
    for (const cdp of sessions) {
      try { cdp.send('Runtime.evaluate', { expression: barStateExpr(s) }).catch(() => {}); } catch (e) {}
    }
  };
  for (const p of pages) {
    const cdp = new Cdp(p.webSocketDebuggerUrl);
    await cdp.connect();
    await cdp.send('Runtime.enable');
    await cdp.send('Page.enable');
    await cdp.send('Runtime.addBinding', { name: '__wsRec' });
    await cdp.send('Runtime.addBinding', { name: '__wsCmd' });
    await cdp.send('Page.addScriptToEvaluateOnNewDocument', { source: SRC });
    await cdp.send('Runtime.evaluate', { expression: SRC });
    cdp.onMessage(m => {
      if (m.method === 'Page.loadEventFired') {
        try { cdp.send('Runtime.evaluate', { expression: SRC }).catch(() => {}); } catch (e) {}
        try { cdp.send('Runtime.evaluate', { expression: barStateExpr('rec') }).catch(() => {}); } catch (e) {}
      }
      if (m.method === 'Runtime.bindingCalled' && m.params.name === '__wsRec') {
        try {
          const st = JSON.parse(m.params.payload);
          steps.push(st);
          if (onStep) onStep(st, steps.length);
        } catch (e) { console.error('录制的点击数据解析失败: ' + e.message); }
      }
      if (m.method === 'Runtime.bindingCalled' && m.params.name === '__wsCmd' && onCmd) {
        try { onCmd(m.params.payload); } catch (e) { console.error('页面停止命令处理失败: ' + e.message); }
      }
    });
    sessions.push(cdp);
  }
  pushAll('rec'); // 点击监听有态闸门，不推录制态的话一步都不会记
  return {
    steps,
    stop: () => {
      pushAll('idle');
      for (const s of sessions) s.close();
    },
    pages: pages.map(p => p.id),
  };
}

// ---------- 执行：找元素 ----------
const FIND_SRC = `(function(sel){
  function vis(el){ var r = el.getBoundingClientRect(); return r.width > 0 && r.height > 0; }
  var el = null;
  if (sel.charAt(0) === '#') { var e1 = document.querySelector(sel); if (e1 && vis(e1)) el = e1; }
  else if (sel.charAt(0) === '[') { var ls = document.querySelectorAll(sel); for (var i=0;i<ls.length;i++) if (vis(ls[i])) { el = ls[i]; break; } }
  else if (sel.indexOf('text=') === 0) {
    var t = sel.slice(5).trim();
    var all = document.querySelectorAll('button,a,[role=button],span,div,td,li,input,i');
    var exact = [], part = [];
    for (var j=0;j<all.length;j++){
      var e = all[j];
      var tx = (e.innerText || e.value || '').replace(/\\s+/g,' ').trim();
      if (!tx || !vis(e)) continue;
      if (tx === t) exact.push(e);
      else if (tx.length < t.length + 20 && tx.indexOf(t) >= 0) part.push(e);
    }
    function smallest(arr){ var best = null; for (var k=0;k<arr.length;k++) if (!best || arr[k].innerText.length < best.innerText.length) best = arr[k]; return best; }
    el = smallest(exact) || smallest(part);
  }
  else if (sel.indexOf('path=') === 0) { var pth = document.querySelector(sel.slice(5)); if (pth && vis(pth)) el = pth; }
  if (!el) return { found:false };
  el.scrollIntoView({block:'center'});
  var r = el.getBoundingClientRect();
  return { found:true, rect:{x:r.left,y:r.top,w:r.width,h:r.height}, text:(el.innerText||'').replace(/\\s+/g,' ').trim().slice(0,30), tag:el.tagName };
})(%SEL%)`;

function findExpr(selector) { return FIND_SRC.replace('%SEL%', JSON.stringify(selector)); }

async function findOnce(cdp, selector) {
  const r = await cdp.send('Runtime.evaluate', { expression: findExpr(selector), returnByValue: true });
  if (r.exceptionDetails) throw new Error('找元素的脚本炸了: ' + (r.exceptionDetails.exception && r.exceptionDetails.exception.description || r.exceptionDetails.text).split('\n')[0]);
  return r.result.value || { found: false };
}
async function waitFor(cdp, selector, ms) {
  const end = Date.now() + ms;
  let last = { found: false }, lastErr = null;
  while (Date.now() < end) {
    try {
      last = await findOnce(cdp, selector);
      if (last.found) return last;
    } catch (e) {
      lastErr = e; // 刚自动开的页正在跳转加载，evaluate 短暂没有执行上下文——窗口内忍着继续等，不是吞错
    }
    await sleep(300);
  }
  if (lastErr && !last.found) throw lastErr; // 到点还找不到：把真错误端出来（找元素脚本真炸了不会只报超时）
  return last;
}

// ---------- 真人味点击 ----------
// band=0.4 → 在元素中间 40% 区域随机取点，永远点在元素内
function jitterPoint(rect, band) {
  const b = Math.min(Math.max(band || 0.4, 0.1), 0.9);
  const f = () => 0.5 - b / 2 + b * Math.random();
  return { x: Math.round(rect.x + rect.w * f()), y: Math.round(rect.y + rect.h * f()) };
}
async function humanClick(cdp, pt) {
  await cdp.send('Input.dispatchMouseEvent', { type: 'mouseMoved', x: pt.x, y: pt.y });
  await cdp.send('Input.dispatchMouseEvent', { type: 'mousePressed', x: pt.x, y: pt.y, button: 'left', buttons: 1, clickCount: 1 });
  await sleep(40 + Math.random() * 60); // 按下到松开 40~100ms
  await cdp.send('Input.dispatchMouseEvent', { type: 'mouseReleased', x: pt.x, y: pt.y, button: 'left', buttons: 0, clickCount: 1 });
}

// ---------- loop 执行器（单点循环/路径循环共用） ----------
// 步里带录制页地址（href，v0.1.15 起录制自动带）的脚本按步路由：每步现查档位开着的页面，
// 在配得上录制地址的那页上点；配不上=页面没开/被关了（重启电脑、手滑关页），按录制地址自动开回来再点。
// 懒开页：只有「当前没有任何页配得上这步」才开，点击后页面正常跳转不会被误开新页。
// 老脚本（步里没地址）和钉了 targetId 的走原路径：抓第一个页面从头点到尾。
// v0.1.16：每步外面套重连窗——GUI 点「启动/后台跑」都会先停档再起档，Chrome 一重启连接全断，
// 以前脚本当场报错死掉；现在断了不判死，等档位回来、把录制页自动开回来接着跑。
// 「按钮真找不到」不进重连窗：那是网页改版，立刻停，不许干等也不乱点。
async function runLoop(script, opts, interrupted) {
  const say = opts.onLog || log;
  const RECONNECT_MS = opts.dry ? 8000 : 90000; // 档位先停再起最多十几秒，90 秒窗口给足；试跑只给 8 秒（点错了快点报）
  const route = (script.steps || []).some(s => s && s.href) && !opts.targetId;
  let single = null; // 老路径的页面连接；断了重挂（v0.1.15 前只在开头挂一次）
  const tabs = new Map(); // targetId -> { cdp, fresh }：fresh=刚自动开的页，找元素给长超时等加载
  const pageList = async () => (await jget(opts.port, '/json/list', 2500)).filter(t => t.type === 'page' && !t.url.startsWith('devtools://'));
  async function tabFor(st) {
    if (!route) {
      if (!single || single.ws.readyState !== 1) { if (single) single.close(); single = await attachPage(opts.port, opts.targetId); }
      return { cdp: single, fresh: false };
    }
    const list = await pageList();
    const hit = st.href ? (list.find(t => samePage(t.url, st.href)) || null) : (list[0] || null);
    if (!hit) { // 录制的页不在了：自动开回来——「下次打开点启动，自己恢复网页接着跑」就是这一步
      const tid = await openTabOnPort(opts.port, st.href);
      say('录制页没开，已自动开: ' + st.href);
      const cdp = await attachPage(opts.port, tid);
      tabs.set(tid, { cdp, fresh: true });
      return tabs.get(tid);
    }
    let e = tabs.get(hit.id);
    if (!e || e.cdp.ws.readyState !== 1) { e = { cdp: await attachPage(opts.port, hit.id), fresh: false }; tabs.set(hit.id, e); } // 页还在但连接断了：重挂
    return e;
  }
  try {
    const loops = opts.loop !== undefined ? opts.loop : (script.loop || 0);
    if (loops === 0) say('无限循环模式，停止: POST /script/' + script.id + '/stop');
    let round = 0, clicks = 0;
    const stop = interrupted || (() => false);
    while (!stop() && (loops === 0 || round < loops)) {
      round += 1;
      for (let i = 0; i < script.steps.length; i++) {
        if (stop()) break;
        const st = script.steps[i];
        const cut = Date.now() + RECONNECT_MS; // 档位重启窗口：连接断了重试到窗口尽头
        let saidDown = false;
        for (;;) {
          try {
            const tab = await tabFor(st);
            const waitMs = tab.fresh ? 25000 : 5000; // 刚开的页要等加载，老等待窗不够
            const found = await waitFor(tab.cdp, st.selector, waitMs);
            tab.fresh = false;
            if (!found.found) {
              const err = new Error('第' + round + '轮步骤' + (i + 1) + ' ' + (waitMs / 1000) + '秒找不到 ' + st.selector + '（「' + (st.text || '') + '」）——网页可能改版，中止不乱点');
              err.noRetry = true; // 页面在、按钮真没有：不是连接问题，不许进重连窗干等
              throw err;
            }
            if (opts.dry) {
              say('试跑 第' + round + '轮 ' + (i + 1) + '/' + script.steps.length + ' ✓ 找到「' + found.text + '」（不点击）');
            } else {
              const pt = jitterPoint(found.rect, script.clickJitter);
              await humanClick(tab.cdp, pt);
              clicks += 1;
              say('第' + round + '轮 ' + (i + 1) + '/' + script.steps.length + ' 点「' + found.text + '」@' + pt.x + ',' + pt.y);
            }
            break; // 这步成了，去下一步
          } catch (e) {
            if (e && e.noRetry) throw e;
            if (stop()) break; // 叫停（halt/stopscript）：在重连窗里等着也叫得动——干净收手算跑完，不把断连当出错
            if (Date.now() > cut) throw e; // 到窗口尽头还没回来（档被彻底停了）：把原始错误交出去
            if (!saidDown) { say('档位连接断了（可能在切窗口↔后台/重启），最多等 ' + Math.round(RECONNECT_MS / 1000) + ' 秒回来接着跑'); saidDown = true; }
            await sleep(1500);
          }
        }
        await sleep((script.delayMs || 1200) + Math.random() * (script.jitterMs === undefined ? 800 : script.jitterMs));
      }
    }
    return { rounds: round, clicks };
  } finally {
    if (single) single.close(); // 不关 WebSocket 进程会吊着不退出
    for (const e of tabs.values()) e.cdp.close();
  }
}

// ---------- watch 执行器（数据触发） ----------
function cellWatchExpr(w) {
  return `(function(){
  var cfg = ${JSON.stringify(w)};
  function num(s){ var m = String(s||'').replace(/,/g,'').match(/-?\\d+(\\.\\d+)?/); return m ? parseFloat(m[0]) : null; }
  var rows = document.querySelectorAll('tr');
  var row = null;
  for (var i=0;i<rows.length;i++){ if ((rows[i].innerText||'').indexOf(cfg.rowText) >= 0) { row = rows[i]; break; } }
  if (!row) return { hit:false, why:'没找到包含「'+cfg.rowText+'」的行' };
  var table = row.closest('table');
  var heads = table ? Array.prototype.map.call(table.querySelectorAll('thead th'), function(th){ return (th.innerText||'').trim(); }) : [];
  var cells = row.querySelectorAll('td');
  var idx = heads.indexOf(cfg.columnHeader);
  var cell = (idx >= 0) ? cells[idx] : null;
  var val = cell ? num(cell.innerText) : null;
  if (val === null) {
    for (var c=1;c<cells.length;c++){ var v2 = num(cells[c].innerText); if (v2 !== null) { val = v2; cell = cells[c]; break; } }
  }
  if (val === null) return { hit:false, why:'「'+cfg.rowText+'」行里没解析出数字' };
  var pass = cfg.op === '<=' ? val <= cfg.value : cfg.op === '<' ? val < cfg.value : cfg.op === '>' ? val > cfg.value : val >= cfg.value;
  if (!pass) return { hit:false, num:val };
  var btns = row.querySelectorAll('button, a, [role=button]');
  var btn = null;
  for (var b=0;b<btns.length;b++){
    var t = (btns[b].innerText||'').trim();
    if (t === cfg.clickText) { btn = btns[b]; break; }
    if (!btn && t.indexOf(cfg.clickText) >= 0) btn = btns[b];
  }
  if (!btn) return { hit:false, num:val, why:'数值'+val+'达标但行里没有「'+cfg.clickText+'」按钮' };
  btn.scrollIntoView({block:'center'});
  var r = btn.getBoundingClientRect();
  return { hit:true, num:val, text:(btn.innerText||'').trim(), rect:{x:r.left,y:r.top,w:r.width,h:r.height} };
})()`;
}

async function runWatch(script, opts, interrupted) {
  const say = opts.onLog || log;
  const w = script.watch;
  const cdp = await attachPage(opts.port, opts.targetId);
  try {
    const stop = interrupted || (() => false);
    const deadline = opts.timeoutMs ? Date.now() + opts.timeoutMs : 0;
    let armed = true, hits = 0, lastMsg = '';
    const every = ((w.intervalMs || 10000) / 1000).toFixed(1);
    const once = msg => { if (msg !== lastMsg) { say(msg); lastMsg = msg; } };
    if (w.mode === 'cell') {
      say('盯表：每' + every + 's 查「' + w.rowText + '」行的' + w.columnHeader + ' ' + (w.op || '>=') + ' ' + w.value + ' → 点该行「' + w.clickText + '」');
    } else {
      say('盯表（自定义表达式）：每' + every + 's 查一次');
    }
    while (!stop()) {
      if (deadline && Date.now() > deadline) return { hits, timeout: true };
      let r;
      if (w.mode === 'expr') {
        const ev = await cdp.send('Runtime.evaluate', { expression: w.expr, returnByValue: true, awaitPromise: true });
        if (ev.exceptionDetails) throw new Error('watch 表达式炸了: ' + (ev.exceptionDetails.exception && ev.exceptionDetails.exception.description || ev.exceptionDetails.text).split('\n')[0]);
        r = ev.result.value || { hit: false };
      } else {
        const ev = await cdp.send('Runtime.evaluate', { expression: cellWatchExpr(w), returnByValue: true });
        if (ev.exceptionDetails) throw new Error('盯表脚本炸了: ' + (ev.exceptionDetails.exception && ev.exceptionDetails.exception.description || ev.exceptionDetails.text).split('\n')[0]);
        r = ev.result.value || { hit: false };
      }
      if (r.hit) {
        if (armed) {
          let pt;
          if (r.rect) pt = jitterPoint(r.rect, script.clickJitter);
          else pt = { x: Math.round(r.x + Math.random() * 6 - 3), y: Math.round(r.y + Math.random() * 6 - 3) };
          if (opts.dry) { say('试跑：达标 num=' + r.num + ' → 会点「' + (r.text || '?') + '」@' + pt.x + ',' + pt.y + '（不点击）'); return { hits: 0 }; }
          await humanClick(cdp, pt);
          hits += 1; armed = false;
          say('达标 num=' + r.num + ' → 点「' + (r.text || '?') + '」@' + pt.x + ',' + pt.y + ' ✓（第' + hits + '次）');
          if (opts.once) return { hits };
          await sleep(w.cooldownMs === undefined ? 3000 : w.cooldownMs);
        }
      } else {
        if (!armed && (r.num !== undefined || r.why)) { armed = true; say('条件回落，重新武装' + (r.num !== undefined ? '（当前 ' + r.num + '）' : '')); }
        else if (r.why) once('注意: ' + r.why);
      }
      await sleep(w.intervalMs || 10000);
    }
    return { hits };
  } finally {
    cdp.close(); // 不关 WebSocket 进程会吊着不退出
  }
}

async function runScript(script, opts, interrupted) {
  if (script.type === 'watch') return runWatch(script, opts, interrupted);
  return runLoop(script, opts, interrupted);
}

// ---------- 脚本存取 ----------
function saveScript(sc) {
  fs.mkdirSync(SCRIPTS_DIR, { recursive: true });
  const safe = (sc.name || '').replace(/[\\/:*?"<>|\s]+/g, '');
  const file = path.join(SCRIPTS_DIR, sc.id + '-' + (safe || '未命名') + '.json');
  fs.writeFileSync(file, JSON.stringify(sc, null, 2));
  return file;
}
function loadScript(id) {
  if (!fs.existsSync(SCRIPTS_DIR)) throw new Error('还没有任何脚本，先 record 或 build');
  const hits = fs.readdirSync(SCRIPTS_DIR).filter(f => f.startsWith(String(id) + '-'));
  if (!hits.length) throw new Error('没有编号 ' + id + ' 的脚本，用 scripts 命令看看');
  if (hits.length > 1) throw new Error('编号 ' + id + ' 对上好几个文件: ' + hits.join(', '));
  return JSON.parse(fs.readFileSync(path.join(SCRIPTS_DIR, hits[0]), 'utf8'));
}
function deleteScript(id) {
  if (!fs.existsSync(SCRIPTS_DIR)) throw new Error('还没有任何脚本，先 record 或 build');
  const hits = fs.readdirSync(SCRIPTS_DIR).filter(f => f.startsWith(String(id) + '-'));
  if (!hits.length) throw new Error('没有编号 ' + id + ' 的脚本，用 scripts 命令看看');
  if (hits.length > 1) throw new Error('编号 ' + id + ' 对上好几个文件: ' + hits.join(', '));
  const file = path.join(SCRIPTS_DIR, hits[0]);
  fs.rmSync(file);
  return file;
}
function nextId() {
  fs.mkdirSync(SCRIPTS_DIR, { recursive: true });
  const ids = fs.readdirSync(SCRIPTS_DIR).map(f => Number((f.match(/^(\d+)-/) || [])[1]) || 0);
  return String((ids.length ? Math.max.apply(null, ids) : 0) + 1).padStart(2, '0');
}
function listScripts() {
  if (!fs.existsSync(SCRIPTS_DIR)) return [];
  return fs.readdirSync(SCRIPTS_DIR).filter(f => f.endsWith('.json')).sort().map(f => {
    try { return JSON.parse(fs.readFileSync(path.join(SCRIPTS_DIR, f), 'utf8')); }
    catch (e) { return { id: '?', name: f + ' 解析失败: ' + e.message, type: '?' }; }
  });
}

// 存 Agent 笔记：录制不进脚本体系，落一份 agent 直接读的 markdown（步骤表+抓到的接口+原始 JSON）
// agent 拿到能干嘛：按步骤用 open/eval 复现、看接口清单判断哪步转纯后台直调、想挂机就照原始 JSON 转脚本
function saveAgentNote(dir, nm, meta, steps, apis) {
  fs.mkdirSync(dir, { recursive: true });
  const safe = String(nm || '').replace(/[\\/:*?"<>|\u0000-\u001f]/g, '').trim().slice(0, 40) || '未命名';
  const t = new Date();
  const p2 = n => String(n).padStart(2, '0');
  const stamp = p2(t.getMonth() + 1) + p2(t.getDate()) + '-' + p2(t.getHours()) + p2(t.getMinutes()) + p2(t.getSeconds());
  let file = path.join(dir, safe + '-' + stamp + '.md');
  for (let i = 2; fs.existsSync(file); i++) file = path.join(dir, safe + '-' + stamp + '-' + i + '.md'); // 同名同秒不覆盖
  const rows = steps.map((s, i) => '| ' + (i + 1) + ' | ' + (s.text || '') + ' | `' + (s.selector || '') + '` | ' + (s.href || '') + ' |').join('\n');
  const apiRows = (apis || []).map(a => '| ' + a.method + ' | ' + (a.status == null ? '?' : a.status) + ' | ' + a.count + ' | ' + a.url + ' |').join('\n');
  const md = [
    '# 录制笔记：' + safe,
    '',
    '- 时间：' + t.toLocaleString('zh-CN'),
    '- 档位：' + ((meta && meta.slotId) || '?') + ((meta && meta.note) ? '（账号：' + meta.note + '）' : ''),
    '- 步数：' + steps.length + ((apis && apis.length) ? '，录制期间抓到 ' + apis.length + ' 个接口' : ''),
    '- 这份是给人手上的 agent 读的操作记录，**不是农场脚本，不会自动跑**。想循环挂机：把底部原始 JSON 交 POST /script/new 转成脚本。',
    '',
    '## 人点了一遍什么',
    '| # | 点什么 | 选择器 | 所在页面 |',
    '|---|---|---|---|',
    rows,
  ].concat((apis && apis.length) ? [
    '',
    '## 录制期间背后的接口（次数多的多半是数据轮询，最值得转纯后台直调）',
    '| 方法 | 状态 | 次数 | URL |',
    '|---|---|---|---|',
    apiRows,
  ] : []).concat([
    '',
    '## 原始 steps（JSON，转脚本直接用）',
    '```json',
    JSON.stringify(steps.map(s => ({ selector: s.selector, text: s.text, tag: s.tag, href: s.href || null })), null, 2),
    '```',
    '',
  ]).join('\n');
  fs.writeFileSync(file, md, 'utf8');
  return file;
}

// 农场录制产物 → forge(record-to-skill) 录制格式 rec.json：脚本/存Agent笔记的 steps+apis
// 直接喂 forge 的 evidence 打分→probe 探查→build 建包管线（桥的另一头是 farm.js 的 forge 命令，
// 两边谁也不用改对面）。字段契约按 forge evidence.mjs 实际读取面：actions[seq/type/at/text/selector/locator/page]
// + network[at/method/url/status/body]，at 用它认的 HH:MM:SS。
function toForgeRec(steps, apis, name, meta) {
  const pad = n => String(n).padStart(2, '0');
  const sec2hms = s => pad(Math.floor(s / 3600)) + ':' + pad(Math.floor(s / 60) % 60) + ':' + pad(s % 60);
  const hms2sec = t => {
    const m = String(t || '').match(/^(\d{1,2}):(\d{2}):(\d{2})/);
    return m ? (+m[1]) * 3600 + (+m[2]) * 60 + (+m[3]) : NaN;
  };
  const nets = [];
  for (const a of (apis || [])) {
    const n = Math.min(Math.max(a.count || 1, 1), 20); // 轮询重复次数保留（evidence 靠重复度认数据源），封顶 20 防膨胀
    for (let i = 0; i < n; i++) nets.push({ at: a.tsUTC || '', method: a.method || 'GET', url: a.url, status: a.status == null ? 0 : a.status, body: a.postData || null });
  }
  const times = nets.map(r => hms2sec(r.at)).filter(Number.isFinite);
  const base = times.length ? Math.max(0, Math.min(...times) - steps.length) : 0; // 动作顺序铺在第一条接口之前，时间线才不倒挂
  const actions = steps.map((s, i) => ({
    seq: i + 1, type: 'click', at: sec2hms(base + i),
    text: s.text || '', selector: s.selector || '', locator: { best: s.selector || null },
    page: s.href || '', url: s.href || '',
  }));
  return {
    meta: { name: name || 'farm-rec', finishedAt: new Date().toISOString(), from: 'browser-farm' + ((meta && meta.slotId) ? ' 档' + meta.slotId : '') },
    actions, network: nets,
  };
}

module.exports = {
  Cdp, attachPage, jget, samePage, openTabOnPort, recordSession, barSession, runScript, runLoop, runWatch,
  cellWatchExpr, findExpr, findOnce, waitFor, jitterPoint, humanClick,
  saveScript, loadScript, deleteScript, nextId, listScripts, saveAgentNote, toForgeRec,
};
