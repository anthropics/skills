/* recorder.js — CDP 注入式网页操作录制器 v2（无扩展 / 无 Node 依赖）
 * v1 底子来自作者前代录制项目（六级定位/去重/探针），v2 新增数据流抓取：
 *   - paste：贴进来的整块内容（含 \t \n 结构）+ 落点的表格上下文 → 供映射推断按"值"对齐
 *   - copy ：在页面里复制走了什么（平台页选中→复制→贴去在线表 这条链的关键一环）
 *   - download：点了指向表格/压缩包的链接 → 记 href + 猜文件名（真文件名由 CDP 下载事件给）
 * 用法：
 *   1) 把本文件全文作为表达式在页面执行一次
 *   2) __SOP_start()  开始录制（清空）
 *   3) 正常操作页面（click / 输入 / 下拉 / 勾选 / 粘贴 / 复制 / 下载 自动记录）
 *   4) __SOP_dump()   返回 actions JSON 字符串
 * 换页（含 SPA 路由跳转）会丢掉 window.__SOP，需在新页重新注入（record.mjs 会自动补）。
 */
(function () {
  if (window.__SOP) { return 'already-injected'; }

  var S = window.__SOP = {
    actions: [],
    notes: [],
    on: false,
    t0: 0,
    lastUrl: location.href,
    navTimer: null
  };

  /* ---------- 6 级定位器 ---------- */
  function validId(id) {
    return id && /^[A-Za-z0-9_\-]+$/.test(id) && !/^[0-9]/.test(id);
  }

  function nthPath(el) {
    var parts = [];
    var cur = el;
    var guard = 0;
    while (cur && cur.nodeType === 1 && guard++ < 12) {
      if (validId(cur.id)) { parts.unshift('#' + cur.id); break; }
      var tag = cur.tagName.toLowerCase();
      var idx = 1;
      var sib = cur;
      while ((sib = sib.previousElementSibling)) {
        if (sib.tagName === cur.tagName) { idx++; }
      }
      parts.unshift(tag + ':nth-of-type(' + idx + ')');
      cur = cur.parentElement;
    }
    return parts.join(' > ');
  }

  function cssOf(el) {
    var tag = el.tagName.toLowerCase();
    var cls = (el.className && typeof el.className === 'string')
      ? el.className.trim().split(/\s+/).filter(function (c) { return c && c.length < 40; }).slice(0, 2)
      : [];
    var base = tag + (cls.length ? '.' + cls.join('.') : '');
    try {
      var n = document.querySelectorAll(base).length;
      return n > 1 ? base + ' [non-unique:' + n + ']' : base;
    } catch (e) { return base; }
  }

  function inferRole(el) {
    var tag = el.tagName.toLowerCase();
    var role = el.getAttribute('role');
    if (role) { return role; }
    if (tag === 'button') { return 'button'; }
    if (tag === 'a') { return 'link'; }
    if (tag === 'input') {
      var t = (el.type || '').toLowerCase();
      if (t === 'checkbox' || t === 'radio') { return t; }
      if (t === 'submit' || t === 'button') { return 'button'; }
    }
    return null;
  }

  function visibleText(el) {
    var t = (el.innerText || el.textContent || '').replace(/\s+/g, ' ').trim();
    return t.length > 60 ? t.slice(0, 60) : t;
  }

  function collectLocators(el) {
    var r = { L1_id: null, L2_testid: null, L3_role: null, L4_text: null, L5_css: null, L6_nth_path: null, best: null };
    if (el.id && validId(el.id)) { r.L1_id = '#' + el.id; }
    var tids = ['data-testid', 'data-test', 'data-qa', 'data-cy'];
    for (var i = 0; i < tids.length; i++) {
      var v = el.getAttribute(tids[i]);
      if (v) { r.L2_testid = '[' + tids[i] + '="' + v + '"]'; break; }
    }
    var role = inferRole(el);
    var name = el.getAttribute('aria-label') || visibleText(el);
    if (role && name) { r.L3_role = role + '[name="' + name.slice(0, 40) + '"]'; }
    var tag = el.tagName.toLowerCase();
    if ((tag === 'button' || tag === 'a') && name) { r.L4_text = name; }
    r.L5_css = cssOf(el);
    r.L6_nth_path = nthPath(el);
    /* 元素快照（改版后能回答「当时那个按钮长什么样」）：只留必要特征，300 字封顶 */
    try {
      var rect = el.getBoundingClientRect ? el.getBoundingClientRect() : null;
      r.snapshot = {
        html: (el.outerHTML || '').replace(/\s+/g, ' ').slice(0, 300),
        tag: tag,
        role: role || '',
        name: (name || '').slice(0, 60),
        text: (visibleText(el) || '').slice(0, 60),
        cls: (el.className && typeof el.className === 'string') ? el.className.trim().slice(0, 80) : '',
        type: el.getAttribute ? (el.getAttribute('type') || '') : '',
        placeholder: el.getAttribute ? (el.getAttribute('placeholder') || '') : '',
        rect: rect ? [Math.round(rect.x), Math.round(rect.y), Math.round(rect.width), Math.round(rect.height)] : null,
        at: new Date().toISOString().slice(0, 19)
      };
    } catch (e) { r.snapshot = null; }
    var best = r.L1_id || r.L2_testid || r.L3_role || r.L4_text;
    if (!best) { best = (r.L5_css || '').replace(/ \[non-unique:\d+\]/, ''); }
    r.best = best || r.L6_nth_path || tag;
    return r;
  }

  /* ---------- 上下文：字段名 / 区域 / 弹窗 ---------- */
  function fieldLabel(el) {
    var aria = el.getAttribute('aria-label');
    if (aria) { return aria.trim(); }
    var ph = el.getAttribute('placeholder');
    if (el.id) {
      var lab = document.querySelector('label[for="' + el.id + '"]');
      if (lab) { return visibleText(lab); }
    }
    var box = el.closest('.el-form-item, .ant-form-item, .form-item, .form-group, td, li');
    if (box) {
      var l = box.querySelector('label, .el-form-item__label, .ant-form-item-label, .form-label, .label');
      if (l) { var t = visibleText(l).replace(/[:：]\s*$/, ''); if (t) { return t; } }
    }
    return ph || '';
  }

  function sectionOf(el) {
    var tab = document.querySelector('.el-tabs__item.is-active, [aria-selected="true"], .tab-item.active, .nav-item.active');
    var tabText = tab ? visibleText(tab) : '';
    var holder = el.closest('.el-form, form, fieldset, section, .panel, .card');
    var title = '';
    if (holder) {
      var h = holder.querySelector('legend, .section-title, .panel-title, .card-title, h3, h4');
      if (h) { title = visibleText(h); }
    }
    return [tabText, title].filter(Boolean).join(' / ');
  }

  function popupOf(el) {
    var dlg = el.closest('[role="dialog"], .el-dialog, .el-drawer, .ant-modal, .ant-drawer, .modal, .drawer, .layui-layer');
    if (!dlg) { return ''; }
    var id = dlg.id ? '#' + dlg.id : '';
    var t = dlg.querySelector('.el-dialog__title, .ant-modal-title, .el-drawer__title, .modal-title, .layui-layer-title, h3, h4');
    var title = t ? visibleText(t) : '';
    return (title || '弹窗') + (id ? ' (' + id + ')' : '');
  }

  /* ---------- 记录 ---------- */
  function push(type, el, extra) {
    if (!S.on) { return; }
    var loc = collectLocators(el);
    // 去重：下拉/勾选/输入前那次点击是"打开控件"的噪声，同一元素 3 秒内直接吞掉
    if (type !== 'click' && S.actions.length) {
      var prev = S.actions[S.actions.length - 1];
      if (prev.type === 'click' && prev.locator && prev.locator.best && prev.locator.best === loc.best) {
        S.actions.pop();
      }
    }
    var a = {
      seq: S.actions.length + 1,
      type: type,
      at: new Date().toISOString().slice(11, 19),
      url: location.href,
      locator: loc,
      label: fieldLabel(el),
      section: sectionOf(el),
      popup: popupOf(el),
      inFrame: (window.top !== window.self)
    };
    if (extra) { for (var k in extra) { a[k] = extra[k]; } }
    S.actions.push(a);
    /* 浮标即时反馈（权威计数由驱动侧推送覆盖） */
    var desc = a.text
      || (a.type === 'paste' ? ('粘贴 ' + (a.rows || 0) + ' 行 × ' + (a.cols || 0) + ' 列') : '')
      || (a.type === 'fill' ? ('填写「' + (a.label || '') + '」') : '')
      || (a.type === 'copy' ? ('复制 ' + (a.rows || 0) + ' 行') : '')
      || (a.type === 'download' ? ('下载 ' + (a.filename || '')) : '')
      || a.label || a.type;
    hudLog(ICON[a.type] || '•', String(desc).slice(0, 40));
    hudRefresh();
  }

  function isHud(e) {
    if (!hud.host) { return false; }
    var path = e.composedPath ? e.composedPath() : null;
    if (path && path.indexOf(hud.host) >= 0) { return true; }
    return e.target === hud.host;
  }

  function onClick(e) {
    if (isHud(e)) { return; }
    var el = e.target;
    if (!el || el.nodeType !== 1) { return; }
    var dl = downloadInfo(el);
    if (dl) { push('download', el, dl); return; }
    if (el.tagName === 'INPUT' && /^(checkbox|radio)$/i.test(el.type)) {
      push('check', el, { value: el.checked ? '勾选' : '取消勾选', text: fieldLabel(el) });
      return;
    }
    push('click', el, { text: visibleText(el) });
  }

  /* ---------- v2：数据流抓取（下载 / 粘贴 / 复制） ---------- */

  // 链接指向表格/压缩包或带 download 属性 = 一次下载动作
  function downloadInfo(el) {
    if (!el.closest) { return null; }
    var a = el.closest('a[href]');
    if (!a) { return null; }
    var href = a.getAttribute('href') || '';
    var forced = a.hasAttribute('download');
    if (!forced && !/\.(xlsx?|csv|tsv|zip)([?#]|$)/i.test(href)) { return null; }
    var fname = a.getAttribute('download') || href.split('/').pop().split('?')[0] || '';
    return { href: href.slice(0, 300), filename: decodeURIComponent(fname).slice(0, 200), text: visibleText(a) };
  }

  // 粘贴落点的表格上下文：在线表格各家 DOM 都不一样，只抓通用的（行列属性/表头/位置），
  // 列对齐靠分析层按"值"匹配，不依赖这里猜准格子
  function gridContextOf(el) {
    var ctx = { host: location.host, docTitle: document.title, cell: null, header: '' };
    var sels = ['td', '[role="gridcell"]', '[data-row]', '[data-cell]', '[class*="cell"]'];
    var cell = null;
    for (var i = 0; i < sels.length; i++) {
      try { cell = el.closest(sels[i]); } catch (e2) { cell = null; }
      if (cell) { break; }
    }
    if (!cell) { cell = el; }
    var r = cell.getBoundingClientRect();
    ctx.cell = {
      rowAttr: cell.getAttribute('data-row') || cell.getAttribute('data-row-index') || cell.getAttribute('aria-rowindex') || '',
      colAttr: cell.getAttribute('data-col') || cell.getAttribute('data-col-index') || cell.getAttribute('aria-colindex') || '',
      cls: ((typeof cell.className === 'string') ? cell.className : '').slice(0, 120),
      rect: [Math.round(r.x), Math.round(r.y), Math.round(r.width), Math.round(r.height)]
    };
    if (cell.tagName === 'TD' && cell.cellIndex >= 0) {
      var tr = cell.closest('tr');
      var head = tr ? tr.parentElement.querySelector('thead th:nth-child(' + (cell.cellIndex + 1) + ')') : null;
      if (head) { ctx.header = visibleText(head).slice(0, 40); }
    }
    return ctx;
  }

  function onPaste(e) {
    if (!S.on || isHud(e)) { return; }
    var el = e.target;
    if (!el || el.nodeType !== 1) { return; }
    var text = e.clipboardData ? e.clipboardData.getData('text/plain') : '';
    if (!text) { return; }
    var lines = text.split(/\r?\n/);
    var cols = 0;
    for (var i = 0; i < lines.length; i++) {
      var c = lines[i].split('\t').length;
      if (c > cols) { cols = c; }
    }
    push('paste', el, {
      value: text.slice(0, 8000),
      rows: lines.length,
      cols: cols,
      grid: gridContextOf(el)
    });
  }

  function onCopy(e) {
    if (!S.on || isHud(e || {})) { return; }
    var text = window.getSelection ? String(window.getSelection()) : '';
    text = text.replace(/\r/g, '');
    if (!text.trim()) { return; }
    var lines = text.split('\n');
    var cols = 1;
    for (var i = 0; i < lines.length; i++) {
      var c = lines[i].split('\t').length;
      if (c > cols) { cols = c; }
    }
    /* 复制内容可能含敏感信息：--no-copy-text 时只记结构（行/列/字数），不留原文 */
    var redact = !!(window.__SOP_CFG && window.__SOP_CFG.redactCopy);
    push('copy', document.activeElement || document.body, redact
      ? { rows: lines.length, cols: cols, chars: text.length, redacted: true }
      : { value: text.slice(0, 8000), rows: lines.length, cols: cols });
  }

  function onChange(e) {
    if (isHud(e)) { return; }
    var el = e.target;
    if (!el || el.nodeType !== 1) { return; }
    var tag = el.tagName.toLowerCase();
    if (tag === 'select') {
      var opt = el.options[el.selectedIndex];
      push('select', el, { value: opt ? visibleText(opt) : el.value });
      return;
    }
    if (tag === 'input' || tag === 'textarea') {
      if (/^(checkbox|radio)$/i.test(el.type)) { return; }
      if (el.type === 'file') { push('upload', el, { value: el.value || '(未取到路径)' }); return; }
      push('fill', el, { value: el.value });
    }
  }

  function pollNav() {
    if (!S.on) { return; }
    if (location.href !== S.lastUrl) {
      S.lastUrl = location.href;
      S.actions.push({
        seq: S.actions.length + 1,
        type: 'nav',
        at: new Date().toISOString().slice(11, 19),
        url: location.href,
        locator: { best: null },
        label: document.title,
        section: '',
        popup: '',
        inFrame: (window.top !== window.self)
      });
    }
  }

  function bind(on) {
    var m = on ? 'addEventListener' : 'removeEventListener';
    document[m]('click', onClick, true);
    document[m]('change', onChange, true);
    document[m]('paste', onPaste, true);
    document[m]('copy', onCopy, true);
    if (on) {
      S.navTimer = setInterval(pollNav, 800);
    } else if (S.navTimer) {
      clearInterval(S.navTimer);
      S.navTimer = null;
    }
  }

  /* ---------- 页面内浮标（HUD）：看得见在不在录、录了几条、能开始/停止/撤销/写备注 ----------
   * 样式对齐常见运营后台面板：标题栏 + 蓝色状态 + 计数 + 大按钮 + 灰底日志。
   * 用 Shadow DOM 隔离，避免被站点 CSS 改样；所有指到浮标的点击/输入一律不记录。
   * 三段状态：待机（还没点开始）→ 录制中 → 已停止（正在保存）。
   * 备注：输入框写「这步是干什么 / 规则」，默认挂到最近一步；点日志某一行可改挂到那一步。 */
  var HUD_ID = '__sop_hud_host';
  var ICON = { click: '▶', fill: '✎', paste: '▤', copy: '⧉', download: '⬇', select: '▾', check: '✔', upload: '⬆', nav: '→' };
  var hud = { host: null, root: null, mini: false, logN: 0, net: 0 };

  function esc(s) {
    return String(s == null ? '' : s).replace(/[&<>\"]/g, function (c) {
      return { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c];
    });
  }

  function hudCss() {
    return ''
      + '.card{position:fixed;top:14px;right:14px;width:340px;box-sizing:border-box;background:#fff;color:#1f2329;'
      + 'border:1px solid #e5e6eb;border-radius:12px;box-shadow:0 10px 30px rgba(0,0,0,.2);'
      + 'font:12px/1.6 -apple-system,BlinkMacSystemFont,"Microsoft YaHei",sans-serif;overflow:hidden}'
      + '.hd{display:flex;align-items:center;gap:8px;padding:12px 14px 4px}'
      + '.dot{width:8px;height:8px;border-radius:50%;background:#a9aeb8;flex:0 0 auto}'
      + '.dot.rec{background:#f5222d;animation:bl 1.2s infinite}'
      + '@keyframes bl{0%,100%{opacity:1}50%{opacity:.25}}'
      + '.ttl{font-weight:700;font-size:14px;flex:1;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}'
      + '.ops{display:flex;gap:6px;flex:0 0 auto}'
      + 'button{font:inherit;cursor:pointer;border-radius:6px;padding:4px 10px;border:1px solid #d0d3d9;background:#f7f8fa;color:#1f2329}'
      + 'button:disabled{opacity:.45;cursor:default}'
      + '.st{padding:4px 14px 0;color:#1677ff;font-weight:700;font-size:13px}'
      + '.st.idle{color:#86909c}.st.pause{color:#fa8c16}.st.done{color:#00a870}'
      + '.bar{height:3px;margin:6px 14px 0;border-radius:2px;background:#f2f3f5;overflow:hidden;display:none}'
      + '.bar.on{display:block}.bar i{display:block;height:100%;width:38%;background:#1677ff;animation:sl 1.4s linear infinite}'
      + '@keyframes sl{0%{margin-left:-38%}100%{margin-left:100%}}'
      + '.cnt{padding:6px 14px 0;color:#4e5969}'
      + '.cur{padding:2px 14px 8px;color:#86909c;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}'
      + '.note{display:flex;gap:6px;margin:0 14px 8px}'
      + '.note input{flex:1;min-width:0;font:inherit;padding:6px 8px;border:1px solid #d0d3d9;border-radius:6px;color:#1f2329}'
      + '.note button{white-space:nowrap;border-color:#1677ff;color:#1677ff;background:#f0f6ff}'
      + '.big{margin:0 14px 8px;width:calc(100% - 28px);padding:10px 0;font-size:14px;font-weight:700;'
      + 'color:#fff;border:0;border-radius:8px;background:#ff8f1f}'
      + '.big.stop{background:#ff4d4f}.big.done{background:#c9cdd4}'
      + '.tools{display:flex;gap:6px;margin:0 14px 8px}'
      + '.tools button{flex:1}'
      + '.log{margin:0 14px 12px;height:104px;overflow-y:auto;border:1px solid #e5e6eb;border-radius:8px;'
      + 'background:#fafbfc;padding:6px 8px;font:11px/1.65 Consolas,Menlo,monospace;color:#4e5969}'
      + '.ln{white-space:nowrap;overflow:hidden;text-overflow:ellipsis;cursor:pointer;padding:0 2px;border-radius:3px}'
      + '.ln:hover{background:#f0f2f5}.ln.sel{background:#fff7e6;color:#ad6800;font-weight:700}'
      + '.ln.empty{color:#a9aeb8;cursor:default}.ln.empty:hover{background:none}'
      + '.ln .nt{color:#1677ff}'
      + '.card.mini{width:auto;border-radius:999px}.card.mini .st,.card.mini .bar,.card.mini .cnt,.card.mini .cur,'
      + '.card.mini .note,.card.mini .big,.card.mini .tools,.card.mini .log{display:none}.card.mini .hd{padding:6px 10px}'
      + '.card.mini .ttl{font-size:12px}.card.mini .dot{animation:none}';
  }

  function buildHud(name) {
    if (hud.host && document.documentElement && document.documentElement.contains(hud.host)) { return; }
    /* 注入时机可能早到 documentElement 还没生成（readyState=loading）：等 DOM 就绪再挂，
       否则 setHudStatus/用户点「开始录制」都无从下手，录制器等于瞎跑（2026-11-10 实测） */
    if (!document.documentElement) {
      if (!hud.waitingDom) {
        hud.waitingDom = true;
        var remount = function () {
          hud.waitingDom = false;
          try { buildHud(S.linkName || name || ''); setHudStatus('待机：点下面「开始录制」我才开始记', 'idle'); } catch (e) { /* 页面不让挂就静默 */ }
        };
        document.addEventListener('DOMContentLoaded', remount, { once: true });
        window.addEventListener('load', remount, { once: true });
      }
      return;
    }
    var host = document.createElement('div');
    host.id = HUD_ID;
    host.style.cssText = 'position:fixed;top:0;left:0;width:0;height:0;z-index:2147483647;';
    var root;
    try { root = host.attachShadow({ mode: 'open' }); }
    catch (e) { return; }   // 极老内核没有 shadow DOM：宁可不显示，也不能挡住页面
    root.innerHTML = '<style>' + hudCss() + '</style>'
      + '<div class="card" id="card">'
      + '<div class="hd"><span class="dot" id="dot"></span><span class="ttl" id="ttl">网页操作录制' + (name ? ' · ' + esc(name) : '') + '</span>'
      + '<span class="ops"><button id="bfold">收起</button></span></div>'
      + '<div class="st idle" id="st">待机：点下面「开始录制」我才开始记</div>'
      + '<div class="bar" id="bar"><i></i></div>'
      + '<div class="cnt" id="cnt">动作 0 · 请求 0 · 备注 0</div>'
      + '<div class="cur" id="cur">等你点「开始录制」</div>'
      + '<div class="note"><input id="notein" placeholder="这步干什么？有规则也写上（预算 80% 改 200）"><button id="bnote">记下</button></div>'
      + '<button class="big" id="bstop">开始录制</button>'
      + '<div class="tools"><button id="btoggle" disabled>暂停</button><button id="bundo" disabled>撤销上一步</button></div>'
      + '<div class="log" id="log"><div class="ln empty">操作会一条条出现在这里，点一行可以给那一步写备注</div></div>'
      + '</div>';
    (document.documentElement || document.body).appendChild(host);
    hud.host = host; hud.root = root;

    /* 主按钮：待机→开始录制；录制中→停止录制；已停止→禁用 */
    root.getElementById('bstop').addEventListener('click', function () {
      var b = root.getElementById('bstop');
      if (S.stopReq) { return; }
      if (!S.armed) { window.__SOP_start(); return; }
      S.stopReq = true;
      S.on = false; bind(false);
      b.textContent = '已停止，正在保存…'; b.className = 'big done'; b.disabled = true;
      var t = root.getElementById('btoggle'); if (t) { t.disabled = true; }
      var u = root.getElementById('bundo'); if (u) { u.disabled = true; }
      setHudStatus('已停止，正在保存…', 'done');
      hudLog('⏹', '你点了停止录制，正在保存');
    });
    root.getElementById('bfold').addEventListener('click', function () {
      hud.mini = !hud.mini;
      root.getElementById('card').classList.toggle('mini', hud.mini);
      root.getElementById('bfold').textContent = hud.mini ? '展开' : '收起';
    });
    root.getElementById('btoggle').addEventListener('click', function () {
      var b = root.getElementById('btoggle');
      if (!S.armed) { hudLog('·', '还没开始录制'); return; }
      if (S.on) {
        S.on = false; S.pausedByUser = true; bind(false);
        b.textContent = '继续'; setHudStatus('已暂停（操作不会被记录）', 'pause');
        hudLog('⏸', '已暂停');
      } else {
        S.on = true; S.pausedByUser = false; bind(true);
        b.textContent = '暂停'; setHudStatus('正在录制…', '');
        hudLog('▶', '继续录制');
      }
    });
    root.getElementById('bundo').addEventListener('click', function () { window.__SOP_undo(); });
    /* 点日志某一行 = 选中那一步，接下来写的备注挂到它身上 */
    root.getElementById('log').addEventListener('click', function (e) {
      var t = e.target;
      while (t && t !== this && !(t.getAttribute && t.getAttribute('data-seq'))) { t = t.parentElement; }
      if (!t || t === this) { return; }
      var seq = Number(t.getAttribute('data-seq'));
      if (!seq) { return; }
      S.noteTarget = (S.noteTarget === seq) ? 0 : seq;
      var lines = this.querySelectorAll('.ln');
      for (var i = 0; i < lines.length; i++) { lines[i].classList.toggle('sel', Number(lines[i].getAttribute('data-seq')) === S.noteTarget); }
      var inp = hud.root.getElementById('notein');
      if (inp) { inp.placeholder = S.noteTarget ? ('给第 ' + S.noteTarget + ' 步写备注（这步干什么 / 规则）') : '这步干什么？有规则也写上（预算 80% 改 200）'; }
    });
    /* 备注：默认挂最近一步；选中了某行就挂那一行 */
    var noteBtn = root.getElementById('bnote');
    var noteIn = root.getElementById('notein');
    if (noteBtn) { noteBtn.addEventListener('click', function () { addNote(noteIn ? noteIn.value : ''); if (noteIn) { noteIn.value = ''; } }); }
    if (noteIn) {
      noteIn.addEventListener('keydown', function (e) {
        if (e.key === 'Enter') { e.preventDefault(); e.stopPropagation(); addNote(noteIn.value); noteIn.value = ''; }
      });
    }
  }

  /* 备注落点：选中步 > 最近一步 > 全局规则（还没录任何动作时） */
  function addNote(text) {
    var t = String(text || '').replace(/\s+/g, ' ').trim();
    if (!t) { return 0; }
    var seq = S.noteTarget || S.actions.length;
    var hit = null;
    for (var i = 0; i < S.actions.length; i++) { if (S.actions[i].seq === seq) { hit = S.actions[i]; } }
    if (hit) {
      hit.note = hit.note ? (hit.note + '；' + t.slice(0, 200)) : t.slice(0, 200);
      hudLog('💬', '第' + seq + '步：' + t.slice(0, 30), seq);
      markLogNote(seq);
    } else {
      S.notes.push({ seq: S.actions.length, at: new Date().toTimeString().slice(0, 8), text: t.slice(0, 200), rule: true });
      hudLog('📌', '规则：' + t.slice(0, 34));
    }
    S.noteTarget = 0;
    hudRefresh();
    return 1;
  }
  window.__SOP_addNote = addNote;

  function markLogNote(seq) {
    if (!hud.root) { return; }
    var box = hud.root.getElementById('log');
    if (!box) { return; }
    var ln = box.querySelector('.ln[data-seq="' + seq + '"]');
    if (ln && ln.textContent.indexOf('💬') < 0) { ln.textContent += ' 💬'; }
  }

  function setHudStatus(txt, cls) {
    if (!hud.root) { return; }
    var el = hud.root.getElementById('st');
    if (!el) { return; }
    el.textContent = txt;
    el.className = 'st' + (cls ? ' ' + cls : '');
    var ttl = hud.root.getElementById('ttl');
    var dot = hud.root.getElementById('dot');
    var bar = hud.root.getElementById('bar');
    var prefix = cls === 'idle' ? '待机' : (cls === 'pause' ? '已暂停' : (cls === 'done' ? '已停止' : '录制中'));
    if (ttl) { ttl.textContent = '网页操作录制' + (S.linkName ? ' · ' + S.linkName : '') + '（' + prefix + '）'; }
    if (dot) {
      dot.className = 'dot' + (cls === 'idle' ? '' : ' rec');
      if (cls === 'pause') { dot.style.background = '#fa8c16'; }
      else if (cls === 'done') { dot.style.background = '#00a870'; }
      else if (cls === 'idle') { dot.style.background = '#a9aeb8'; }
      else { dot.style.background = '#f5222d'; }
    }
    if (bar) { bar.className = 'bar' + (cls === '' ? ' on' : ''); }
  }

  function hudLog(icon, text, seq) {
    if (!hud.root) { return; }
    var box = hud.root.getElementById('log');
    if (!box) { return; }
    if (hud.logN === 0) { box.innerHTML = ''; }
    var ln = document.createElement('div');
    ln.className = 'ln';
    if (seq) { ln.setAttribute('data-seq', String(seq)); }
    ln.textContent = '[' + new Date().toTimeString().slice(0, 8) + '] ' + icon + ' ' + text;
    box.appendChild(ln);
    hud.logN++;
    while (box.children.length > 60) { box.removeChild(box.firstChild); }
    box.scrollTop = box.scrollHeight;
    var cur = hud.root.getElementById('cur');
    if (cur) { cur.textContent = '刚记录：' + text; }
  }

  function hudRefresh(actTotal, netTotal) {
    if (!hud.root) { return; }
    var c = localCounts();
    var act = (actTotal != null) ? actTotal : S.actions.length;
    var net = (netTotal != null) ? netTotal : (hud.net || 0);
    var noted = 0;
    for (var i = 0; i < S.actions.length; i++) { if (S.actions[i].note) { noted++; } }
    var cnt = hud.root.getElementById('cnt');
    if (cnt) {
      cnt.textContent = '动作 ' + act + ' · 点击 ' + c.click + ' · 填充 ' + c.fill
        + ' · 粘贴 ' + c.paste + ' · 下载 ' + c.download + ' · 请求 ' + net
        + ' · 备注 ' + (noted + S.notes.length);
    }
  }

  function localCounts() {
    var c = { click: 0, fill: 0, paste: 0, download: 0 };
    for (var i = 0; i < S.actions.length; i++) {
      var t = S.actions[i].type;
      if (c[t] != null) { c[t]++; }
    }
    return c;
  }

  /* 驱动侧（record.mjs）每轮推：{actions, net, name, status} */
  window.__SOP_hudSet = function (o) {
    o = o || {};
    if (o.name) { S.linkName = o.name; buildHud(o.name); }
    if (!hud.root) { return 'no-hud'; }
    if (o.net != null) { hud.net = o.net; }
    hudRefresh(o.actions, hud.net);
    if (S.stopReq) { return 'ok'; }
    if (!S.armed) { setHudStatus('待机：点下面「开始录制」我才开始记', 'idle'); return 'ok'; }
    if (o.status === 'paused') { setHudStatus('已暂停（操作不会被记录）', 'pause'); }
    else if (S.on) { setHudStatus('正在录制…', ''); }
    return 'ok';
  };

  /* 驱动侧查：用户是不是点了停止 / 有没有真的开始录 */
  window.__SOP_hudState = function () {
    return JSON.stringify({
      stop: !!S.stopReq, on: !!S.on, paused: !!S.pausedByUser,
      armed: !!S.armed, actions: S.actions.length, notes: S.notes.length, noteTarget: S.noteTarget || 0
    });
  };

  /* 撤销上一步：录制中误点自救（只删最近一条，备注跟着删） */
  window.__SOP_undo = function () {
    if (!S.actions.length) { hudLog('↩', '没有可撤销的动作'); return 0; }
    var a = S.actions.pop();
    if (hud.root) {
      var box = hud.root.getElementById('log');
      var ln = box && box.querySelector('.ln[data-seq="' + a.seq + '"]');
      if (ln) { ln.remove(); }
    }
    S.noteTarget = 0;
    hudLog('↩', '撤销第' + a.seq + '步：' + String(a.text || a.label || a.type).slice(0, 30));
    hudRefresh();
    return a.seq;
  };

  /* 就地剔除误点（驱动/agent 用）：删掉指定 seq，剩下的重排序号 */
  window.__SOP_drop = function (seqs) {
    var list = (seqs || []).map(Number).filter(function (n) { return n > 0; });
    if (!list.length || !S.actions.length) { return 0; }
    var before = S.actions.length;
    S.actions = S.actions.filter(function (a) { return list.indexOf(a.seq) === -1; });
    var gone = before - S.actions.length;
    if (!gone) { return 0; }
    if (hud.root) {
      var box2 = hud.root.getElementById('log');
      if (box2) {
        var lines = box2.querySelectorAll('.ln[data-seq]');
        for (var i = 0; i < lines.length; i++) {
          if (list.indexOf(Number(lines[i].getAttribute('data-seq'))) >= 0) { lines[i].remove(); }
        }
      }
    }
    S.actions.forEach(function (a, i) { a.seq = i + 1; });
    S.noteTarget = 0;
    hudLog('🗑', '剔除了 ' + gone + ' 步误点，还剩 ' + S.actions.length + ' 步');
    hudRefresh();
    return gone;
  };

  /* ---------- 对外接口 ---------- */
  window.__SOP_start = function () {
    S.actions = [];
    S.notes = [];
    S.on = true;
    S.armed = true;
    S.pausedByUser = false;
    S.noteTarget = 0;
    S.stopReq = false;
    S.t0 = Date.now();
    S.lastUrl = location.href;
    bind(true);
    buildHud(S.linkName || '');
    setHudStatus('正在录制…', '');
    if (hud.root) {
      var b = hud.root.getElementById('bstop');
      if (b) { b.textContent = '停止录制'; b.className = 'big stop'; b.disabled = false; }
      var t = hud.root.getElementById('btoggle');
      if (t) { t.textContent = '暂停'; t.disabled = false; }
      var u = hud.root.getElementById('bundo');
      if (u) { u.disabled = false; }
      hudLog('▶', '开始录制：现在起你的操作都会被记下来');
    }
    return 'recording';
  };

  /* 换页/新标签重新注入后由驱动调用：接着录，不清空已有动作（新页本来就是空） */
  window.__SOP_arm = function (v) {
    if (v && !S.armed) { return window.__SOP_start(); }
    return S.armed ? 'recording' : 'idle';
  };

  window.__SOP_stop = function () {
    S.on = false;
    bind(false);
    return S.actions.length;
  };

  window.__SOP_dump = function () {
    return JSON.stringify({
      url: location.href,
      title: document.title,
      injectedAt: new Date(S.t0).toISOString(),
      version: 3,
      count: S.actions.length,
      notes: S.notes,
      actions: S.actions
    }, null, 1);
  };

  /* 单点取证：对指定选择器取 6 级定位（不开录制也能用） */
  window.__SOP_pick = function (selector) {
    var el = document.querySelector(selector);
    if (!el) { return null; }
    return JSON.stringify({
      locator: collectLocators(el),
      label: fieldLabel(el),
      section: sectionOf(el),
      popup: popupOf(el),
      text: visibleText(el)
    }, null, 1);
  };

  /* 手册健康检查：传入 SOP 里的 best 列表，逐个判断当前页面还认不认
   * 返回 [{sel, ok, count, text}]，ok=false 即"网页改版了"。 */
  function resolve(sel) {
    if (!sel) { return []; }
    var m;
    if ((m = sel.match(/^getByRole\('([^']+)',\s*\{\s*name:\s*'([^']*)'/))) {
      var role = m[1], name = m[2];
      var map = { button: 'button,input[type=button],input[type=submit]', link: 'a', textbox: 'input,textarea', combobox: 'select', checkbox: 'input[type=checkbox]', radio: 'input[type=radio]' };
      var pool = document.querySelectorAll(map[role] || '*');
      var hits = [];
      for (var i = 0; i < pool.length; i++) {
        var t = (pool[i].getAttribute('aria-label') || visibleText(pool[i]) || '');
        if (t.indexOf(name) === 0 || t === name) { hits.push(pool[i]); }
      }
      return hits;
    }
    if ((m = sel.match(/^getByText\('([^']*)'/))) {
      var kw = m[1], all = document.querySelectorAll('body *'), out = [];
      for (var j = 0; j < all.length; j++) {
        if (all[j].children.length === 0 && visibleText(all[j]).indexOf(kw) >= 0) { out.push(all[j]); }
      }
      return out;
    }
    try { return Array.prototype.slice.call(document.querySelectorAll(sel.replace(/ \[non-unique:\d+\]/, ''))); }
    catch (e) { return []; }
  }

  window.__SOP_probe = function (list) {
    var res = [];
    for (var i = 0; i < list.length; i++) {
      var sel = list[i];
      var els = resolve(sel);
      res.push({ sel: sel, ok: els.length > 0, count: els.length, text: els.length ? visibleText(els[0]) : '' });
    }
    return JSON.stringify(res);
  };

  /* 注入即显示面板（待机态）：用户看到「开始录制」才知道要点它 */
  try {
    buildHud(S.linkName || '');
    setHudStatus('待机：点下面「开始录制」我才开始记', 'idle');
  } catch (e) { /* 页面不让挂浮标就静默，不影响录制主链 */ }

  return 'ready';
})();
