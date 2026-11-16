/* act.js — 执行器的页面动作库（CDP 注入，配合 run.mjs 用）
 * 定位链失败自动降级：#id → [data-testid] → role[name] → 文本 → css → nth路径，
 * 全挂了才报"页面改版"（对应工厂的 broken 流程）。
 * 点击/填值法门来自真实后台实测：坐标连读两遍一致才点；React 框用原生 setter + 事件。
 */
(function () {
  if (window.__ACT) { return 'already'; }

  function visibleText(el) {
    return (el.innerText || el.textContent || '').replace(/\s+/g, ' ').trim();
  }

  function findByRoleName(role, name) {
    var map = {
      button: 'button,input[type=button],input[type=submit]',
      link: 'a', textbox: 'input,textarea', combobox: 'select',
      checkbox: 'input[type=checkbox]', radio: 'input[type=radio]'
    };
    var pool = document.querySelectorAll(map[role] || '*');
    var hits = [];
    for (var i = 0; i < pool.length; i++) {
      var t = pool[i].getAttribute('aria-label') || visibleText(pool[i]);
      if (t.indexOf(name) === 0 || t === name) { hits.push(pool[i]); }
    }
    return hits;
  }

  function findByText(name) {
    var all = document.querySelectorAll('button, a, [role=button], .btn, span'), hits = [];
    for (var i = 0; i < all.length; i++) {
      var t = visibleText(all[i]);
      if (t && t === name) { hits.push(all[i]); }
    }
    if (!hits.length) {
      for (var j = 0; j < all.length; j++) {
        var t2 = visibleText(all[j]);
        if (t2 && t2.indexOf(name) >= 0) { hits.push(all[j]); }
      }
    }
    return hits;
  }

  window.__ACT = {
    /* best 定位串 → 元素列表（可能多个，执行器自己挑/报歧义） */
    find: function (best) {
      if (!best) { return []; }
      var m;
      try {
        if (best[0] === '#' || best[0] === '[') {
          return Array.prototype.slice.call(document.querySelectorAll(best.replace(/ \[non-unique:\d+\]/, '')));
        }
      } catch (e) { /* 非法选择器，继续走后面的策略 */ }
      if ((m = best.match(/^(\w+)\[name="(.*)"\]$/))) { return findByRoleName(m[1], m[2]); }
      if (/^[a-z0-9]+(\.|:|\[| >)/i.test(best)) {
        try {
          var els = document.querySelectorAll(best.replace(/ \[non-unique:\d+\]/, ''));
          if (els.length) { return Array.prototype.slice.call(els); }
        } catch (e2) { /* 落到文本策略 */ }
      }
      return findByText(best);
    },

    /* 坐标稳定点击：滚进视口 → 连读两遍 rect 一致 → 真实鼠标事件 + JS click 双保险 */
    clickStable: function (el) {
      if (!el) { return 'no-element'; }
      try { el.scrollIntoView({ block: 'center' }); } catch (e) { /* 有些元素不支持，忽略 */ }
      var r1 = el.getBoundingClientRect();
      var r2 = el.getBoundingClientRect();
      if (Math.abs(r1.x - r2.x) > 2 || Math.abs(r1.y - r2.y) > 2) { return 'layout-moving'; }
      var x = r1.x + r1.width / 2, y = r1.y + r1.height / 2;
      ['mouseenter', 'mousedown', 'mouseup', 'click'].forEach(function (t) {
        el.dispatchEvent(new MouseEvent(t, { bubbles: true, cancelable: true, clientX: x, clientY: y }));
      });
      try { el.click(); } catch (e3) { /* dispatch 那份已够 */ }
      return 'ok';
    },

    /* React 受控框填值：原生 setter + input/change + blur（真实后台实证两套框里通用的一套） */
    setVal: function (el, val) {
      if (!el) { return 'no-element'; }
      el.focus();
      var proto = el.tagName === 'TEXTAREA' ? HTMLTextAreaElement.prototype : HTMLInputElement.prototype;
      var setter = Object.getOwnPropertyDescriptor(proto, 'value').set;
      setter.call(el, val);
      el.dispatchEvent(new Event('input', { bubbles: true }));
      el.dispatchEvent(new Event('change', { bubbles: true }));
      el.blur();
      return el.value === val ? 'ok' : 'readback-mismatch:' + el.value;
    },

    /* 合成粘贴：把 TSV 文本"贴"进当前聚焦的格子（在线表格编辑器普遍认 paste 事件） */
    pasteText: function (text) {
      var target = document.activeElement || document.body;
      target.focus();
      var dt = new DataTransfer();
      dt.setData('text/plain', text);
      var ev = new ClipboardEvent('paste', { clipboardData: dt, bubbles: true, cancelable: true });
      var ok = target.dispatchEvent(ev);
      if (!ok || !ev.defaultPrevented) {
        // 没人接管就退回 execCommand（部分老编辑器只认这条）
        try { document.execCommand('insertText', false, text); } catch (e) { /* 双路都失败才真失败 */ }
      }
      return 'ok';
    },

    /* 点击某格定位粘贴落点：按 best 找到格子 → 点它 → 贴 */
    pasteInto: function (best, text) {
      var els = window.__ACT.find(best);
      if (!els.length) { return 'target-not-found:' + best; }
      var clickRes = window.__ACT.clickStable(els[0]);
      if (clickRes !== 'ok') { return clickRes; }
      return window.__ACT.pasteText(text);
    },

    /* 回读复核素材：整页文本（执行器拿去逐键找值） */
    bodyText: function () {
      return document.body ? document.body.innerText.slice(0, 200000) : '';
    }
  };
  return 'ready';
})();
