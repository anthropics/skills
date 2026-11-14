/* lib-farm.mjs — 定位库 → 浏览器农场挂机脚本 翻译器（纯函数，不发请求不碰盘）
 *
 * 为什么有这一层：
 *   UI 版子包能自己跑，但「自动反复跑」要有人调度。浏览器农场（browser-farm）正好是
 *   常驻运行时：每账号一个登录档，loop/watch 引擎挂总管后台跑。
 *   这里把 定位库.csv 一步步翻译成农场的 steps（多级定位 locs 直译过去，farm 执行器
 *   v0.1.22 起认 locs 并能逐级自愈），生成的 农场脚本.json 交 POST /script/new 即用。
 *
 * 口径（不许含糊）：
 *   1) 只翻译纯点击链路（动作 ∈ click/download；nav 是页面上下文不生成步）。
 *      链路里有 fill/paste 等要输入值的动作 → 整份不出：farm 循环只会点，出半截脚本会点错。
 *   2) 定位翻译规则固定：#id 与 [属性] 原样；L4 文本 → text=；L5/L6 css → path=；
 *      L3 role[name=…] 解出 name → text=（farm 没有 role 引擎，按文字找最接近）。
 *      forge 的 best定位 若是 L3/文本形态无法直译，靠各级定位列兜住，不猜。
 *   3) 每步带 href（=定位库「页面」列）：farm 跑时页面没开自动开回来。
 */

/* 单条定位翻译：认得出就翻成 farm 的四种格式（#id / [属性] / text= / path=），认不出返回 '' */
export function translateLocator(v) {
  const s = String(v || '').trim().replace(/ \[non-unique:\d+\]$/, '');
  if (!s) return '';
  if (s.startsWith('#')) return s;                    // L1_id
  if (s.startsWith('[')) return s;                    // L2_testid 等属性选择器
  const role = s.match(/^([a-z]+)\[name="(.+)"\]$/i); // L3_role：button[name="导出"] → 按文字找
  if (role) return 'text=' + role[2];
  return 'path=' + s;                                 // L5_css / L6_nth_path：querySelector 直查
}

/* 一个定位库步 → 一个 farm 步；翻不出任何可用定位返回 null（整份放弃的理由之一） */
export function stepToFarm(row) {
  const act = String(row['动作'] || '').trim().toLowerCase();
  if (act === 'nav') return { skip: true };           // 页面上下文，不是动作；href 已挂在别的步上
  if (!['click', 'download', ''].includes(act)) return { skip: true, blocking: true }; // fill/paste…：farm 点不了
  const out = [];
  const push = sel => { const v = String(sel || '').trim(); if (v && !out.includes(v)) out.push(v); };
  // 只翻无歧义的列：L4 文本按定义是文字；L5/L6 按定义是选择器。
  // best定位 三形态：#id/[属性] 直译；带结构字符的当 css 走 path=（误判也只是安全 miss，不会乱点）；
  // 纯文字当 text=。录制真包里 L1-L6 列总会覆盖 best，这里兜的是手写定位库只填 best 的情况。
  const best = String(row['best定位'] || '').trim().replace(/ \[non-unique:\d+\]$/, '');
  if (best) {
    if (best.startsWith('#') || best.startsWith('[')) push(best);
    else if (/[.[\]:>@~=+]/.test(best)) push('path=' + best);
    else push('text=' + best.slice(0, 30));
  }
  const t1 = String(row['L1_id'] || '').trim(); if (t1) push(t1);
  const t2 = translateLocator(row['L2_testid']); if (t2) push(t2);
  const t4 = String(row['L4_text'] || '').trim(); if (t4) push('text=' + t4.slice(0, 30));
  const t3 = translateLocator(row['L3_role']); if (t3 && t3.startsWith('text=')) push(t3); // role → 按文字找
  const t5 = translateLocator(row['L5_css']); if (t5) push(t5);
  const t6 = translateLocator(row['L6_nth_path']); if (t6) push(t6);
  if (!out.length) return { skip: true, blocking: true };
  return {
    skip: false,
    step: {
      selector: out[0],
      locs: out.slice(0, 6),
      text: String(row['标签'] || row['L4_text'] || '').replace(/\s+/g, ' ').trim().slice(0, 30),
      href: String(row['页面'] || '').trim() || undefined,
    },
  };
}

/* 定位库行数组 → 农场脚本对象；翻不了（有 blocking 步/一步都没翻出来）返回 { ok:false, why } */
export function toFarmScript(rows, { name, triggerNote } = {}) {
  if (!Array.isArray(rows) || !rows.length) return { ok: false, why: '定位库是空的' };
  const steps = [];
  const blockers = [];
  for (const row of rows) {
    const r = stepToFarm(row);
    if (r.skip && r.blocking) blockers.push(String(row['步骤'] || '?') + '（' + String(row['动作'] || '') + '）');
    else if (!r.skip) steps.push(r.step);
  }
  if (blockers.length) {
    return { ok: false, why: `第 ${blockers.join('、')} 步要填值/粘贴，农场循环只会点，出半截脚本会点错——这链路用子包跑（run.mjs），别上农场` };
  }
  if (!steps.length) return { ok: false, why: '没有任何可翻译的点击步' };
  const sc = {
    name: String(name || 'forge链路'),
    loop: 0, delayMs: 1500, jitterMs: 800,
    desc: 'skill-forge 生成：' + String(name || ''),
    steps,
  };
  if (triggerNote) sc._触发说明 = String(triggerNote).slice(0, 120); // 触发.json 的说明带给人看，farm 不消费
  return { ok: true, script: sc };
}
