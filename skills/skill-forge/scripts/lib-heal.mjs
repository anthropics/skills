/* lib-heal.mjs — 失败自愈：定位失效时逐级降级重试，命中哪级就把新定位回写定位库
 *
 * 为什么要这个：
 *   网页小改版（按钮换 class、换个包裹层）时，原 best定位 找不到，过去只能整条重录。
 *   但录制时已经存了 6 级定位（L1_id → L6_nth_path），按顺序再试一遍，
 *   大概率能点到同一个元素 —— 点到了就把结果写回 定位库.csv，下次直接用新定位。
 *
 * 口径（不许含糊）：
 *   1) 只做「同一元素换定位」，不改动作顺序、不改值、不猜页面。
 *   2) 降级顺序固定 L1→L6（越靠前越稳），命中级别必须记进日志，方便事后看是哪级救的。
 *   3) 回写只改 best定位 一列；原值写进 自愈记录.csv，能一眼看出从什么换到什么。
 *   4) 全 6 级都找不到 = 真改版，不许硬猜，交给 manage.mjs fail 标 broken。
 *   5) 只有 --heal 才回写；不给就只报告不落盘（默认不动用户的库）。
 */

export const LEVEL_COLUMNS = ['L1_id', 'L2_testid', 'L3_role', 'L4_text', 'L5_css', 'L6_nth_path'];

/* 给一个定位库行，按「先原样、再按级降级」的顺序列出候选 */
export function levelCandidates(step) {
  const out = [];
  const seen = new Set();
  const push = (sel, level, index) => {
    const s = String(sel || '').trim();
    if (!s || seen.has(s)) return;
    seen.add(s);
    out.push({ sel: s.replace(/ \[non-unique:\d+\]$/, ''), level, index });
  };
  push(step['best定位'], 'best定位', 0);
  LEVEL_COLUMNS.forEach((c, i) => push(step[c], c, i + 1));
  return out;
}

/* 单次尝试的 JS：找到就顺手做动作，找不到返回 found:false（不抛错，方便逐级重试） */
export function attemptJs(sel, act, value) {
  return `(function(){
    var els = [];
    try { els = window.__ACT.find(${JSON.stringify(sel)}); } catch (e) { els = []; }
    if (!els || !els.length) return { found: false };
    try {
      var a = ${JSON.stringify(act)};
      if (a === 'fill') return { found: true, ok: window.__ACT.setVal(els[0], ${JSON.stringify(value ?? '')}) };
      if (a === 'paste' && window.__ACT.pasteInto) return { found: true, ok: window.__ACT.pasteInto(${JSON.stringify(sel)}, ${JSON.stringify(value ?? '')}) };
      return { found: true, ok: window.__ACT.clickStable(els[0]) };
    } catch (e) { return { found: true, ok: 'error:' + (e && e.message || e) }; }
  })()`;
}

/* 逐级找：试到第一个 found 为止（run 可以是 async）。返回命中的级别、试了几次、以及未命中的选择器 */
export async function firstHit(cands, run) {
  const misses = [];
  for (const c of cands) {
    const r = await run(c);
    if (r && r.found) return { hit: c, result: r, misses, tried: misses.length + 1 };
    misses.push(c.sel);
  }
  return { hit: null, result: null, misses, tried: misses.length };
}

/* 自愈记录行：一眼看出「哪一步、从什么换到什么、救它的那级是什么」 */
export function healRecord(link, step, hit, stamp) {
  return {
    时间: stamp,
    链路: link || '',
    步骤: String(step['步骤'] ?? ''),
    动作: String(step['动作'] ?? ''),
    原定位: String(step['best定位'] ?? ''),
    新定位: hit.sel,
    命中级别: hit.level,
    试了几级: String(hit.index + 1)
  };
}

export function healLogLine(rec) {
  return [rec.时间, rec.链路, '第' + rec.步骤 + '步', rec.动作, rec.命中级别, rec.新定位].join('\t');
}

/* ---------- 最小 CSV 读写（只服务定位库/自愈记录，不引第三方） ---------- */
export function parseCsv(text) {
  const lines = String(text).replace(/^\uFEFF/, '').split(/\r?\n/).filter(l => l.trim());
  if (!lines.length) return { header: [], rows: [] };
  const cut = (line) => {
    const out = [];
    let cur = '', inQ = false;
    for (let i = 0; i < line.length; i++) {
      const c = line[i];
      if (inQ) {
        if (c === '"' && line[i + 1] === '"') { cur += '"'; i++; }
        else if (c === '"') inQ = false;
        else cur += c;
      } else if (c === '"') inQ = true;
      else if (c === ',') { out.push(cur); cur = ''; }
      else cur += c;
    }
    out.push(cur);
    return out.map(s => s.trim());
  };
  const header = cut(lines[0]);
  const rows = lines.slice(1).map(l => {
    const c = cut(l);
    const r = {};
    header.forEach((h, i) => { r[h] = c[i] ?? ''; });
    return r;
  });
  return { header, rows };
}

const q = (v) => {
  const s = String(v ?? '');
  return /[",\r\n]/.test(s) ? '"' + s.replace(/"/g, '""') + '"' : s;
};
export const csvCell = q;

export function toCsv(header, rows) {
  return [header.join(',')].concat(rows.map(r => header.map(h => q(r[h])).join(','))).join('\r\n') + '\r\n';
}

/* 回写：只改命中那一步的 best定位，其余原样保留 */
export function applyHeal(csvText, step, newSel) {
  const { header, rows } = parseCsv(csvText);
  let changed = 0;
  for (const r of rows) {
    if (String(r['步骤']) === String(step['步骤'])) { r['best定位'] = newSel; changed++; }
  }
  return { text: toCsv(header, rows), changed };
}
